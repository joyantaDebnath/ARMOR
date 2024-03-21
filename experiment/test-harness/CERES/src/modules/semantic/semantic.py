import io
import os
from datetime import *
from hashlib import *
from subprocess import *

from modules.helper import *
from modules.parsers.combinator_based import parser_rsa_signature
from modules.parsers.dsl_based import parser_rsa_signature_dsl
from modules.x509_ds import *
from pysmt.logics import *
from pysmt.shortcuts import *
from pysmt.smtlib.script import *
from pysmt.solvers.solver import *

import random

home = os.path.expanduser('~')
extra_location = "{}/.ceres/extras".format(home)
errors = []

# default values
MAX_EXTENSIONS = 15
MAX_DISTPOINT = 8
MAX_POLICY = 8
MAX_CHAIN_LENGTH = 5
MAX_NAME_LENGTH = 8
MAX_NAME_RDNSET_LENGTH = 1
MAX_CA_STORE_SIZE = 150

chain_smtVariables = []
chain_rawcert_smts = []
only_smt_global = None


def call_smt_solver(lfsc, postfix):
    solverLoc = '{}/CVC4/cvc4'.format(extra_location)
    proofcheckerLoc = '{}/LFSC/lfscc'.format(extra_location)
    proofCheckerTheories = '{}/LFSC/sat.plf {}/LFSC/smt.plf {}/LFSC/th_int.plf {}/LFSC/th_real.plf {}/LFSC/th_lira.plf  {}/LFSC/th_base.plf {}/LFSC/th_arrays.plf {}/LFSC/th_bv.plf {}/LFSC/th_bv_bitblast.plf'.format(
        extra_location, extra_location, extra_location, extra_location, extra_location, extra_location, extra_location, extra_location,
        extra_location)
    proofIn = '{}/LFSC/proof_{}.plf'.format(extra_location, postfix)
    solverIn = '{}/CVC4/temp_{}.smt2'.format(extra_location, postfix)
    solverOut = '{}/CVC4/result_{}.txt'.format(extra_location, postfix)

    # generate result, unsat-core and proof using solver
    os.system('{} {} > {}'.format(solverLoc, solverIn, solverOut))

    # separate result
    try:
        assert os.path.exists(solverOut)
        res_file = open(solverOut, 'r')
        temp = res_file.readlines()
        res_file.close()
        assert len(temp) > 0
    except:
        errors.append("Couldn't parse output of SMT solver")

    result = temp[0].lower().rstrip()
    unsat_core = None
    proof_check_status = None
    if result != "sat":
        temp_unsat_core = []
        j = 0
        for j in range(1, len(temp)):
            if temp[j].rstrip() == "(":
                continue
            elif temp[j].rstrip() == ")":
                break
            else:
                temp_unsat_core.append(temp[j].lower().rstrip())
        unsat_core = ';'.join(temp_unsat_core)

        if lfsc:
            try:
                proof_file = open(proofIn, 'w')
                proof_file.write(''.join(temp[j + 1:]))
                proof_file.close()
                subprocess = Popen('{} {} {}'.format(proofcheckerLoc, proofCheckerTheories, proofIn), shell=True,
                                   stdout=PIPE)
                proof_res = subprocess.stdout.read()
                proof_check_status = proof_res.decode("utf-8").__contains__('Proof checked successfully')
            except:
                errors.append("LFSCC : Couldn't check proof succesfully")
    
    # clean up residual files
    if os.path.exists(proofIn):
        os.remove(proofIn)
    if os.path.exists(solverIn):
        os.remove(solverIn)
    if os.path.exists(solverOut):
        os.remove(solverOut)
    
    return errors, result, unsat_core, proof_check_status


def generate_smtlib_formulas(cert_list, dsl_parser, lfsc, purposes, ca_store, ca_store_sizes, only_smt, sym_chain_len):
    global only_smt_global
    global MAX_CHAIN_LENGTH

    assignment_formulas = []
    property_formulas = []
    assignment_asserts = []
    property_asserts = []
    only_smt_global = only_smt

    if only_smt_global and sym_chain_len >= 1:
        MAX_CHAIN_LENGTH = sym_chain_len

    # generate property formulas
    for k in range(0, MAX_CHAIN_LENGTH):
        dec_cert_symbols(k)
        # single cert
        p_formulas, p_asserts = create_property_formulas_single(k)
        property_formulas.extend(p_formulas)
        property_asserts.extend(p_asserts)

    # chain
    p_formulas, p_asserts = create_property_formulas_chain(purposes)
    property_formulas.extend(p_formulas)
    property_asserts.extend(p_asserts)

    if not only_smt_global:
        # generate assignment formulas
        for k in range(0, len(cert_list)):
            parsedCert = cert_list[k]
            a_formulas, a_asserts = create_assignment_formulas(parsedCert, k, len(cert_list))
            assignment_formulas.extend(a_formulas)
            assignment_asserts.extend(a_asserts)

    # generate trusted store cons
    a30, f30, a30_a, f30_a = gen_cons_ca_in_store(cert_list, ca_store, ca_store_sizes)
    assignment_formulas.extend(a30)
    assignment_asserts.extend(a30_a)
    property_formulas.extend(f30)
    property_asserts.extend(f30_a)

    # check RSA signature
    a31, f31, a31_a, f31_a = gen_cons_rsa_signature(cert_list, dsl_parser)
    assignment_formulas.extend(a31)
    assignment_asserts.extend(a31_a)
    property_formulas.extend(f31)
    property_asserts.extend(f31_a)

    all_formulas = assignment_formulas + property_formulas
    all_formulas_asserts = assignment_asserts + property_asserts

    # dump smt-lib to file
    smtlib_init = to_smtlib_init(And(all_formulas), 'QF_AUFBVLIA')
    start = '(set-option :produce-unsat-cores true)\n'
    end = '\n(check-sat)\n(get-unsat-core)\n'
    if lfsc:
        end = end + '(get-proof)'
        start = start + '(set-option :produce-proofs true)\n'
    smtlib_out = start + smtlib_init + "\n".join(all_formulas_asserts) + end

    postfix = random.random()

    f = open('{}/CVC4/temp_{}.smt2'.format(extra_location, postfix), 'w')
    f.write(smtlib_out)
    f.close()

    return errors, postfix


## declare smt symbols
def dec_cert_symbols(k):
    Self_signed = Symbol("Self_signed_{}".format(k), BVType(5))
    Index = Symbol("Index_{}".format(k), BVType(5))
    RawCert = Symbol("RawCert_{}".format(k), INT)
    Tbs_hash = Symbol("Tbs_hash_{}".format(k), INT)
    Sig_digest = Symbol("Sig_digest_{}".format(k), INT)
    Version = Symbol("Version_{}".format(k), INT)
    Serial = Symbol("Serial_{}".format(k), INT)
    Serial_size = Symbol("Serial_size{}".format(k), INT)
    Cert_sign_algo_id = Symbol("Cert_sign_algo_id_{}".format(k), INT)
    Cert_sign_algo_id_size = Symbol("Cert_sign_algo_id_size_{}".format(k), INT)
    Cert_sign_algo_param_type = Symbol("Cert_sign_algo_param_type_{}".format(k), INT)
    Cert_sign_algo_param = Symbol("Cert_sign_algo_param_{}".format(k), INT)
    Cert_sign_algo_param_size = Symbol("Cert_sign_algo_param_size_{}".format(k), INT)
    Tbs_sign_algo_id = Symbol("Tbs_sign_algo_id_{}".format(k), INT)
    Tbs_sign_algo_id_size = Symbol("Tbs_sign_algo_id_size_{}".format(k), INT)
    Tbs_sign_algo_param_type = Symbol("Tbs_sign_algo_param_type_{}".format(k), INT)
    Tbs_sign_algo_param = Symbol("Tbs_sign_algo_param_{}".format(k), INT)
    Tbs_sign_algo_param_size = Symbol("Cert_sign_algo_param_size_{}".format(k), INT)
    NotbeforeYr = Symbol("NotbeforeYr_{}".format(k), BVType(14))
    NotbeforeMon = Symbol("NotbeforeMon_{}".format(k), BVType(4))
    NotbeforeDay = Symbol("NotbeforeDay_{}".format(k), BVType(5))
    NotbeforeHr = Symbol("NotbeforeHr_{}".format(k), BVType(5))
    NotbeforeMin = Symbol("NotbeforeMin_{}".format(k), BVType(6))
    NotbeforeSec = Symbol("NotbeforeSec_{}".format(k), BVType(6))
    NotafterYr = Symbol("NotafterYr_{}".format(k), BVType(14))
    NotafterMon = Symbol("NotafterMon_{}".format(k), BVType(4))
    NotafterDay = Symbol("NotafterDay_{}".format(k), BVType(5))
    NotafterHr = Symbol("NotafterHr_{}".format(k), BVType(5))
    NotafterMin = Symbol("NotafterMin_{}".format(k), BVType(6))
    NotafterSec = Symbol("NotafterSec_{}".format(k), BVType(6))
    CurtimeYr = Symbol("CurtimeYr_{}".format(k), BVType(14))
    CurtimeMon = Symbol("CurtimeMon_{}".format(k), BVType(4))
    CurtimeDay = Symbol("CurtimeDay_{}".format(k), BVType(5))
    CurtimeHr = Symbol("CurtimeHr_{}".format(k), BVType(5))
    CurtimeMin = Symbol("CurtimeMin_{}".format(k), BVType(6))
    CurtimeSec = Symbol("CurtimeSec_{}".format(k), BVType(6))
    RSA_pk_present = Symbol("RSA_pk_present_{}".format(k), BOOL)
    Extensions_present = Symbol("Extensions_present_{}".format(k), BOOL)
    ExtensionsList = [Symbol("Extension{}_{}".format(i, k), INT) for i in range(0, MAX_EXTENSIONS)]
    ExtensionsCriticalsList = [Symbol("ExtensionCritical{}_{}".format(i, k), BOOL) for i in range(0, MAX_EXTENSIONS)]
    ExtensionsKnownList = [Symbol("ExtensionKnown{}_{}".format(i, k), BOOL) for i in range(0, MAX_EXTENSIONS)]
    Bc_present = Symbol("BC_present_{}".format(k), BOOL)
    CA_present = Symbol("CA_present_{}".format(k), BOOL)
    BC_pathlen = Symbol("BC_pathlen_{}".format(k), BVType(5))
    BC_pathlen_present = Symbol("BC_pathlen_present_{}".format(k), BOOL)
    Ku_present = Symbol("Ku_present_{}".format(k), BOOL)
    ExKUdigitalSignature = Symbol("ExKUdigitalSignature_{}".format(k), BOOL)
    ExKUnonRepudiation = Symbol("ExKUnonRepudiation_{}".format(k), BOOL)
    ExKUkeyEncipherment = Symbol("ExKUkeyEncipherment_{}".format(k), BOOL)
    ExKUdataEncipherment = Symbol("ExKUdataEncipherment_{}".format(k), BOOL)
    ExKUkeyAgreement = Symbol("ExKUkeyAgreement_{}".format(k), BOOL)
    ExKUkeyCertSign = Symbol("ExKUkeyCertSign_{}".format(k), BOOL)
    ExKUcRLSign = Symbol("ExKUcRLSign_{}".format(k), BOOL)
    ExKUencipherOnly = Symbol("ExKUencipherOnly_{}".format(k), BOOL)
    ExKUdecipherOnly = Symbol("ExKUdecipherOnly_{}".format(k), BOOL)
    Eku_present = Symbol("Eku_present_{}".format(k), BOOL)
    ExEKUserverauth = Symbol("ExEKUserverauth_{}".format(k), BOOL)
    ExEKUclientauth = Symbol("ExEKUclientauth_{}".format(k), BOOL)
    ExEKUcodesign = Symbol("ExEKUcodesign_{}".format(k), BOOL)
    ExEKUemailpro = Symbol("ExEKUemailpro_{}".format(k), BOOL)
    ExEKUtimestamp = Symbol("ExEKUtimestamp_{}".format(k), BOOL)
    ExEKUocspsign = Symbol("ExEKUocspsign_{}".format(k), BOOL)
    San_present = Symbol("San_present_{}".format(k), BOOL)
    SanSizenozero = Symbol("SanSizenozero_{}".format(k), BOOL)
    SanCritical = Symbol("SanCritical_{}".format(k), BOOL)
    Aki_keyid_present = Symbol("Aki_keyid_present_{}".format(k), BOOL)
    Ski_keyid_present = Symbol("Ski_keyid_present_{}".format(k), BOOL)
    Subjectuniid_present = Symbol("Subjectuniid_present_{}".format(k), BOOL)
    Issueruniid_present = Symbol("Issueruniid_present_{}".format(k), BOOL)
    Issuer = Symbol("Issuer_{}".format(k), ArrayType(INT, ArrayType(INT, ArrayType(INT, INT))))
    Issuer_length = Symbol("Issuer_length_{}".format(k), INT)
    Issuer_rdns_size = Symbol("Issuer_rdns_size_{}".format(k), ArrayType(INT, INT))
    Subject = Symbol("Subject_{}".format(k), ArrayType(INT, ArrayType(INT, ArrayType(INT, INT))))
    Subject_length = Symbol("Subject_length_{}".format(k), INT)
    Subject_rdns_size = Symbol("Subject_rdns_size_{}".format(k), ArrayType(INT, INT))
    Policy_present = Symbol("Policy_present_{}".format(k), BOOL)
    PolicyIdsList = [Symbol("PolicyId{}_{}".format(i, k), INT) for i in range(0, MAX_POLICY)]
    Crl_dist_present = Symbol("Crl_dist_present_{}".format(k), BOOL)
    DistpointnamesList = [Symbol("Distpointname{}_{}".format(i, k), BOOL) for i in range(0, MAX_DISTPOINT)]
    DistpointreasonsList = [Symbol("Distpointreason{}_{}".format(i, k), BOOL) for i in range(0, MAX_DISTPOINT)]
    DistpointcrlissuersList = [Symbol("Distpointcrlissuer{}_{}".format(i, k), BOOL) for i in range(0, MAX_DISTPOINT)]

    Certificate = Cert_smtVariables(Self_signed, Index, Tbs_hash, Sig_digest, Version, Serial, Serial_size,
                                    Cert_sign_algo_id, Cert_sign_algo_id_size,
                                    Cert_sign_algo_param_type, Cert_sign_algo_param, Cert_sign_algo_param_size,
                                    Tbs_sign_algo_id, Tbs_sign_algo_id_size,
                                    Tbs_sign_algo_param_type, Tbs_sign_algo_param, Tbs_sign_algo_param_size,
                                    NotbeforeYr, NotbeforeMon, NotbeforeDay, NotbeforeHr, NotbeforeMin, NotbeforeSec,
                                    NotafterYr, NotafterMon, NotafterDay, NotafterHr, NotafterMin, NotafterSec,
                                    CurtimeYr, CurtimeMon, CurtimeDay, CurtimeHr, CurtimeMin, CurtimeSec,
                                    RSA_pk_present,
                                    Extensions_present, ExtensionsList, ExtensionsCriticalsList, ExtensionsKnownList,
                                    Bc_present, CA_present, BC_pathlen, BC_pathlen_present,
                                    Ku_present, ExKUdigitalSignature, ExKUnonRepudiation, ExKUkeyEncipherment,
                                    ExKUdataEncipherment,
                                    ExKUkeyAgreement, ExKUkeyCertSign, ExKUcRLSign, ExKUencipherOnly, ExKUdecipherOnly,
                                    Eku_present, ExEKUserverauth, ExEKUclientauth, ExEKUcodesign, ExEKUemailpro,
                                    ExEKUtimestamp,
                                    ExEKUocspsign,
                                    San_present, SanSizenozero, SanCritical,
                                    Issueruniid_present, Subjectuniid_present,
                                    Issuer, Issuer_length, Issuer_rdns_size, Subject, Subject_length, Subject_rdns_size,
                                    Policy_present, PolicyIdsList, Crl_dist_present, DistpointnamesList,
                                    DistpointreasonsList,
                                    DistpointcrlissuersList,
                                    Aki_keyid_present, Ski_keyid_present)

    chain_smtVariables.append(Certificate)
    chain_rawcert_smts.append(RawCert)


def create_assignment_formulas(parsedCert, k, n):
    bc_present_flag = False
    ku_present_flag = False
    san_present_flag = False
    policy_present_flag = False
    crl_dist_present_flag = False
    eku_present_flag = False
    aki_present_flag = False
    ski_present_flag = False
    assignment_formulas = []
    assignment_asserts = []
    ck = chain_smtVariables[k]
    # assignment formulas from a certificate
    a0_0 = Ite(generate_name_check_constraints(ck, ck), Equals(ck.Self_signed, BV(1, 5)),
               Equals(ck.Self_signed, BV(0, 5)))
    assignment_formulas.append(a0_0)
    assignment_asserts.append(to_smtlib_assert(a0_0))

    a0 = chain_rawcert_smts[k].Equals(Int(parsedCert.RawCert))
    assignment_formulas.append(a0)
    assignment_asserts.append(to_smtlib_assert(a0))
    #
    Id = parsedCert.SignatureAlgorithm.Value.Id
    param = parsedCert.SignatureAlgorithm.Value.Parameter
    if param is None:
        param = [0, 0, 0]
    else:
        if param.Value is None:
            param = [param.Type, 0, 0]
        else:
            param = [param.Type, int(param.Value, 16), len(param.Value)]

    a1_1 = ck.Cert_sign_algo_id.Equals(Int(Id[0]))
    assignment_formulas.append(a1_1)
    assignment_asserts.append(to_smtlib_assert(a1_1))
    a1_2 = ck.Cert_sign_algo_id_size.Equals(Int(Id[1]))
    assignment_formulas.append(a1_2)
    assignment_asserts.append(to_smtlib_assert(a1_2))
    a1_3 = ck.Cert_sign_algo_param_type.Equals(Int(param[0]))
    assignment_formulas.append(a1_3)
    assignment_asserts.append(to_smtlib_assert(a1_3))
    a1_4 = ck.Cert_sign_algo_param.Equals(param[1])
    assignment_formulas.append(a1_4)
    assignment_asserts.append(to_smtlib_assert(a1_4))
    a1_5 = ck.Cert_sign_algo_param_size.Equals(param[2])
    assignment_formulas.append(a1_5)
    assignment_asserts.append(to_smtlib_assert(a1_5))

    Id = parsedCert.TbsCertificate.SignatureAlgorithm.Value.Id
    param = parsedCert.TbsCertificate.SignatureAlgorithm.Value.Parameter
    if param is None:
        param = [0, 0, 0]
    else:
        if param.Value is None:
            param = [param.Type, 0, 0]
        else:
            param = [param.Type, int(param.Value, 16), len(param.Value)]

    a1_6 = ck.Tbs_sign_algo_id.Equals(Int(Id[0]))
    assignment_formulas.append(a1_6)
    assignment_asserts.append(to_smtlib_assert(a1_6))
    a1_7 = ck.Tbs_sign_algo_id_size.Equals(Int(Id[1]))
    assignment_formulas.append(a1_7)
    assignment_asserts.append(to_smtlib_assert(a1_7))
    a1_8 = ck.Tbs_sign_algo_param_type.Equals(Int(param[0]))
    assignment_formulas.append(a1_8)
    assignment_asserts.append(to_smtlib_assert(a1_8))
    a1_9 = ck.Tbs_sign_algo_param.Equals(param[1])
    assignment_formulas.append(a1_9)
    assignment_asserts.append(to_smtlib_assert(a1_9))
    a1_10 = ck.Tbs_sign_algo_param_size.Equals(param[2])
    assignment_formulas.append(a1_10)
    assignment_asserts.append(to_smtlib_assert(a1_10))

    if str(type(parsedCert.TbsCertificate.SubjectPKI.PublicKey)) == "<class 'modules.x509_ds.RSAkey'>":
        a31 = ck.RSA_pk_present
        assignment_formulas.append(a31)
        assignment_asserts.append(to_smtlib_assert(a31))
    else:
        a31 = ck.RSA_pk_present.Iff(False)
        assignment_formulas.append(a31)
        assignment_asserts.append(to_smtlib_assert(a31))

    if parsedCert.TbsCertificate.Extensions is not None:
        a2_1 = ck.Extensions_present
        assignment_formulas.append(a2_1)
        assignment_asserts.append(to_smtlib_assert(a2_1))

        j = 0
        for ex in parsedCert.TbsCertificate.Extensions.List:
            a12 = Equals(ck.ExtensionsList[j], Int(ex.ExtnId[0]))
            a_ex_crit = ck.ExtensionsCriticalsList[j].Iff(Bool(ex.Critical))
            a_ex_knwn = ck.ExtensionsKnownList[j].Iff(
                Bool(str(type(ex.ExtnValue)) != "<class 'modules.x509_ds.Unknown_extension'>"))
            assignment_formulas.append(a12)
            assignment_asserts.append(to_smtlib_assert(a12))
            assignment_formulas.append(a_ex_crit)
            assignment_asserts.append(to_smtlib_assert(a_ex_crit))
            assignment_formulas.append(a_ex_knwn)
            assignment_asserts.append(to_smtlib_assert(a_ex_knwn))

            j = j + 1

            if ex.ExtnId[0] == 5578003:
                bc_present_flag = True
                a7_2 = ck.CA_present.Iff(Bool(ex.ExtnValue.CA))
                assignment_formulas.append(a7_2)
                assignment_asserts.append(to_smtlib_assert(a7_2))
                if ex.ExtnValue.PathLen is not None:
                    a17 = And(Equals(ck.BC_pathlen, BV(ex.ExtnValue.PathLen[0], 5)),
                              ck.BC_pathlen_present.Iff(True))
                    assignment_formulas.append(a17)
                    assignment_asserts.append(to_smtlib_assert(a17))
                else:
                    a17 = ck.BC_pathlen_present.Iff(False)
                    assignment_formulas.append(a17)
                    assignment_asserts.append(to_smtlib_assert(a17))
            elif ex.ExtnId[0] == 5577999:
                ku_present_flag = True
                kubits = ex.ExtnValue.Purposes
                a8_1 = ck.ExKUdigitalSignature.Iff(Bool("digitalSignature" in kubits))
                a8_2 = ck.ExKUnonRepudiation.Iff(Bool("nonRepudiation" in kubits))
                a8_3 = ck.ExKUkeyEncipherment.Iff(Bool("keyEncipherment" in kubits))
                a8_4 = ck.ExKUdataEncipherment.Iff(Bool("dataEncipherment" in kubits))
                a8_5 = ck.ExKUkeyAgreement.Iff(Bool("keyAgreement" in kubits))
                a8_6 = ck.ExKUkeyCertSign.Iff(Bool("keyCertSign" in kubits))
                a8_7 = ck.ExKUcRLSign.Iff(Bool("cRLSign" in kubits))
                a8_8 = ck.ExKUencipherOnly.Iff(Bool("encipherOnly" in kubits))
                a8_9 = ck.ExKUdecipherOnly.Iff(Bool("decipherOnly" in kubits))
                assignment_formulas.append(a8_1)
                assignment_asserts.append(to_smtlib_assert(a8_1))
                assignment_formulas.append(a8_2)
                assignment_asserts.append(to_smtlib_assert(a8_2))
                assignment_formulas.append(a8_3)
                assignment_asserts.append(to_smtlib_assert(a8_3))
                assignment_formulas.append(a8_4)
                assignment_asserts.append(to_smtlib_assert(a8_4))
                assignment_formulas.append(a8_5)
                assignment_asserts.append(to_smtlib_assert(a8_5))
                assignment_formulas.append(a8_6)
                assignment_asserts.append(to_smtlib_assert(a8_6))
                assignment_formulas.append(a8_7)
                assignment_asserts.append(to_smtlib_assert(a8_7))
                assignment_formulas.append(a8_8)
                assignment_asserts.append(to_smtlib_assert(a8_8))
                assignment_formulas.append(a8_9)
                assignment_asserts.append(to_smtlib_assert(a8_9))
            elif ex.ExtnId[0] == 5578021:
                eku_present_flag = True
                ekus = ex.ExtnValue.Purposes
                a88_1 = ck.ExEKUserverauth.Iff(Bool("serverAuth" in ekus))
                a88_2 = ck.ExEKUclientauth.Iff(Bool("clientAuth" in ekus))
                a88_3 = ck.ExEKUcodesign.Iff(Bool("codeSigning" in ekus))
                a88_4 = ck.ExEKUemailpro.Iff(Bool("emailProtection" in ekus))
                a88_5 = ck.ExEKUtimestamp.Iff(Bool("timeStamping" in ekus))
                a88_6 = ck.ExEKUocspsign.Iff(Bool("OCSPSigning" in ekus))
                assignment_formulas.append(a88_1)
                assignment_asserts.append(to_smtlib_assert(a88_1))
                assignment_formulas.append(a88_2)
                assignment_asserts.append(to_smtlib_assert(a88_2))
                assignment_formulas.append(a88_3)
                assignment_asserts.append(to_smtlib_assert(a88_3))
                assignment_formulas.append(a88_4)
                assignment_asserts.append(to_smtlib_assert(a88_4))
                assignment_formulas.append(a88_5)
                assignment_asserts.append(to_smtlib_assert(a88_5))
                assignment_formulas.append(a88_6)
                assignment_asserts.append(to_smtlib_assert(a88_6))
            elif ex.ExtnId[0] == 5578001:
                san_present_flag = True
                a9_1 = ck.SanCritical.Iff(Bool(ex.Critical))
                assignment_formulas.append(a9_1)
                assignment_asserts.append(to_smtlib_assert(a9_1))
                a9_2 = ck.SanSizenozero.Iff(Bool(len(ex.ExtnValue.Value) > 0))
                assignment_formulas.append(a9_2)
                assignment_asserts.append(to_smtlib_assert(a9_2))
            elif ex.ExtnId[0] == 5578016:
                policy_present_flag = True
                i = 0
                for policy in ex.ExtnValue.Value:
                    a15 = Equals(ck.PolicyIdsList[i], Int(policy.PolicyIdentifier[0]))
                    assignment_formulas.append(a15)
                    assignment_asserts.append(to_smtlib_assert(a15))
                    i = i + 1
            elif ex.ExtnId[0] == 5578019:
                if ex.ExtnValue.KeyId is not None:
                    aki_present_flag = True
            elif ex.ExtnId[0] == 5577998:
                if ex.ExtnValue.KeyId is not None:
                    ski_present_flag = True
            elif ex.ExtnId[0] == 5578015:
                crl_dist_present_flag = True
                i = 0
                for distpoint in ex.ExtnValue.Value:
                    a18_1 = ck.DistpointnamesList[i].Iff(
                        Bool(distpoint.DistributionPoint is not None))
                    a18_2 = ck.DistpointreasonsList[i].Iff(Bool(distpoint.Reasons is not None))
                    a18_3 = ck.DistpointcrlissuersList[i].Iff(Bool(distpoint.CRLIssuer is not None))
                    assignment_formulas.append(a18_1)
                    assignment_asserts.append(to_smtlib_assert(a18_1))
                    assignment_formulas.append(a18_2)
                    assignment_asserts.append(to_smtlib_assert(a18_2))
                    assignment_formulas.append(a18_3)
                    assignment_asserts.append(to_smtlib_assert(a18_3))
                    i = i + 1
    else:
        a2_1 = ck.Extensions_present.Iff(False)
        assignment_formulas.append(a2_1)
        assignment_asserts.append(to_smtlib_assert(a2_1))

    e1 = ck.Bc_present.Iff(bc_present_flag)
    assignment_formulas.append(e1)
    assignment_asserts.append(to_smtlib_assert(e1))
    e2 = ck.Ku_present.Iff(ku_present_flag)
    assignment_formulas.append(e2)
    assignment_asserts.append(to_smtlib_assert(e2))
    e3 = ck.San_present.Iff(san_present_flag)
    assignment_formulas.append(e3)
    assignment_asserts.append(to_smtlib_assert(e3))
    e4 = ck.Policy_present.Iff(policy_present_flag)
    assignment_formulas.append(e4)
    assignment_asserts.append(to_smtlib_assert(e4))
    e5 = ck.Crl_dist_present.Iff(crl_dist_present_flag)
    assignment_formulas.append(e5)
    assignment_asserts.append(to_smtlib_assert(e5))
    e6 = ck.Eku_present.Iff(eku_present_flag)
    assignment_formulas.append(e6)
    assignment_asserts.append(to_smtlib_assert(e6))
    e7 = ck.Aki_keyid_present.Iff(aki_present_flag)
    assignment_formulas.append(e7)
    assignment_asserts.append(to_smtlib_assert(e7))
    e8 = ck.Ski_keyid_present.Iff(ski_present_flag)
    assignment_formulas.append(e8)
    assignment_asserts.append(to_smtlib_assert(e8))

    a2_2 = ck.Version.Equals(Int(parsedCert.TbsCertificate.Version[0]))
    assignment_formulas.append(a2_2)
    assignment_asserts.append(to_smtlib_assert(a2_2))

    a4_1 = ck.Serial_size.Equals(Int(parsedCert.TbsCertificate.Serial[1]))
    a4_2 = ck.Serial.Equals(Int(parsedCert.TbsCertificate.Serial[0]))
    a4 = And(a4_1, a4_2)
    assignment_formulas.append(a4)
    assignment_asserts.append(to_smtlib_assert(a4))

    a10_1 = ck.Issueruniid_present.Iff(Bool(parsedCert.TbsCertificate.IssuerUID is not None))
    assignment_formulas.append(a10_1)
    assignment_asserts.append(to_smtlib_assert(a10_1))

    a10_2 = ck.Subjectuniid_present.Iff(Bool(parsedCert.TbsCertificate.SubjectUID is not None))
    assignment_formulas.append(a10_2)
    assignment_asserts.append(to_smtlib_assert(a10_2))

    p = -1
    Issuer = Symbol("Issuer_{}".format(k), ArrayType(INT, ArrayType(INT, ArrayType(INT, INT))))
    Issuer_rdns_size = Symbol("Issuer_rdns_size_{}".format(k), ArrayType(INT, INT))
    for rdnset in parsedCert.TbsCertificate.Issuer.List:
        p = p + 1
        q = -1
        IssuerRDN = Symbol("IssuerRDN_{}_{}".format(k, p), ArrayType(INT, ArrayType(INT, INT)))
        if rdnset != None:
            for attbt in rdnset.List:
                q = q + 1
                oid = attbt.Id[0]
                valtype = attbt.Value.Type
                value = call_stringprep(attbt.Value.Value, valtype)
                if value is None:
                    errors.append(
                        "Issuer : LDAP string perparation error in certificate {} set {} attribute {}".format(k, p, q))
                    return [], []

                IssuerRDNNA = Symbol("IssuerRDNNA_{}_{}_{}".format(k, p, q), ArrayType(INT, INT))
                IssuerRDNNA = Store(IssuerRDNNA, Int(0), Int(oid))
                IssuerRDNNA = Store(IssuerRDNNA, Int(1), Int(valtype))
                IssuerRDNNA = Store(IssuerRDNNA, Int(2), Int(value))
                IssuerRDN = Store(IssuerRDN, Int(q), IssuerRDNNA)
            Issuer = Store(Issuer, Int(p), IssuerRDN)
            Issuer_rdns_size = Store(Issuer_rdns_size, Int(p), Int(q + 1))
    a_iss1 = ck.Issuer.Equals(Issuer)
    a_iss2 = ck.Issuer_rdns_size.Equals(Issuer_rdns_size)
    a_iss3 = ck.Issuer_length.Equals(Int(p + 1))
    a_iss = And(a_iss1, a_iss2, a_iss3)

    assignment_formulas.append(a_iss)
    assignment_asserts.append(to_smtlib_assert(a_iss))

    p = -1
    Subject = Symbol("Subject_{}".format(k), ArrayType(INT, ArrayType(INT, ArrayType(INT, INT))))
    Subject_rdns_size = Symbol("Subject_rdns_size_{}".format(k), ArrayType(INT, INT))
    for rdnset in parsedCert.TbsCertificate.Subject.List:
        p = p + 1
        q = -1
        SubjectRDN = Symbol("SubjectRDN_{}_{}".format(k, p), ArrayType(INT, ArrayType(INT, INT)))
        if rdnset != None:
            for attbt in rdnset.List:
                q = q + 1
                oid = attbt.Id[0]
                valtype = attbt.Value.Type
                value = call_stringprep(attbt.Value.Value, valtype)
                if value is None:
                    errors.append(
                        "Subject : LDAP string perparation error in certificate {} set {} attribute {}".format(k, p, q))
                    return [], []

                SubjectRDNNA = Symbol("SubjectRDNNA_{}_{}_{}".format(k, p, q), ArrayType(INT, INT))
                SubjectRDNNA = Store(SubjectRDNNA, Int(0), Int(oid))
                SubjectRDNNA = Store(SubjectRDNNA, Int(1), Int(valtype))
                SubjectRDNNA = Store(SubjectRDNNA, Int(2), Int(value))
                SubjectRDN = Store(SubjectRDN, Int(q), SubjectRDNNA)
            Subject = Store(Subject, Int(p), SubjectRDN)
            Subject_rdns_size = Store(Subject_rdns_size, Int(p), Int(q + 1))
    a_sub1 = ck.Subject.Equals(Subject)
    a_sub2 = ck.Subject_rdns_size.Equals(Subject_rdns_size)
    a_sub3 = ck.Subject_length.Equals(Int(p + 1))
    a_sub = And(a_sub1, a_sub2, a_sub3)

    assignment_formulas.append(a_sub)
    assignment_asserts.append(to_smtlib_assert(a_sub))

    NByr, NBmon, NBday, NBhr, NBmin, NBsec = Timedecoder(parsedCert.TbsCertificate.Validity.NotBefore)
    NAyr, NAmon, NAday, NAhr, NAmin, NAsec = Timedecoder(parsedCert.TbsCertificate.Validity.NotAfter)

    current_time = datetime.utcnow()
    Curyr, Curmon, Curday, Curhr, Curmin, Cursec = int(current_time.year), int(current_time.month), int(
        current_time.day), int(current_time.hour), int(current_time.minute), int(current_time.second)

    a21_1 = And(ck.NotbeforeYr.Equals(BV(NByr, 14)), ck.NotbeforeMon.Equals(BV(NBmon, 4)),
                ck.NotbeforeDay.Equals(BV(NBday, 5)), ck.NotbeforeHr.Equals(BV(NBhr, 5)),
                ck.NotbeforeMin.Equals(BV(NBmin, 6)), ck.NotbeforeSec.Equals(BV(NBsec, 6)))
    a21_2 = And(ck.NotafterYr.Equals(BV(NAyr, 14)), ck.NotafterMon.Equals(BV(NAmon, 4)),
                ck.NotafterDay.Equals(BV(NAday, 5)), ck.NotafterHr.Equals(BV(NAhr, 5)),
                ck.NotafterMin.Equals(BV(NAmin, 6)), ck.NotafterSec.Equals(BV(NAsec, 6)))
    a21_3 = And(ck.CurtimeYr.Equals(BV(Curyr, 14)), ck.CurtimeMon.Equals(BV(Curmon, 4)),
                ck.CurtimeDay.Equals(BV(Curday, 5)), ck.CurtimeHr.Equals(BV(Curhr, 5)),
                ck.CurtimeMin.Equals(BV(Curmin, 6)), ck.CurtimeSec.Equals(BV(Cursec, 6)))
    a21 = And(a21_1, a21_2, a21_3)
    assignment_formulas.append(a21)
    assignment_asserts.append(to_smtlib_assert(a21))

    return assignment_formulas, assignment_asserts


def create_property_formulas_single(k):
    property_formulas = []
    property_asserts = []
    ck = chain_smtVariables[k]

    ## assign Index
    f0 = ck.Index.Equals(BV(k, 5))
    property_formulas.append(f0)
    property_asserts.append(to_smtlib_assert(f0))

    # signatureAlgorithm field MUST contain the same algorithm identifier as the
    # signature field in the sequence tbsCertificate.
    f1_1 = ck.Cert_sign_algo_id.Equals(ck.Tbs_sign_algo_id)
    f1_2 = ck.Cert_sign_algo_id_size.Equals(ck.Tbs_sign_algo_id_size)
    f1_3 = ck.Cert_sign_algo_param_type.Equals(ck.Tbs_sign_algo_param_type)
    f1_4 = ck.Cert_sign_algo_param.Equals(ck.Tbs_sign_algo_param)
    f1_5 = ck.Cert_sign_algo_param_size.Equals(ck.Tbs_sign_algo_param_size)
    f1 = And(f1_1, f1_2, f1_3, f1_4, f1_5)
    property_formulas.append(f1)
    property_asserts.append(to_smtlib_named_assert(f1, 'signatureAlgorithm_mismatch_in_certificate_{}'.format(k)))
    #
    # Extension field MUST only appear if the Version is 3
    f2 = ck.Extensions_present.Implies(ck.Version.Equals(2))
    property_formulas.append(f2)
    property_asserts.append(to_smtlib_named_assert(f2, 'extension_appears_in_older_version_certificate_{}'.format(k)))

    # At a minimum, conforming implementations MUST recognize Version 3 certificates.
    # Generation of version 2 certificates is not expected by implementations based on this profile.
    f3 = Or(ck.Version.Equals(0), ck.Version.Equals(2))
    property_formulas.append(f3)
    property_asserts.append(to_smtlib_named_assert(f3, 'unsupported_version_in_certificate_{}'.format(k)))

    # The Serial number MUST be a positive integer assigned by the CA to
    # each certificate. Certificate users MUST be able to
    # handle SerialNumber values up to 20 octets. (we will consider 50 octet)
    f4_1 = And(GE(ck.Serial_size, Int(1)), LE(ck.Serial_size, Int(50)))
    f4_2 = GT(ck.Serial, Int(0))
    f4 = And(f4_1, f4_2)
    property_formulas.append(f4)
    property_asserts.append(to_smtlib_named_assert(f4, 'serial_not_in_range_in_certificate_{}'.format(k)))
    #
    # The issuer field MUST contain a non-empty distinguished name (DN).
    f5 = GT(ck.Issuer_length, Int(0))
    property_formulas.append(f5)
    property_asserts.append(to_smtlib_named_assert(f5, 'empty_issuer_rdn_in_certificate_{}'.format(k)))
    #
    # if the subject is a CA (e.g., the basic constraints extension, is present and the value of cA is
    # TRUE), then the subject field MUST be populated with a non-empty
    # distinguished name.
    f7 = And(ck.Bc_present, ck.CA_present).Implies(GT(ck.Subject_length, Int(0)))
    property_formulas.append(f7)
    property_asserts.append(to_smtlib_named_assert(f7, 'empty_subject_rdn_in_ca_certificate_{}'.format(k)))
    #
    # Unique Identifiers fields MUST only appear if the Version is 2 or 3.
    # These fields MUST NOT appear if the Version is 1.
    f10_1 = ck.Issueruniid_present.Implies(Or(ck.Version.Equals(1), ck.Version.Equals(2)))
    f10_2 = ck.Subjectuniid_present.Implies(Or(ck.Version.Equals(1), ck.Version.Equals(2)))
    f10_3 = ck.Version.Equals(0).Implies(ck.Issueruniid_present.Iff(False))
    f10_4 = ck.Version.Equals(0).Implies(ck.Subjectuniid_present.Iff(False))
    f10 = And(f10_1, f10_2, f10_3, f10_4)
    property_formulas.append(f10)
    property_asserts.append(to_smtlib_named_assert(f10, 'unique_identifier_in_version_1_certificate_{}'.format(k)))
    #
    # Where it appears, the pathLenConstraint field
    # MUST be greater than or equal to zero.
    f17 = And(ck.Bc_present, ck.BC_pathlen_present).Implies(BVUGE(ck.BC_pathlen, BV(0, 5)))
    property_formulas.append(f17)
    property_asserts.append(to_smtlib_named_assert(f17, 'pathLenConstraint_not_in_range_in_certificate_{}'.format(k)))
    #
    # If the subject is a CRL issuer (e.g., the key usage extension, is present
    # and the value of cRLSign is TRUE), then the subject field MUST be populated with a non-empty
    # distinguished name.
    f8 = And(ck.Ku_present, ck.ExKUcRLSign).Implies(GT(ck.Subject_length, Int(0)))
    property_formulas.append(f8)
    property_asserts.append(to_smtlib_named_assert(f8, 'empty_subject_rdn_in_crl_certificate_{}'.format(k)))
    #
    # When the keyUsage extension appears in a certificate, at least one of the bits MUST be set to 1.
    f14 = ck.Ku_present.Implies(Or(ck.ExKUdigitalSignature, ck.ExKUnonRepudiation, ck.ExKUkeyEncipherment,
                                   ck.ExKUdataEncipherment, ck.ExKUkeyAgreement, ck.ExKUkeyCertSign,
                                   ck.ExKUcRLSign, ck.ExKUencipherOnly, ck.ExKUdecipherOnly))
    property_formulas.append(f14)
    property_asserts.append(to_smtlib_named_assert(f14, 'no_key_usage_purpose_in_certificate_{}'.format(k)))
    #
    # If subject naming information is present only in the subjectAltName extension , then the subject
    # name MUST be an empty sequence and the subjectAltName extension MUST be critical.
    f9 = And(ck.San_present, ck.SanSizenozero, Equals(ck.Subject_length, Int(0))).Implies(ck.SanCritical)
    property_formulas.append(f9)
    property_asserts.append(to_smtlib_named_assert(f9, 'wrong_usage_of_subjectAltName_in_certificate_{}'.format(k)))
    #
    # If the subjectAltName extension is present, the sequence MUST contain at least one entry.
    f16 = ck.San_present.Implies(ck.SanSizenozero)
    property_formulas.append(f16)
    property_asserts.append(to_smtlib_named_assert(f16, 'subjectAltName_is_empty_in_certificate_{}'.format(k)))
    #
    # If the keyCertSign bit is asserted, then the cA bit in the basic
    # constraints extension MUST also be asserted.
    # If the cA boolean is not asserted, then the keyCertSign bit
    # in the key usage extension MUST NOT be asserted.
    f13 = And(ck.Ku_present, ck.Bc_present).Implies(Or(Not(ck.ExKUkeyCertSign), ck.CA_present))
    property_formulas.append(f13)
    property_asserts.append(to_smtlib_named_assert(f13, 'keycertsign_in_non_ca_certificate_{}'.format(k)))
    #
    # A certificate MUST NOT include more than one instance of a particular extension.
    f12 = ck.Extensions_present.Implies(AllDifferent(ck.ExtensionsList))
    property_formulas.append(f12)
    property_asserts.append(to_smtlib_named_assert(f12, 'repeated_extensions_in_certificate_{}'.format(k)))

    # A certificate-using system MUST reject the certificate if it encounters
    # a critical extension it does not recognize or a critical extension
    # that contains information that it cannot process.
    for p in range(0, MAX_EXTENSIONS):
        f12_crit_ext = And(ck.Extensions_present, ck.ExtensionsCriticalsList[p]).Implies(ck.ExtensionsKnownList[p])
        property_formulas.append(f12_crit_ext)
        property_asserts.append(
            to_smtlib_named_assert(f12_crit_ext,
                                   'unknown_critical_extension_{}_in_certificate_{}'.format(p, k)))
    #
    # A certificate policy OID MUST NOT appear more than once in a certificate policies extension.
    f15 = ck.Policy_present.Implies(AllDifferent(ck.PolicyIdsList))
    property_formulas.append(f15)
    property_asserts.append(to_smtlib_named_assert(f15, 'repeated_policies_in_certificate_{}'.format(k)))
    #
    # While each of these fields is optional, a DistributionPoint MUST NOT
    # consist of only the reasons field; either distributionPoint or
    # cRLIssuer MUST be present
    for i in range(0, MAX_DISTPOINT):
        f18 = And(ck.Crl_dist_present, ck.DistpointreasonsList[i]).Implies(
            Or(ck.DistpointnamesList[i], ck.DistpointcrlissuersList[i]))
        property_formulas.append(f18)
        property_asserts.append(to_smtlib_named_assert(f18,
                                                       'wrong_structure_1_of_CRL_distribution_point_{}_in_certificate_{}'.format(
                                                           i, k)))

    #
    # The certificate validity period includes the current time.
    f21_1 = generate_time_constraints(ck.NotbeforeYr, ck.NotbeforeMon, ck.NotbeforeDay,
                                      ck.NotbeforeHr, ck.NotbeforeMin, ck.NotbeforeSec,
                                      ck.CurtimeYr, ck.CurtimeMon, ck.CurtimeDay,
                                      ck.CurtimeHr, ck.CurtimeMin, ck.CurtimeSec)
    f21_2 = generate_time_constraints(ck.CurtimeYr, ck.CurtimeMon, ck.CurtimeDay,
                                      ck.CurtimeHr, ck.CurtimeMin, ck.CurtimeSec,
                                      ck.NotafterYr, ck.NotafterMon, ck.NotafterDay,
                                      ck.NotafterHr, ck.NotafterMin, ck.NotafterSec)
    f21 = And(f21_1, f21_2)
    property_formulas.append(f21)
    property_asserts.append(to_smtlib_named_assert(f21, 'expired_certificate_{}'.format(k)))

    return property_formulas, property_asserts


def create_property_formulas_chain(purposes):
    property_formulas = []
    property_asserts = []

    for k in range(0, MAX_CHAIN_LENGTH):
        f90 = Or(chain_smtVariables[k].Self_signed.Equals(BV(0, 5)), chain_smtVariables[k].Self_signed.Equals(BV(1, 5)))
        f91 = chain_smtVariables[k].Index.Equals(BV(k, 5))
        f9 = And([f90, f91])
        property_formulas.append(f9)
        property_asserts.append(to_smtlib_assert(f9))

        if k == 0:
            ## check leaf certificate purposes against user input
            temp = []
            for purpose in purposes:
                if purpose == 'serverAuth':
                    temp.append(chain_smtVariables[k].ExEKUserverauth)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'clientAuth':
                    temp.append(chain_smtVariables[k].ExEKUclientauth)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'codeSigning':
                    temp.append(chain_smtVariables[k].ExEKUcodesign)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'emailProtection':
                    temp.append(chain_smtVariables[k].ExEKUemailpro)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'timeStamping':
                    temp.append(chain_smtVariables[k].ExEKUtimestamp)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'OCSPSigning':
                    temp.append(chain_smtVariables[k].ExEKUocspsign)
                    temp.append(chain_smtVariables[k].Eku_present)
                elif purpose == 'digitalSignature':
                    temp.append(chain_smtVariables[k].ExKUdigitalSignature)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'nonRepudiation':
                    temp.append(chain_smtVariables[k].ExKUnonRepudiation)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'keyEncipherment':
                    temp.append(chain_smtVariables[k].ExKUkeyEncipherment)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'dataEncipherment':
                    temp.append(chain_smtVariables[k].ExKUdataEncipherment)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'keyAgreement':
                    temp.append(chain_smtVariables[k].ExKUkeyAgreement)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'keyCertSign':
                    temp.append(chain_smtVariables[k].ExKUkeyCertSign)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'cRLSign':
                    temp.append(chain_smtVariables[k].ExKUcRLSign)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'encipherOnly':
                    temp.append(chain_smtVariables[k].ExKUencipherOnly)
                    temp.append(chain_smtVariables[k].Ku_present)
                elif purpose == 'decipherOnly':
                    temp.append(chain_smtVariables[k].ExKUdecipherOnly)
                    temp.append(chain_smtVariables[k].Ku_present)
            f5 = And(temp)
            property_formulas.append(f5)
            property_asserts.append(to_smtlib_named_assert(f5, 'Wrong_purposes_for_leaf_certifcate'))

            # If a certificate contains both a key usage extension and an extended
            # key usage extension, then both extensions MUST be processed
            # independently and the certificate MUST only be used for a purpose
            # consistent with both extensions. If there is no purpose consistent
            # with both extensions, then the certificate MUST NOT be used for any
            # purpose.
            f71 = chain_smtVariables[k].ExEKUserverauth.Implies(
                Or(chain_smtVariables[k].ExKUdigitalSignature, chain_smtVariables[k].ExKUkeyEncipherment,
                   chain_smtVariables[k].ExKUkeyAgreement))
            f72 = chain_smtVariables[k].ExEKUclientauth.Implies(
                Or(chain_smtVariables[k].ExKUdigitalSignature,
                   chain_smtVariables[k].ExKUkeyAgreement))
            f73 = chain_smtVariables[k].ExEKUcodesign.Implies(chain_smtVariables[k].ExKUdigitalSignature)
            f74 = chain_smtVariables[k].ExEKUemailpro.Implies(
                Or(chain_smtVariables[k].ExKUdigitalSignature, chain_smtVariables[k].ExKUkeyEncipherment,
                   chain_smtVariables[k].ExKUkeyAgreement, chain_smtVariables[k].ExKUnonRepudiation))
            f75 = chain_smtVariables[k].ExEKUtimestamp.Implies(
                Or(chain_smtVariables[k].ExKUdigitalSignature, chain_smtVariables[k].ExKUnonRepudiation))
            f76 = chain_smtVariables[k].ExEKUocspsign.Implies(
                Or(chain_smtVariables[k].ExKUdigitalSignature, chain_smtVariables[k].ExKUnonRepudiation))
            f = And(chain_smtVariables[k].Ku_present, chain_smtVariables[k].Eku_present).Implies(
                And(f71, f72, f73, f74, f75, f76))
            property_formulas.append(f)
            property_asserts.append(
                to_smtlib_named_assert(f, 'inconsistent_purposes_in_certificate_{}'.format(k)))

        elif k >= 1:
            # Conforming implementations may choose to reject all version 1
            # and version 2 intermediate CA certificates
            f50 = Equals(chain_smtVariables[k].Self_signed, BV(0, 5)).Implies(
                Equals(chain_smtVariables[k].Version, Int(2)))
            property_formulas.append(f50)
            property_asserts.append(
                to_smtlib_named_assert(f50, 'Intermediate_ca_certificate_{}_with_older_version'.format(k)))
            f51 = And(chain_smtVariables[k].CA_present, chain_smtVariables[k].Bc_present)
            f52 = chain_smtVariables[k].Ku_present.Implies(chain_smtVariables[k].ExKUkeyCertSign)
            f5_ = And(f51, f52)
            property_formulas.append(f5_)
            property_asserts.append(to_smtlib_named_assert(f5_, 'Non_leaf_cert_{}_must_be_CA_cert'.format(k)))

            # The pathLenConstraint field is meaningful only if the cA boolean is
            # asserted and the key usage extension, if present, asserts the
            # keyCertSign bit (Section 4.2.1.3). In this case, it gives the
            # maximum number of non-self-issued intermediate certificates that
            # may follow this certificate in a valid certification path.
            f61 = f5_.Implies(chain_smtVariables[k].BC_pathlen_present.Implies(
                BVUGE(chain_smtVariables[k].BC_pathlen, count_non_self_signed_int_ca(k, 0))))
            property_formulas.append(f61)
            property_asserts.append(
                to_smtlib_named_assert(f61, 'CA_cert_{}_does_not_follow_pathLenConstraint'.format(k)))

    # If the certificate issuer is not the CRL
    # issuer, then the cRLIssuer field MUST be present and contain the Name
    # of the CRL issuer. If the certificate issuer is also the CRL issuer,
    #    then conforming CAs MUST omit the cRLIssuer field and MUST include
    #    the distributionPoint field.
    for k in range(0, MAX_CHAIN_LENGTH - 1):
        temp1 = [chain_smtVariables[k].DistpointcrlissuersList[i] for i in range(0, MAX_DISTPOINT)]
        f19_1 = And(chain_smtVariables[k].Crl_dist_present, chain_smtVariables[k + 1].Ku_present,
                    chain_smtVariables[k + 1].ExKUcRLSign.Iff(False)).Implies(And(temp1))
        temp2 = [And(chain_smtVariables[k].DistpointcrlissuersList[i].Iff(False),
                     chain_smtVariables[k].DistpointnamesList[i]) for i in range(0, MAX_DISTPOINT)]
        f19_2 = And(chain_smtVariables[k].Crl_dist_present, chain_smtVariables[k + 1].Ku_present,
                    chain_smtVariables[k + 1].ExKUcRLSign).Implies(And(temp2))
        f19 = And(f19_1, f19_2)
        property_formulas.append(f19)
        property_asserts.append(
            to_smtlib_named_assert(f19, 'wrong_structure_2_of_CRL_distribution_point_in_certificate_{}'.format(k)))

    # A certificate MUST NOT appear more than once in a prospective certification path.
    f22 = AllDifferent(chain_rawcert_smts)
    property_formulas.append(f22)
    property_asserts.append(to_smtlib_named_assert(f22, 'repeated_certificates_in_chain'))

    # Certificate users MUST be prepared to process the issuer
    # distinguished name and subject distinguished name
    # fields to perform name chaining for certification path validation
    for k in range(0, MAX_CHAIN_LENGTH - 1):
        f6 = generate_name_check_constraints(chain_smtVariables[k], chain_smtVariables[k + 1])
        property_formulas.append(f6)
        property_asserts.append(to_smtlib_named_assert(f6, 'wrong_name_chaining_in_certificate_{}'.format(k)))

    return property_formulas, property_asserts


## helper functions for converting to smt-libv2.6 syntax
def to_smtlib_named_assert(formula, name):
    buf = io.StringIO()
    p = SmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    output = "(assert (! {} :named {} ))".format(res, name)
    return output


def to_smtlib_assert(formula):
    buf = io.StringIO()
    p = SmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    output = "(assert {} )".format(res)
    return output


def to_smtlib_init(formulas, logic):
    buf = io.StringIO()
    script = SmtLibScript()
    script.add(name=smtcmd.SET_LOGIC,
               args=[logic])
    # Declare all types
    types = get_env().typeso.get_types(formulas, custom_only=True)
    for type_ in types:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    deps = formulas.get_free_variables()
    # Declare all variables
    for symbol in deps:
        assert symbol.is_symbol()
        script.add(name=smtcmd.DECLARE_FUN, args=[symbol])

    script.serialize(buf, False)
    res = buf.getvalue()
    buf.close()
    return res


# call LDAP
def call_stringprep(Value, ValType):
    try:
        if ValType == 30:  # bmpstring
            Value = bytes(Value).decode('utf-16-be')
        elif ValType == 19:  # printablestring
            Value = bytes(Value).decode('us-ascii')
        elif ValType == 12:  # UTF8String
            Value = bytes(Value).decode('utf-8')
        elif ValType == 28:  # universalstring
            Value = bytes(Value).decode('utf-32-be')
        elif ValType == 20:  # teletexstring
            Value = bytes(Value).decode('iso-8859-1')
    except:
        return None

    stringprep = Popen(
        ["{}/stringprep/runStringPrep".format(extra_location), Value],
        stdout=PIPE)
    (output, err) = stringprep.communicate()
    stringprep.wait()
    Value = output[1:len(output) - 2]
    if Value == b'ERROR!!':
        return None

    return int.from_bytes(Value, byteorder='big')


def generate_time_constraints(Yr1, Mon1, Day1, Hr1, Min1, Sec1, Yr2, Mon2, Day2, Hr2, Min2, Sec2):
    # time1 <= time2
    f21_12 = Ite(Equals(Sec1, Sec2), Bool(True), Bool(False))
    f21_11 = Ite(BVULT(Sec1, Sec2), Bool(True), f21_12)
    f21_10 = Ite(Equals(Min1, Min2), f21_11, Bool(False))
    f21_9 = Ite(BVULT(Min1, Min2), Bool(True), f21_10)
    f21_8 = Ite(Equals(Hr1, Hr2), f21_9, Bool(False))
    f21_7 = Ite(BVULT(Hr1, Hr2), Bool(True), f21_8)
    f21_6 = Ite(Equals(Day1, Day2), f21_7, Bool(False))
    f21_5 = Ite(BVULT(Day1, Day2), Bool(True), f21_6)
    f21_4 = Ite(Equals(Mon1, Mon2), f21_5, Bool(False))
    f21_3 = Ite(BVULT(Mon1, Mon2), Bool(True), f21_4)
    f21_2 = Ite(Equals(Yr1, Yr2), f21_3, Bool(False))
    f21_1 = Ite(BVULT(Yr1, Yr2), Bool(True), f21_2)
    return f21_1


def generate_name_check_constraints(cert1, cert2):
    issuer1 = cert1.Issuer
    subject2 = cert2.Subject
    issuer1_len = cert1.Issuer_length
    subject2_len = cert2.Subject_length
    issuer1_rdns_size = cert1.Issuer_rdns_size
    subject2_rdns_size = cert2.Subject_rdns_size

    fs = [issuer1_len.Equals(subject2_len)]
    for i in range(0, MAX_NAME_LENGTH):
        fs.append(matchRdns(Select(issuer1, Int(i)), Select(issuer1_rdns_size, Int(i)),
                            Select(subject2, Int(i)), Select(subject2_rdns_size, Int(i))))

    return And(fs)


def count_non_self_signed_int_ca(start, end):
    # between 0 to start
    # return BV(start - end - 1, 5)
    if start == 1:
        return BV(0, 5)

    sum = Symbol("Sum_{}".format(start), BVType(5))
    c = 0
    for p in range(end + 1, start):
        c = c + 1
        if p == end + 1:
            sum = BVAdd(BV(0, 5), chain_smtVariables[p].Self_signed)
        else:
            sum = BVAdd(sum, chain_smtVariables[p].Self_signed)

    output = BVSub(BV(c, 5), sum)
    return output


def matchRdns(rdn1, size1, rdn2, size2):
    fs = [size1.Equals(size2)]
    for i in range(0, MAX_NAME_RDNSET_LENGTH):
        y = []
        for j in range(0, MAX_NAME_RDNSET_LENGTH):
            y.append(matchNas(Select(rdn1, Int(i)), Select(rdn2, Int(j))))
        fs.append(Or(y))
    return And(fs)


def matchNas(na1, na2):
    f1 = Select(na1, Int(0)).Equals(Select(na2, Int(0)))
    f2 = Select(na1, Int(1)).Equals(Select(na2, Int(1)))
    f3 = Select(na1, Int(2)).Equals(Select(na2, Int(2)))
    return And(f1, f2, f3)


def gen_cons_ca_in_store(cert_list, ca_store, ca_store_sizes):
    global MAX_CA_STORE_SIZE
    property_formulas = []
    assignment_formulas = []
    property_asserts = []
    assignment_asserts = []

    lastcert = Symbol("lastcert", INT)
    lastcert_size = Symbol("lastcert_size", INT)

    if not only_smt_global:
        temp1 = []
        a1 = lastcert.Equals(Int(cert_list[len(cert_list) - 1].RawCert))
        a2 = lastcert_size.Equals(Int(cert_list[len(cert_list) - 1].RawCert_size))
        temp1.append(a1)
        temp1.append(a2)

        for k in range(0, len(ca_store)):
            trust_cert = Symbol("trust_cert_{}".format(k), INT)
            trust_cert_size = Symbol("trust_cert_size_{}".format(k), INT)
            a3 = trust_cert.Equals(Int(ca_store[k]))
            a4 = trust_cert_size.Equals(Int(ca_store_sizes[k]))
            temp1.append(a3)
            temp1.append(a4)
        assignment_formulas = [And(temp1)]
        assignment_asserts = [to_smtlib_assert(assignment_formulas[0])]
        MAX_CA_STORE_SIZE = len(ca_store)

    temp2 = []
    for k in range(0, MAX_CA_STORE_SIZE):
        trust_cert = Symbol("trust_cert_{}".format(k), INT)
        trust_cert_size = Symbol("trust_cert_size_{}".format(k), INT)
        f_ = And(lastcert.Equals(trust_cert), (lastcert_size.Equals(trust_cert_size)))
        temp2.append(f_)
    property_formulas = [Or(temp2)]
    property_asserts = [to_smtlib_named_assert(property_formulas[0], 'untrusted_root_CA')]

    return assignment_formulas, property_formulas, assignment_asserts, property_asserts


def gen_cons_rsa_signature(cert_list, dsl_parser):
    property_formulas = []
    assignment_formulas = []
    property_asserts = []
    assignment_asserts = []

    if not only_smt_global:
        temp1 = []
        for k in range(0, len(cert_list) - 1):
            cert1 = cert_list[k]
            cert2 = cert_list[k + 1]
            ck = chain_smtVariables[k]
            cert1sig = int.from_bytes(cert1.Signature, byteorder='big')
            try:
                cert2n = cert2.TbsCertificate.SubjectPKI.PublicKey.n[0]
                cert2n_size = cert2.TbsCertificate.SubjectPKI.PublicKey.n[1]
                cert2e = cert2.TbsCertificate.SubjectPKI.PublicKey.e[0]

                if cert2n_size * 8 < 2048:
                    errors.append("error : RSA public key size must be greater than or equal to 2048 bits")
                    return [], [], [], []
            except:
                continue

            hashFromsign1 = "%X" % pow(cert1sig, cert2e, cert2n)
            if len(hashFromsign1) % 2 != 0:
                hashFromsign1 = '000' + hashFromsign1
            else:
                hashFromsign1 = '00' + hashFromsign1

            try:
                if dsl_parser:
                    sig_bytes = bytes.fromhex(hashFromsign1)
                    parser_rsa_signature_dsl.initialize(sig_bytes)
                    temp = parser_rsa_signature_dsl.Pkcs(0)
                    if not temp[0]:
                        raise Exception()
                    parsed_signature1 = [temp[2][0], temp[2][1]]
                else:
                    parsed_signature1 = parser_rsa_signature.run(hashFromsign1)
            except:
                errors.append("Couldn't parse rsa signature")
                return [], [], [], []

            parsed_sigid1 = parsed_signature1[0].Id[0]
            parsed_digest1 = parsed_signature1[1]
            tbs1 = cert1.TbsCertificate.RawTbs

            if parsed_sigid1 == int('2B0E07020301', 16) \
                    or parsed_sigid1 == int('2B0E030202', 16) \
                    or parsed_sigid1 == int('2B0E030203', 16) \
                    or parsed_sigid1 == int('2B0E03021A', 16):
                # md2, md4, md5, sha1
                errors.append("error : Insecure signature algorithm")
                return [], [], [], []
            elif parsed_sigid1 == int('608648016503040201', 16):
                hashoftbs1 = sha256(tbs1).hexdigest()
            elif parsed_sigid1 == int('608648016503040204', 16):
                hashoftbs1 = sha224(tbs1).hexdigest()
            elif parsed_sigid1 == int('608648016503040202', 16):
                hashoftbs1 = sha384(tbs1).hexdigest()
            elif parsed_sigid1 == int('608648016503040203', 16):
                hashoftbs1 = sha512(tbs1).hexdigest()
            else:
                continue

            a_1 = ck.Sig_digest.Equals(Int(int.from_bytes(parsed_digest1, byteorder='big')))
            a_2 = ck.Tbs_hash.Equals(Int(int(hashoftbs1, 16)))
            temp1.append(a_1)
            temp1.append(a_2)
        assignment_formulas = [And(temp1)]
        assignment_asserts = [to_smtlib_assert(assignment_formulas[0])]

    temp2 = []
    for k in range(0, MAX_CHAIN_LENGTH - 1):
        ck = chain_smtVariables[k]
        ck1 = chain_smtVariables[k + 1]
        f_ = ck1.RSA_pk_present.Implies(ck.Sig_digest.Equals(ck.Tbs_hash))
        temp2.append(f_)
    property_formulas = [And(temp2)]
    property_asserts = [to_smtlib_named_assert(property_formulas[0], 'rsa_signature_not_verified')]
    return assignment_formulas, property_formulas, assignment_asserts, property_asserts
