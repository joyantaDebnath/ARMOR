import argparse
import base64
import os
import sys

from modules.chain_builder import chain_builder
from modules.parsers.combinator_based import parser_tbs_raw
from modules.parsers.combinator_based import parser_x509
from modules.parsers.dsl_based import parser_x509_dsl
from modules.semantic import semantic
from modules.semantic import semantic_quick

current_version = "1.0-11_08_2021"

sys.set_int_max_str_digits(10000)

################################ pre-processor module ############################
def pre_process_chain_mod(path):
    errors = []
    cert_list_decoded = []
    cert_list_raw = []

    file = open(path, 'r')
    lines = "".join(file.readlines())
    file.close()

    count_begin = lines.count('-----BEGIN CERTIFICATE-----')
    count_end = lines.count('-----END CERTIFICATE-----')
    if count_begin == count_end and count_begin > 0:
        lines = lines.replace('-----BEGIN CERTIFICATE-----', '')
        lines = lines.replace('-----END CERTIFICATE-----', ' ')
        lines = lines.replace('\n', '')
        tempChain = lines.split(' ')

        for f in range(0, len(tempChain)):
            if tempChain[f] != '':
                try:
                    cert = base64.b64decode(tempChain[f].strip()).hex().upper()
                    cert_list_decoded.append(cert)
                    cert_list_raw.append(tempChain[f].strip())
                except:
                    cert_list_decoded = []
                    cert_list_raw = []
                    break
    try:
        assert len(cert_list_decoded) > 0 \
               and len(cert_list_decoded) == count_begin \
               and count_begin == count_end
    except AssertionError:
        errors.append("Couldn't decode/read the certificate chain")

    return errors, cert_list_decoded, cert_list_raw


################################ parser module ###################################
def parser_mod(cert_list_decoded, dsl_parser, show_chain):
    errors = []
    cert_list_parsed = []

    for k in range(0, len(cert_list_decoded)):
        try:
            if dsl_parser:
                cert_bytes = bytes.fromhex(cert_list_decoded[k])
                parser_x509_dsl.initialize(cert_bytes)
                flag, size, parsedCert, cur_index = parser_x509_dsl.run()
                rawCert = int(cert_list_decoded[k], 16)
            else:
                (flag, size, parsedCert), rawCert = parser_x509.run(cert_list_decoded[k])
        except:
            (flag, size, parsedCert), rawCert = (False, -1, ()), None
        try:
            assert flag and size == len(cert_list_decoded[k]) / 2
            parsedCert.RawCert = rawCert
            parsedCert.RawCert_size = len(cert_list_decoded[k])
            parsedCert.TbsCertificate.RawTbs = parser_tbs_raw.run(cert_list_decoded[k])
            cert_list_parsed.append(parsedCert)
            if show_chain:
                print("Certificate {}".format(k))
                parser_x509.pretty_printx(parsedCert)
        except AssertionError:
            if dsl_parser:
                errors.append("Couldn't parse certificate {}; reason : {}".format(k, parser_x509_dsl.error()))
            else:
                errors.append("Couldn't parse certificate {}; reason : {}".format(k, parser_x509.error()))
            cert_list_parsed = []
            break

    ## chain_build
    try:
        cert_list_parsed_w_info = chain_builder.set_more_info(cert_list_parsed)
        cert_list_ordered = chain_builder.reorder(cert_list_parsed_w_info)
        return errors, cert_list_ordered
    except:
        return errors, [cert_list_parsed]


################################ semantic module ###################################
def semantic_mod(cert_list_parsed, dsl_parser, lfsc, purposes, ca_store, ca_store_sizes, only_smt, chain_len_sym):
    errors, postfix = semantic.generate_smtlib_formulas(cert_list_parsed, dsl_parser, lfsc, purposes, ca_store, ca_store_sizes,
                                               only_smt, chain_len_sym)
    if len(errors) > 0:
        return errors, None, None, None
    return semantic.call_smt_solver(lfsc, postfix)


def handle_spec_consistency_check(chain_len):
    errors, result, unsat_core, proof_check_status = semantic_mod([], False, True, [], [], 0, True, chain_len)
    try:
        assert len(errors) == 0 and result == "sat"
        print("Specification is consistent")
    except AssertionError:
        if len(errors) > 0:
            print("Some error occured ...")
            print(";".join(errors))
        else:
            print("Specification is inconsistent")
            print("UNSAT-core : {}; Proof-check-status : {}".format(unsat_core, proof_check_status))


################################ ENTRY POINT #####################################
# usage: ceres [-h] [--input INPUT] [--ca-store CA_STORE] [--check-purpose CHECK_PURPOSE [CHECK_PURPOSE ...]] [--check-proof] [--show-chain] [--check-spec] [--dsl-parser] [--version]
parser = argparse.ArgumentParser(description='CERES command-line arguments')
parser.add_argument('--input', type=str,
                    help='Input chain location')
parser.add_argument('--ca-store', type=str, default='/etc/ssl/certs/ca-certificates.crt',
                    help='Trusted CA store location; default=/etc/ssl/certs/ca-certificates.crt')
parser.add_argument('--check-purpose', nargs='+',
                    help='list of expected purposes of End certificate: serverAuth, clientAuth, codeSigning, emailProtection, timeStamping, OCSPSigning, digitalSignature, nonRepudiation, keyEncipherment, dataEncipherment, keyAgreement, keyCertSign, cRLSign, encipherOnly, decipherOnly; default=anyPurpose',
                    default=[])
parser.add_argument('--check-proof', action='store_true',
                    help='Check UNSAT proof; default=False')
parser.add_argument('--show-chain', action='store_true',
                    help='Show certificates; default=False')
parser.add_argument('--check-spec', action='store_true',
                    help='Check specification SAT; default=False')
parser.add_argument('--dsl-parser', action='store_true',
                    help='Enable PG-based parser; default=False')
parser.add_argument('--version', action='store_true',
                    help='Show current CERES version; default=False')
parser.add_argument('--asn1parse', action='store_true',
                    help='Only parse the input certificates; default=False')
parser.add_argument('--quick-semantic-check-sc', action='store_true',
                    help='Quick semantic check (no SMT solver) for a single certificate; default=False')
args = parser.parse_args()

input_chain = args.input
input_CA_store = args.ca_store
input_lfsc = args.check_proof
input_show_chain = args.show_chain
input_purposes = args.check_purpose
input_only_smt = args.check_spec
temp_parser = args.dsl_parser
show_version = args.version
asn1parse = args.asn1parse
quickSemChkCert = args.quick_semantic_check_sc

if input_chain == None:
    if show_version:
        print(current_version)
    if input_only_smt:  # check specification consistency
        print("Checking specification consistency ...")
        try:
            chain_len = int(input("Enter symbolic certificate chain length:"))
        except:
            print("Invalid length; must be between 1 to 32")
            sys.exit(-1)

        if chain_len >= 1 and chain_len <= 32:
            handle_spec_consistency_check(chain_len)
        else:
            print("Invalid length; must be between 1 to 32")
    if not (show_version or input_only_smt):
        print("Error : input certificate chain required")
    sys.exit(-1)

if temp_parser:
    input_dsl_parser = True
else:
    input_dsl_parser = False

for purpose in input_purposes:
    if purpose == 'serverAuth':
        continue
    elif purpose == 'clientAuth':
        continue
    elif purpose == 'codeSigning':
        continue
    elif purpose == 'emailProtection':
        continue
    elif purpose == 'timeStamping':
        continue
    elif purpose == 'OCSPSigning':
        continue
    elif purpose == 'digitalSignature':
        continue
    elif purpose == 'nonRepudiation':
        continue
    elif purpose == 'keyEncipherment':
        continue
    elif purpose == 'dataEncipherment':
        continue
    elif purpose == 'keyAgreement':
        continue
    elif purpose == 'keyCertSign':
        continue
    elif purpose == 'cRLSign':
        continue
    elif purpose == 'encipherOnly':
        continue
    elif purpose == 'decipherOnly':
        continue
    else:
        print(
            "Error : Purposes are not supported (supported purposes: serverAuth, "
            "clientAuth, codeSigning, emailProtection, timeStamping, OCSPSigning, "
            "digitalSignature, nonRepudiation, keyEncipherment, dataEncipherment, "
            "keyAgreement, keyCertSign, cRLSign, encipherOnly, decipherOnly"
            ")")
        sys.exit(-1)

if not (input_chain.endswith((".pem", ".crt")) \
        and input_CA_store.endswith((".pem", ".crt")) \
        and os.path.exists(input_chain) and os.path.exists(input_CA_store)):
    print("Error : Input file or CA store doesn't exist or not supported (supported formats: .pem, .crt)")
    sys.exit(-1)

# call chain pre-processor module
errors, cert_list_decoded, cert_list_raw = pre_process_chain_mod(input_chain)
try:
    assert len(errors) == 0
except AssertionError:
    print("Chain pre-process error...exiting")
    print(";".join(errors))
    sys.exit(-1)

if not asn1parse:
    # pre-process root CA store
    errors, ca_store, ca_list_raw = pre_process_chain_mod(input_CA_store)
    try:
        assert len(errors) == 0
        ca_store_certs = [int(ca_store[i], 16) for i in range(0, len(ca_store))]
        ca_store_certs_sizes = [len(x) for x in ca_store]
    except AssertionError:
        print("CA store pre-process error...exiting")
        print(";".join(errors))
        sys.exit(-1)

# call parser module
errors, cert_list_parsed = parser_mod(cert_list_decoded, input_dsl_parser, input_show_chain)
try:
    assert len(errors) == 0
    print("Succesfully parsed certificates")
except AssertionError:
    print("Certificate chain parsing error...exiting")
    print(";".join(errors))
    sys.exit(-1)

if not asn1parse:
    # call semantic checker module
    cert_list_parsed_new = []
    for element in cert_list_parsed:
        if element not in cert_list_parsed_new:
            cert_list_parsed_new.append(element)

    for i in range(0, len(cert_list_parsed_new)):
        if quickSemChkCert:
            for cert in cert_list_parsed_new[i]:
                result = semantic_quick.check(cert)
                print(result)
        else:
            errors, result, unsat_core, proof_check_status = semantic_mod(cert_list_parsed_new[i], input_dsl_parser,
                                                                          input_lfsc,
                                                                          input_purposes,
                                                                          ca_store_certs,
                                                                          ca_store_certs_sizes, input_only_smt, -1)
            try:
                assert len(errors) == 0 and result == "sat"
                print("Certificate chain verification : OK")
                break
            except AssertionError:
                if i == len(cert_list_parsed_new) - 1:
                    print("Certificate chain verification : Falied (Semantic Error)")
                    if len(errors) > 0:
                        print(";".join(errors))
                    else:
                        print("UNSAT-core : {}; Proof-check-status : {}".format(unsat_core, proof_check_status))
                else:
                    pass
                    continue
