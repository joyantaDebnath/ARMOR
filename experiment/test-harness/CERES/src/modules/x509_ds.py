class Certificate:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.TbsCertificate = f[0]
        self.SignatureAlgorithm = f[1]
        self.Signature = f[2]
        self.RawCert = None
        self.RawCert_size = None
        self.ski = None
        self.aki = None


class TbsCertificate:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Version = f[0]
        self.Serial = f[1]
        self.SignatureAlgorithm = f[2]
        self.Issuer = f[3]
        self.Validity = f[4]
        self.Subject = f[5]
        self.SubjectPKI = f[6]
        self.IssuerUID = f[7]
        self.SubjectUID = f[8]
        self.Extensions = f[9]
        self.RawTbs = None


class SignatureAlgorithm:
    def __init__(self, f):
        if type(f) == list and len(f) == 1:  # DSL
            f = f[0]
        self.Value = f


class AlgorithmIdentifier:
    def __init__(self, f):
        self.Id = f[0]
        self.Parameter = f[1]


class RSAkey:
    def __init__(self, f):
        if type(f) == list and len(f) == 1:  # DSL
            f = f[0]
        self.n = f[0]
        self.e = f[1]


class SubjectPKI:
    def __init__(self, f):
        self.AlgorithmId = f[0]
        self.PublicKey = f[1]


class IssuerDN:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.List = f


class SubjectDN:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.List = f


class RDNset:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.List = f


class ValidityPeriod:
    def __init__(self, f):
        self.NotBefore = f[0]
        self.NotAfter = f[1]


class NotBefore:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == list and len(f[0]) == 7:  # DSL
            if f[0][6] == 23:
                f = UtcTimeMod(f[0])
            elif f[0][6] == 24:
                f = f[0]
        elif len(f) == 7:  # DSL
            if f[6] == 23:
                f = UtcTimeMod(f)
            elif f[6] == 24:
                f = f
        self.Year = f[0]
        self.Month = f[1]
        self.Day = f[2]
        self.Hour = f[3]
        self.Minute = f[4]
        self.Second = f[5]


class NotAfter:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == list and len(f[0]) == 7:  # DSL
            if f[0][6] == 23:
                f = UtcTimeMod(f[0])
            elif f[0][6] == 24:
                f = f[0]
        elif len(f) == 7:  # DSL
            if f[6] == 23:
                f = UtcTimeMod(f)
            elif f[6] == 24:
                f = f
        self.Year = f[0]
        self.Month = f[1]
        self.Day = f[2]
        self.Hour = f[3]
        self.Minute = f[4]
        self.Second = f[5]


class Extn:
    def __init__(self, f):
        self.ExtnId = f[0]
        self.Critical = f[1]
        self.ExtnValue = f[2]


class Auth_key_id:
    def __init__(self, f):
        self.KeyId = f[0]
        self.CertificateIssuer = f[1]
        self.CertificateSerial = f[2]


class Sub_key_id:
    def __init__(self, f):
        if type(f) == list and len(f) == 1:  # DSL
            f = f[0]
        self.KeyId = f


class Key_usage:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == list:  # DSL
            f = f[0]
        self.Purposes = f


class Ext_key_usage:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == list:  # DSL
            f = f[0]
        self.Purposes = f


class Subject_alt_name:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Value = f


class Issuer_alt_name:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Value = f


class GenerelName:
    def __init__(self, f):
        self.Type = f[0]
        self.Value = f[1]


class Basic_constraints:
    def __init__(self, f):
        self.CA = f[0]
        self.PathLen = f[1]


class PolicyInformation:
    def __init__(self, f):
        self.PolicyIdentifier = f[0]
        self.PolicyQualifiers = f[1]


class Cert_policies:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Value = f


class CrlIssuer:
    def __init__(self, f):
        self.Value = f


class AuthorityCertIssuer:
    def __init__(self, f):
        self.Value = f


class DistributionPoint:
    def __init__(self, f):
        self.DistributionPoint = f[0]
        self.Reasons = f[1]
        self.CRLIssuer = f[2]


class CRL_dist_points:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Value = f


class AccessDescription:
    def __init__(self, f):
        self.AccessMethod = f[0]
        self.AccessLocation = f[1]


class Authority_info_access:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.Value = f


class Unknown_extension:
    def __init__(self, f):
        if type(f) == list and len(f) == 1:  # DSL
            f = f[0]
        self.OctetString = f


class Policy_mapping:
    def __init__(self, f):
        self.OctetString = f


class Name_constraints:
    def __init__(self, f):
        self.OctetString = f


class Subject_directory_attributes:
    def __init__(self, f):
        self.OctetString = f


class Policy_constraints:
    def __init__(self, f):
        self.OctetString = f


class Inhibit_anypolicy:
    def __init__(self, f):
        self.OctetString = f


class Freshest_crl:
    def __init__(self, f):
        self.OctetString = f


class Subject_info_access:
    def __init__(self, f):
        self.OctetString = f


class Parameter:
    def __init__(self, f):
        self.Type = f[0]
        self.Value = f[1]


class String:
    def __init__(self, f):
        self.Type = f[0]
        self.Value = f[1]


class Attribute:
    def __init__(self, f):
        self.Id = f[0]
        self.Value = f[1]


class Extns:
    def __init__(self, f):
        if len(f) == 1 and type(f[0]) == tuple:  # DSL
            f = f[0]
        self.List = f


def pretty_printx(clas, indent=0):
    print(' ' * indent + type(clas).__name__ + ':')
    indent += 4
    for k, v in clas.__dict__.items():
        if '__dict__' in dir(v):
            pretty_printx(v, indent)
        elif type(v).__name__ == 'tuple':
            for x in v:
                if x is None:
                    print(' ' * indent + k + ': ' + 'None')
                elif type(x).__name__ == 'int':
                    print(' ' * indent + k + ': ' + str(x))
                elif type(x).__name__ == 'bytes':
                    print(' ' * indent + k + ': ' + str(x))
                elif type(x).__name__ == 'tuple':
                    for y in x:
                        pretty_printx(y, indent)
                else:
                    pretty_printx(x, indent)
        elif k == 'ski' or k == 'aki' or k == 'RawCert' or k == 'RawCert_size' or k == 'RawTbs':
            continue
        else:
            print(' ' * indent + k + ': ' + str(v))


class Cert_smtVariables:
    def __init__(self, Self_signed, Index, Tbs_hash, Sig_digest, Version, Serial, Serial_size,
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
                 Eku_present, ExEKUserverauth, ExEKUclientauth, ExEKUcodesign, ExEKUemailpro, ExEKUtimestamp,
                 ExEKUocspsign,
                 San_present, SanSizenozero, SanCritical,
                 Issueruniid_present, Subjectuniid_present,
                 Issuer, Issuer_length, Issuer_rdns_size, Subject, Subject_length, Subject_rdns_size,
                 Policy_present, PolicyIdsList, Crl_dist_present, DistpointnamesList,
                 DistpointreasonsList,
                 DistpointcrlissuersList,
                 Aki_keyid_present, Ski_keyid_present):
        self.Tbs_hash = Tbs_hash
        self.Sig_digest = Sig_digest
        self.Version = Version
        self.Serial = Serial
        self.Serial_size = Serial_size
        self.Cert_sign_algo_id = Cert_sign_algo_id
        self.Cert_sign_algo_id_size = Cert_sign_algo_id_size
        self.Cert_sign_algo_param_type = Cert_sign_algo_param_type
        self.Cert_sign_algo_param = Cert_sign_algo_param
        self.Cert_sign_algo_param_size = Cert_sign_algo_param_size
        self.Tbs_sign_algo_id = Tbs_sign_algo_id
        self.Tbs_sign_algo_id_size = Tbs_sign_algo_id_size
        self.Tbs_sign_algo_param_type = Tbs_sign_algo_param_type
        self.Tbs_sign_algo_param = Tbs_sign_algo_param
        self.Tbs_sign_algo_param_size = Tbs_sign_algo_param_size
        self.NotbeforeYr = NotbeforeYr
        self.NotbeforeMon = NotbeforeMon
        self.NotbeforeDay = NotbeforeDay
        self.NotbeforeHr = NotbeforeHr
        self.NotbeforeMin = NotbeforeMin
        self.NotbeforeSec = NotbeforeSec
        self.NotafterYr = NotafterYr
        self.NotafterMon = NotafterMon
        self.NotafterDay = NotafterDay
        self.NotafterHr = NotafterHr
        self.NotafterMin = NotafterMin
        self.NotafterSec = NotafterSec
        self.CurtimeYr = CurtimeYr
        self.CurtimeMon = CurtimeMon
        self.CurtimeDay = CurtimeDay
        self.CurtimeHr = CurtimeHr
        self.CurtimeMin = CurtimeMin
        self.CurtimeSec = CurtimeSec
        self.RSA_pk_present = RSA_pk_present
        self.Extensions_present = Extensions_present
        self.ExtensionsList = ExtensionsList
        self.ExtensionsCriticalsList = ExtensionsCriticalsList
        self.ExtensionsKnownList = ExtensionsKnownList
        self.Bc_present = Bc_present
        self.CA_present = CA_present
        self.BC_pathlen = BC_pathlen
        self.Ku_present = Ku_present
        self.ExKUdigitalSignature = ExKUdigitalSignature
        self.ExKUnonRepudiation = ExKUnonRepudiation
        self.ExKUkeyEncipherment = ExKUkeyEncipherment
        self.ExKUdataEncipherment = ExKUdataEncipherment
        self.ExKUkeyAgreement = ExKUkeyAgreement
        self.ExKUkeyCertSign = ExKUkeyCertSign
        self.ExKUcRLSign = ExKUcRLSign
        self.ExKUencipherOnly = ExKUencipherOnly
        self.ExKUdecipherOnly = ExKUdecipherOnly
        self.San_present = San_present
        self.SanSizenozero = SanSizenozero
        self.SanCritical = SanCritical
        self.Issueruniid_present = Issueruniid_present
        self.Subjectuniid_present = Subjectuniid_present
        self.Issuer = Issuer
        self.Issuer_length = Issuer_length
        self.Issuer_rdns_size = Issuer_rdns_size
        self.Subject = Subject
        self.Subject_length = Subject_length
        self.Subject_rdns_size = Subject_rdns_size
        self.Policy_present = Policy_present
        self.PolicyIdsList = PolicyIdsList
        self.Crl_dist_present = Crl_dist_present
        self.DistpointnamesList = DistpointnamesList
        self.DistpointreasonsList = DistpointreasonsList
        self.DistpointcrlissuersList = DistpointcrlissuersList
        self.ExEKUserverauth = ExEKUserverauth
        self.ExEKUclientauth = ExEKUclientauth
        self.ExEKUcodesign = ExEKUcodesign
        self.ExEKUemailpro = ExEKUemailpro
        self.ExEKUtimestamp = ExEKUtimestamp
        self.ExEKUocspsign = ExEKUocspsign
        self.Eku_present = Eku_present
        self.Index = Index
        self.Self_signed = Self_signed
        self.Ski_keyid_present = Ski_keyid_present
        self.Aki_keyid_present = Aki_keyid_present
        self.BC_pathlen_present = BC_pathlen_present


## for dsl
def UtcTimeMod(f):
    year = f[0]
    mon = f[1]
    day = f[2]
    hour = f[3]
    min = f[4]
    sec = f[5]

    if year >= 50 and year <= 99:
        year = 1900 + year
    else:
        year = 2000 + year

    return [year, mon, day, hour, min, sec]


class GenericTime:
    def __init__(self, a, b, c, d, e, f):
        self.Year = a
        self.Month = b
        self.Day = c
        self.Hour = d
        self.Minute = e
        self.Second = f
