from cryptography.hazmat.primitives.serialization import load_der_public_key
from cryptography.hazmat.backends import default_backend

def hex_to_int(inp):
    res = ""
    for x in inp.strip().split(" "):
        res = res + str(int(x, 16)) + " "
    return res.strip()

def int_to_hex(inp):
    res = ""
    for x in inp.strip().split(" "):
        res = res + "" + '{:02x}'.format(int(x))
    return res

def hex_to_bytes(inp):
    return bytes.fromhex(inp)


def int_to_Bytes(inp):
    return hex_to_bytes(int_to_hex(inp))

tbs_bytes = []
sign_oids = []
signatures = []
pks = []
purposes = []

sign_oid_map = {
    "6 9 42 134 72 134 247 13 1 1 11": "sha256WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 12": "sha384WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 13": "sha512WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 14": "sha224WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 5": "sha1WithRSAEncryption",
    '6 8 42 134 72 206 61 4 3 1': 'ecdsa-with-SHA224',
    '6 8 42 134 72 206 61 4 3 2': 'ecdsa-with-SHA256',
    '6 8 42 134 72 206 61 4 3 3': 'ecdsa-with-SHA384',
    '6 8 42 134 72 206 61 4 3 4': 'ecdsa-with-SHA512'
}

sign_oid_map_insecure = {
    "6 9 42 134 72 134 247 13 1 1 2": "md2WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 3": "md4WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 4": "md5WithRSAEncryption"
}

eku_oid_purpose_map = {
    "6 8 43 6 1 5 5 7 3 1": "serverAuth",
    "6 8 43 6 1 5 5 7 3 2": "clientAuth",
    "6 8 43 6 1 5 5 7 3 3": "codeSigning",
    "6 8 43 6 1 5 5 7 3 4": "emailProtection",
    "6 8 43 6 1 5 5 7 3 8": "timeStamping",
    "6 8 43 6 1 5 5 7 3 9": "OCSPSigning",
    "6 4 85 29 37 0": "anyExtendedKeyUsage"
}

def process_eku_purposes(ekulist):
    ret = []
    if ekulist != "":
        ekulist = ekulist.split(" @@")[:-1]        
        for p in ekulist:
            if p.strip() in eku_oid_purpose_map:
                ret.append(eku_oid_purpose_map[p.strip()])
    return ret

def readData(filepath):
    f = open(filepath, "r")
    lines = f.readlines()

    for i in range(0, len(lines)):
        if (i % 6 == 0):  # tbs bytes
            tbs_bytes.append(int_to_Bytes(lines[i].strip()))
        elif (i % 6 == 1):  # signature
            if lines[i].strip().startswith("0 "):  ## 0 as padding byte
                lines_i_0_stripped = lines[i].strip()[2:]
                signatures.append(int_to_Bytes(lines_i_0_stripped))
            else:  ## without padding byte
                signatures.append(int_to_Bytes(lines[i].strip()))
        elif (i % 6 == 2):  # pk
            pks.append(load_der_public_key(int_to_Bytes(lines[i].strip()), backend=default_backend()))
        elif (i % 6 == 3):  # sign oid
            sign_oids.append(lines[i].strip())
        elif (i % 6 == 4):  # eku purposes
            purposes.append(process_eku_purposes(lines[i].strip()))

def verifyCertificatePurpose(input_purpose):
    end_cert_purposes = None
    if len(purposes) > 0:
        end_cert_purposes = purposes[0]

    if input_purpose == None or end_cert_purposes == None:
        return True
    else:
        return (input_purpose in end_cert_purposes)
