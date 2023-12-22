import os.path
import subprocess
import sys
import argparse
import os
import random

from pathlib import Path
from pem import *
from base64 import *
from verifySignature import *

def main():

    ### command-line argument processing
    # usage: ./armor-driver [-h] [--chain INPUT] [--trust_store CA_STORE] [--purpose CHECK_PURPOSE] 
    parser = argparse.ArgumentParser(description='ARMOR command-line arguments')
    parser.add_argument('--chain', type=str,
                        help='Input certificate chain location')
    parser.add_argument('--trust_store', type=str, default='/etc/ssl/certs/ca-certificates.crt',
                        help='Trust anchor location; default=/etc/ssl/certs/ca-certificates.crt')
    parser.add_argument('--purpose', type=str,
                        help='expected purpose for end-user certificate: serverAuth, clientAuth, codeSigning, emailProtection, timeStamping, or OCSPSigning, default=anyExtendedKeyUsage')
    args = parser.parse_args()

    input_chain = args.chain
    input_CA_store = args.trust_store
    input_purpose = args.purpose

    if (input_purpose != 'serverAuth' and \
        input_purpose != 'clientAuth' and \
        input_purpose != 'codeSigning' and \
        input_purpose != 'emailProtection' and \
        input_purpose != 'timeStamping' and \
        input_purpose != 'OCSPSigning' and \
        input_purpose != 'anyExtendedKeyUsage' and input_purpose != None):
            print(
            "Error : Purposes are not supported (supported purposes: serverAuth, "
            "clientAuth, codeSigning, emailProtection, timeStamping, OCSPSigning, anyExtendedKeyUsage")
            sys.exit(-1)

    if not (input_chain.endswith((".pem", ".crt")) \
        and input_CA_store.endswith((".pem", ".crt")) \
        and os.path.exists(input_chain) and os.path.exists(input_CA_store)):
        print("Error : Input file or CA store doesn't exist or not supported (supported formats: .pem, .crt)")
        sys.exit(-1)

    #############################

    ep = random.random()
    args = sys.argv
    home_dir = str(Path.home())
    filename_certchain = input_chain
    filename_armor_output = home_dir + "/.residuals/temp_{}.txt".format(ep)

    if not os.path.exists(home_dir + "/.residuals/"):
        os.mkdir(home_dir + "/.residuals/")

    cmd = ['{}/.armor/armor-bin {} {} > {}'.format(home_dir, filename_certchain, input_CA_store, filename_armor_output)]
    armor_res = subprocess.getoutput(cmd)
    print(armor_res)
    if armor_res.__contains__("failed") or armor_res.__contains__("error") or armor_res.__contains__("Error") \
            or armor_res.__contains__("exception") or armor_res.__contains__("TLV: cert") \
            or armor_res.__contains__("cannot execute binary file") or armor_res.__contains__("more bytes remain") \
            or armor_res.__contains__("incomplete read"):
        print("ARMOR syntactic or semantic checks: failed")
        os.remove(filename_armor_output)
        return False
    else:
        print("ARMOR syntactic and semantic checks: passed")

    readData(filename_armor_output)
    os.remove(filename_armor_output)

    purpose_verify_res = verifyCertificatePurpose(input_purpose)
    if not purpose_verify_res:
        print("Error: Incorrect certificate purpose")
        return False

    sign_verify_res = verifySignatures()
    if sign_verify_res == "false":
        print("Signature verification: failed")
        return False
    else:
        print("Signature verification: passed")

    return True

if __name__ == "__main__":
    res = main()
    if res:
        print("success")
    else:
        print("failed")
