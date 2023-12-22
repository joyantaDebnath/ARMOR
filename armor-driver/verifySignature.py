from helpers import *
from pathlib import Path
from hashlib import *

import subprocess

## with morpheous formally verified oracle
def verifySign(signature, sign_algo, msg, pk, i):
    if sign_algo in sign_oid_map_insecure:
        print("Singnature algorithm {} is insecure in certificate {}".format(sign_oid_map_insecure[sign_algo], i))
        return "false"

    home_dir = str(Path.home())
    morpheous_loc = home_dir + "/.armor/morpheus-bin"
    #hacl_loc = home_dir + "/.armor/hash-hacl-star-bin"

    if sign_algo in sign_oid_map:
        if sign_oid_map[sign_algo] == "sha256WithRSAEncryption":
            try:
                signature_mod = pow(int.from_bytes(signature, byteorder='big'), pk.public_numbers().e, pk.public_numbers().n)
                signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
                print(signature_mod)
                print(signature_mod_hex)
                #cmd2 = ['{} {} {}'.format(hacl_loc, msg.hex(), 'sha256')]
                #tbs_hash = subprocess.getoutput(cmd2)
                tbs_hash = sha256(msg).hexdigest()
                print(tbs_hash)
                n_length = pk.public_numbers().n.bit_length() // 8
                print(n_length)
                hash_size = 256
                cmd = ['{} {} {} {} {}'.format(morpheous_loc, signature_mod_hex, n_length, tbs_hash, hash_size)]
                morpheous_res = subprocess.getoutput(cmd)
                print(morpheous_res, hash_size)
                return morpheous_res
            except:
                return "false"
        elif sign_oid_map[sign_algo] == "sha384WithRSAEncryption":
            try:
                signature_mod = pow(int.from_bytes(signature, byteorder='big'), pk.public_numbers().e, pk.public_numbers().n)
                signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
                #cmd2 = ['{} {} {}'.format(hacl_loc, msg.hex(), 'sha384')]
                #tbs_hash = subprocess.getoutput(cmd2)
                tbs_hash = sha384(msg).hexdigest()
                n_length = pk.public_numbers().n.bit_length() // 8
                hash_size = 384
                cmd = ['{} {} {} {} {}'.format(morpheous_loc, signature_mod_hex, n_length, tbs_hash, hash_size)]
                morpheous_res = subprocess.getoutput(cmd)
                print(morpheous_res, hash_size)
                return morpheous_res
            except:
                return "false"
        elif sign_oid_map[sign_algo] == "sha512WithRSAEncryption":
            try:
                signature_mod = pow(int.from_bytes(signature, byteorder='big'), pk.public_numbers().e, pk.public_numbers().n)
                signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
                #cmd2 = ['{} {} {}'.format(hacl_loc, msg.hex(), 'sha512')]
                #tbs_hash = subprocess.getoutput(cmd2)
                tbs_hash = sha512(msg).hexdigest()
                n_length = pk.public_numbers().n.bit_length() // 8
                hash_size = 512
                cmd = ['{} {} {} {} {}'.format(morpheous_loc, signature_mod_hex, n_length, tbs_hash, hash_size)]
                morpheous_res = subprocess.getoutput(cmd)
                print(morpheous_res, hash_size)
                return morpheous_res
            except:
                return "false"
        elif sign_oid_map[sign_algo] == "sha224WithRSAEncryption":
            try:
                signature_mod = pow(int.from_bytes(signature, byteorder='big'), pk.public_numbers().e, pk.public_numbers().n)
                signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
                #cmd2 = ['{} {} {}'.format(hacl_loc, msg.hex(), 'sha224')]
                #tbs_hash = subprocess.getoutput(cmd2)
                tbs_hash = sha224(msg).hexdigest()
                n_length = pk.public_numbers().n.bit_length() // 8
                hash_size = 224
                cmd = ['{} {} {} {} {}'.format(morpheous_loc, signature_mod_hex, n_length, tbs_hash, hash_size)]
                morpheous_res = subprocess.getoutput(cmd)
                print(morpheous_res, hash_size)
                return morpheous_res
            except:
                return "false"
        elif sign_oid_map[sign_algo] == "sha1WithRSAEncryption":
            try:
                signature_mod = pow(int.from_bytes(signature, byteorder='big'), pk.public_numbers().e, pk.public_numbers().n)
                signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
                #cmd2 = ['{} {} {}'.format(hacl_loc, msg.hex(), 'sha1')]
                #tbs_hash = subprocess.getoutput(cmd2)
                tbs_hash = sha1(msg).hexdigest()
                n_length = pk.public_numbers().n.bit_length() // 8
                hash_size = 1
                cmd = ['{} {} {} {} {}'.format(morpheous_loc, signature_mod_hex, n_length, tbs_hash, hash_size)]
                morpheous_res = subprocess.getoutput(cmd)
                print(morpheous_res, hash_size)
                return morpheous_res
            except:
                return "false"
    else:
        print("Singnature algorithm {} is not supported - verification bypassed in certificate {}".format(int_to_hex(sign_algo).upper(), i))
        return "true"

def verifySignatures():
    res = "true"
    for i in range(0, len(signatures) - 1):
        res = verifySign(signatures[i], sign_oids[i], tbs_bytes[i], pks[i + 1], i)

        if res == "false":
            print("Failed to verify signature of certificate {}".format(i))
            break
    return res
