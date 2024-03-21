import base64
import os
import shutil
import sys
import time

from modules.parsers.combinator_based import parser_x509

home = os.path.expanduser('~')
out = "{}/.ceres/compiled-ca-store".format(home)


def split_ca_store(path):
    cert_list_decoded = []

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
                except:
                    pass
                    continue

    return cert_list_decoded


def build_ca_store(path):
    cert_list = split_ca_store(path)

    for k in range(0, len(cert_list)):
        try:
            (flag, size, parsedCert), rawCert = parser_x509.run(cert_list[k])
            for ex in parsedCert.TbsCertificate.Extensions.List:
                if ex.ExtnId[0] == 5577998:
                    ski = ex.ExtnValue.KeyId[0]
                    sub_fld = str('{}/'.format(out) + str(ski))
                    if not os.path.exists(sub_fld):
                        os.mkdir(sub_fld)
                    f = open("{}/{}.der".format(sub_fld, time.time()), "w")
                    f.write(cert_list[k])
                    f.close()
        except:
            pass
            continue


try:
    shutil.rmtree(out, ignore_errors=True)
    os.mkdir(out)

    build_ca_store(sys.argv[1])
except:
    raise
    print("Failed to create ~/.ceres/compiled-ca-store")
    shutil.rmtree(out, ignore_errors=True)
