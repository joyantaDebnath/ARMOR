import os
from itertools import groupby

from modules.parsers.combinator_based import parser_tbs_raw
from modules.parsers.combinator_based import parser_x509

ski_index_map = {}
mapped_ca_store_path = str(os.getcwd()) + "/" + "compiled-ca-store/"


def set_more_info(cert_list):
    for k in range(0, len(cert_list)):
        aki = None
        ski = None
        cert_exs = cert_list[k].TbsCertificate.Extensions
        if cert_exs is not None:
            for ex in cert_exs.List:
                if ex.ExtnId[0] == 5578019:
                    aki = ex.ExtnValue.KeyId[0]
                elif ex.ExtnId[0] == 5577998:
                    ski = ex.ExtnValue.KeyId[0]
        cert_list[k].ski = ski
        cert_list[k].aki = aki
    return cert_list


def add_trusted_ca(last_index, res):
    ca_list = get_trusted_ca(res[last_index].aki)
    if len(ca_list) == 0:
        return res + ['end']
    res_ca = []
    for q in ca_list:
        res_ca.extend(res + [q] + ['end'])
    return res_ca


def helper(start_aki, res, input_no_dup):
    i_list = ski_index_map.get(start_aki)
    if i_list is None or len(i_list) == 0:
        last_index = len(res) - 1
        if (res[last_index].ski == res[last_index].aki) or (
                res[last_index].ski is not None and res[last_index].aki is None):
            res.append('end')
            return res
        else:
            return add_trusted_ca(last_index, res)

    res_list = []
    res_temp = []
    start_aki_temp = []
    for i in i_list:
        if input_no_dup[i].ski == input_no_dup[i].aki:
            res.append(input_no_dup[i])
        else:
            res_temp.append(input_no_dup[i])
            start_aki_temp.append(input_no_dup[i].aki)

    if len(res_temp) > 0:
        for k in range(0, len(res_temp)):
            p = helper(start_aki_temp[k], res + [res_temp[k]], input_no_dup)
            res_list.extend(p)
    else:
        del ski_index_map[start_aki]
        p = helper(start_aki, res, input_no_dup)
        res_list.extend(p)
    return res_list


def reorder(input):
    if len(input) == 0:
        return input
    input_no_dup = []
    temp = []
    for cert in input:
        if (cert.RawCert, cert.RawCert_size) not in temp:
            temp.append((cert.RawCert, cert.RawCert_size))
            input_no_dup.append(cert)

    keys = range(1, len(input_no_dup))
    for i in keys:
        if input_no_dup[i].ski not in ski_index_map:
            ski_index_map[input_no_dup[i].ski] = [i]
        else:
            ski_index_map[input_no_dup[i].ski].append(i)

    # case 1: leaf ski is None, aki is None => cannot build, so return whatever we have
    if input_no_dup[0].ski is None and input_no_dup[0].aki is None:
        return [input_no_dup]
    # case 2: leaf ski is not None, aki is None => possible self-signed cert, so return the first cert only
    elif input_no_dup[0].ski is not None and input_no_dup[0].aki is None:
        return [input_no_dup]
    # case 3: leaf ski == aki is not None => possible self-signed cert, so return the first cert only
    elif input_no_dup[0].ski == input_no_dup[0].aki:
        return [input_no_dup]
    else:  # (leaf ski is None and aki is not None) or leaf ski != aki
        if len(input_no_dup) == 1:  # needs to find root CA, append, then return
            res_list = add_trusted_ca(0, input_no_dup)
            zz = [list(group) for k, group in groupby(res_list, lambda x: x == 'end') if not k]
            return zz
        else:  # look for next certs, each cert has ski != aki or ski == aki, terminates if nowhere to go
            start_aki = input_no_dup[0].aki
            res = [input_no_dup[0]]
            res_list = helper(start_aki, res, input_no_dup)
            zz = [list(group) for k, group in groupby(res_list, lambda x: x == 'end') if not k]
            zz.append(input_no_dup)
            return zz


def get_trusted_ca(given_aki):
    ret_list = []
    ski_fld = mapped_ca_store_path + str(given_aki) + '/'
    if os.path.exists(ski_fld):
        entries = os.scandir(ski_fld)
        for entry in entries:
            f = open(ski_fld + entry.name, "r")
            cert_hex = f.read()
            try:
                (flag, size, parsedCert), rawCert = parser_x509.run(cert_hex)
                assert flag and size == len(cert_hex) / 2
                parsedCert.RawCert = rawCert
                parsedCert.RawCert_size = len(cert_hex)
                parsedCert.TbsCertificate.RawTbs = parser_tbs_raw.run(cert_hex)
                ret_list.append(parsedCert)
            except:
                pass
                continue
    return ret_list
