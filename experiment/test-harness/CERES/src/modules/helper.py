def hex_n_bytes_to_int(x):
    if x == []:
        return None
    elif type(x) == list and len(x) > 0:
        temp = []
        for i in x:
            temp.append(int(i, 16))
        q = ''.join(format(x, '02X') for x in bytes(temp))
        return int(q, 16)
    else:
        return int(x, 16)


def array_to_bytes(x):
    if x == []:
        return None
    temp = []
    for k in x:
        temp.append(int(k, 16))
    return bytes(temp)


def get_ku_padding_count(elem):
    if elem == []:
        return 0
    temp = int(elem[len(elem) - 1], 16)
    bin_temp = "{0:08b}".format(temp)
    padding = len(bin_temp) - len(bin_temp.rstrip('0'))
    return padding


def map_version(x):
    if type(x) == list and len(x) == 1:  # DSL
        x = x[0]
    if x is None:
        return [0, 0]
    return x


def map_bool(x):
    if type(x) == list and len(x) == 1:  # DSL
        x = x[0]
    return bool(x)  # bool(None) == False


def map_ku(x):
    temp = ""
    for k in x:
        if type(k) == bytes:
            k = k.hex()
        temp = temp + "{0:08b}".format(int(k, 16))
    kus = []
    for j in range(0, len(temp)):
        if j == 0 and temp[j] == '1':
            kus.append('digitalSignature')
        elif j == 1 and temp[j] == '1':
            kus.append('nonRepudiation/contentCommitment')
        elif j == 2 and temp[j] == '1':
            kus.append('keyEncipherment')
        elif j == 3 and temp[j] == '1':
            kus.append('dataEncipherment')
        elif j == 4 and temp[j] == '1':
            kus.append('keyAgreement')
        elif j == 5 and temp[j] == '1':
            kus.append('keyCertSign')
        elif j == 6 and temp[j] == '1':
            kus.append('cRLSign')
        elif j == 7 and temp[j] == '1':
            kus.append('encipherOnly')
        elif j == 8 and temp[j] == '1':
            kus.append('decipherOnly')
    return kus


def map_eku(x):
    if len(x) == 1 and type(x[0]) == tuple:  # DSL
        x = x[0]
    temp = []
    for oid in x:
        if oid[0] == 3100166514561975041:
            temp.append('serverAuth')
        elif oid[0] == 3100166514561975042:
            temp.append('clientAuth')
        elif oid[0] == 3100166514561975043:
            temp.append('codeSigning')
        elif oid[0] == 3100166514561975044:
            temp.append('emailProtection')
        elif oid[0] == 3100166514561986563:
            temp.append('timeStamping')
        elif oid[0] == 3100166514561975049:
            temp.append('OCSPSigning')
        else:
            temp.append(oid[0])
    return temp


def addtotuple(a, b):
    if b is None and a is not None:
        return a
    elif a is None and b is not None:
        return b
    elif type(a) == tuple and type(b) == tuple:
        return a + b
    elif type(a) == tuple and type(b) != tuple:
        return a + (b,)
    elif type(a) != tuple and type(b) == tuple:
        return (a,) + b
    else:
        return (a, b)


def Timedecoder(Value):
    return Value.Year, Value.Month, Value.Day, Value.Hour, Value.Minute, Value.Second


### for dsl_based_parsers
cert = []
cur_index = -1


def initialize(certin):
    global cert, cur_index
    cert = certin
    cur_index = 0


def match(p, flag, i):
    global cert, cur_index
    if flag:
        if i < len(cert) and str(cert[i]) == p:
            i = i + 1
            cur_index = i
            return True, 1, None, i
        else:
            return False, 0, None, i
    else:
        if i >= len(cert) or str(cert[i]) != p:
            return True, 0, None, i
        else:
            return False, 0, None, i


def get_ku_padding_count_dsl(y):
    elem = y[0]
    if elem == None:
        return 0
    elif type(elem) == tuple:
        x = int(elem[len(elem) - 1])
    else:
        x = int(elem)
    lastkuval = "{0:08b}".format(x)
    padding = len(lastkuval) - len(lastkuval.rstrip('0'))
    return padding


def splituple(y):
    x = y[0]
    if x == None:
        return x
    p = list()
    p = Func_split(x, p)
    return tuple(p)


def Func_split(data, temp):
    if data[1] == None:
        temp.append(data[0])
        return temp
    elif type(data[1]) != tuple:
        temp.append(data)
        return temp

    temp.append(data[0])
    return Func_split(data[1], temp)


def hex_n_bytes_to_int_dsl(y):
    x = y[0]
    if x == None:
        return None
    elif type(x) == tuple:
        temp = []
        for i in x:
            temp.append(int(i))
        q = ''.join(format(x, '02X') for x in bytes(temp))
        return int(q, 16)
    else:
        return int(x)


def array_to_bytes_dsl(y):
    x = y[0]
    if x == None:
        return None
    elif (type(x) == tuple):
        temp = []
        for k in x:
            temp.append(int(k))
        return bytes(temp)
    else:
        return bytes([int(x)])


def endcheck(y):
    op = y[0]
    global cur_index
    if op == 1:
        return cur_index < len(cert)
    elif op == 2:
        return cur_index == len(cert)
    elif op == 3:
        return cur_index <= len(cert)
    return False


def getintvalue(x):
    if len(x) == 1:
        if len(x[0]) == 2:
            return x[0][0]
    return None


def addtotuple_dsl(x):
    a, b = x[0], x[1]
    if b is None and a is not None:
        return a
    elif a is None and b is not None:
        return b
    elif type(a) == tuple and type(b) == tuple:
        return a + b
    elif type(a) == tuple and type(b) != tuple:
        return a + (b,)
    elif type(a) != tuple and type(b) == tuple:
        return (a,) + b
    else:
        return (a, b)


def checkKnownExtId(id):
    if id == 5578019:
        return True, 'auth_key_id'
    elif id == 5577998:
        return True, 'sub_key_id'
    elif id == 5577999:
        return True, 'key_usage'
    elif id == 5578021:
        return True, 'ext_key_usage'
    elif id == 5578001:
        return True, 'subject_alt_name'
    elif id == 5578002:
        return True, 'issuer_alt_name'
    elif id == 5578003:
        return True, 'basic_constraints'
    elif id == 5578016:
        return True, 'cert_policies'
    elif id == 5578015:
        return True, 'crl_dist_points'
    elif id == 3100166514561974529:
        return True, 'authority_info_access'
    else:
        return False, None
