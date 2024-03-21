from modules.helper import *
from modules.x509_ds import *
from parsec import *


def add_parsers(x):
    global parsers
    parsers.append(x)


def pop_parsers():
    global parsers
    parsers.pop()


def error():
    global parsers

    if len(parsers) > 0:
        return parsers[len(parsers) - 1]
    else:
        None


@generate('')
def no_parser():
    yield count(any_byte, 0)
    return 0, None


@generate('')
def aki_key_id():
    yield string('80')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, [fields, size]


@generate('')
def aki_cert_issuer():
    yield string('A1')
    s1, size1 = yield length
    rem = size1
    gen_names = ()
    while rem > 0:
        tag = yield regex(r'(A0|81|82|A3|A4|A5|86|87|88)').parsecmap(hex_n_bytes_to_int)
        s2, size2 = yield length
        value = yield count(any_byte, size2).parsecmap(array_to_bytes)
        rem = rem - 1 - s2 - size2
        gen_names = addtotuple(gen_names, GenerelName([tag, value]))
        if size2 <= 0:
            raise ParseError("not proper length", "", -1)

    if rem != 0 or len(gen_names) == 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size1

    return s, AuthorityCertIssuer(gen_names)


@generate('')
def aki_cert_serial():
    yield string('82')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, [fields, size]


@generate('')
def short_length():
    x = yield regex(r'[0-7][0-9A-F]').parsecmap(hex_n_bytes_to_int)
    return 1, x


@generate('')
def long_length():
    x = yield regex(r'8[1-6]')
    size = int(x) - 80
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)

    if not (fields >= 128):
        raise ParseError("not proper length", "", -1)

    return 1 + size, fields


@generate('')
def serial():
    add_parsers('serial')
    yield string('02')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, [fields, size]


@generate('')
def version():
    yield string('A0')
    add_parsers('version')
    s1, size1 = yield length
    yield string('02')
    s2, size2 = yield length
    fields = yield count(any_byte, size2).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + 1 + s2 + size2

    if size1 != 1 + s2 + size2 or size2 <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, [fields, size2]


@generate('')
def intgr_parser():
    yield string('02')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    # if size == 0:
    #     raise ParseError("not proper length", "", -1)

    return s, [fields, size]


@generate('')
def issuer():
    add_parsers('issuer')
    yield string('30')
    s1, size1 = yield length
    rem1 = size1
    out1 = ()
    while rem1 > 0:
        yield string('31')
        s2, size2 = yield length
        rem2 = size2
        out2 = ()
        while rem2 > 0:
            yield string('30')
            s3, size3 = yield length
            rem3 = size3
            out3 = ()
            while rem3 > 0:
                s_1, oid = yield oid_parser
                str_type = yield regex(r'(1[34CE])|(0C)').parsecmap(hex_n_bytes_to_int)
                s_2, size = yield length
                if size == 0:
                    raise ParseError("not proper length", "", -1)
                str_value = yield count(any_byte, size).parsecmap(array_to_bytes)
                s_ = s_1 + 1 + s_2 + size
                rem3 = rem3 - s_
                field = Attribute([oid, String([str_type, str_value])])
                out3 = addtotuple(out3, field)

            if rem3 != 0 or size3 <= 0:
                raise ParseError("not proper length", "", -1)

            rem2 = rem2 - 1 - s3 - size3
            out2 = addtotuple(out2, RDNset(out3))

        if rem2 != 0 or len(out2) == 0:
            raise ParseError("not proper length", "", -1)

        rem1 = rem1 - 1 - s2 - size2
        out1 = addtotuple(out1, out2)

    if rem1 != 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size1
    pop_parsers()
    return s, IssuerDN(out1)


@generate('')
def utc_time():
    yield string('17')
    s1, size = yield length
    if size != 13:
        raise ParseError("not proper length", "", -1)

    year1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    year2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    mon1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    mon2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    day1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    day2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    hour1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    hour2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    min1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    min2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    sec1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    sec2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    char_Z = (yield any_byte.parsecmap(hex_n_bytes_to_int))
    time_ = [year1 * 10 + year2,
             mon1 * 10 + mon2,
             day1 * 10 + day2,
             hour1 * 10 + hour2,
             min1 * 10 + min2,
             sec1 * 10 + sec2,
             23]

    if char_Z == 90 \
            and (0 <= time_[0] <= 99) \
            and (1 <= time_[1] <= 12) \
            and (1 <= time_[2] <= 31) \
            and (0 <= time_[3] <= 23) \
            and (0 <= time_[4] <= 59) \
            and (0 <= time_[5] <= 59):
        s = 1 + s1 + size
        return s, time_
    else:
        raise ParseError("not proper length", "", -1)


@generate('')
def gen_time():
    yield string('18')
    s1, size = yield length
    if size != 15:
        raise ParseError("not proper length", "", -1)

    year1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    year2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    year3 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    year4 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    mon1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    mon2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    day1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    day2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    hour1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    hour2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    min1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    min2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    sec1 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    sec2 = (yield any_byte.parsecmap(hex_n_bytes_to_int)) - 48
    char_Z = (yield any_byte.parsecmap(hex_n_bytes_to_int))
    time_ = [year1 * 1000 + year2 * 100 + year3 * 10 + year4,
             mon1 * 10 + mon2,
             day1 * 10 + day2,
             hour1 * 10 + hour2,
             min1 * 10 + min2,
             sec1 * 10 + sec2,
             24]

    if char_Z == 90 \
            and (0 <= time_[0] <= 9999) \
            and (1 <= time_[1] <= 12) \
            and (1 <= time_[2] <= 31) \
            and (0 <= time_[3] <= 23) \
            and (0 <= time_[4] <= 59) \
            and (0 <= time_[5] <= 59):
        s = 1 + s1 + size
        return s, time_
    else:
        raise ParseError("not proper length", "", -1)


@generate('')
def validity():
    add_parsers('validity')
    yield string('30')
    s1, size = yield length
    s2, notbefore = yield try_choice(utc_time, gen_time)
    s3, notafter = yield try_choice(utc_time, gen_time)
    s = 1 + s1 + s2 + s3

    if size != s2 + s3 or size <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, ValidityPeriod([NotBefore(notbefore), NotAfter(notafter)])


@generate('')
def subject():
    add_parsers('subject')
    yield string('30')
    s1, size1 = yield length
    rem1 = size1
    out1 = ()
    while rem1 > 0:
        yield string('31')
        s2, size2 = yield length
        rem2 = size2
        out2 = ()
        while rem2 > 0:
            yield string('30')
            s3, size3 = yield length
            rem3 = size3
            out3 = ()
            while rem3 > 0:
                s_1, oid = yield oid_parser
                str_type = yield regex(r'(1[34CE])|(0C)').parsecmap(hex_n_bytes_to_int)
                s_2, size = yield length
                if size == 0:
                    raise ParseError("not proper length", "", -1)
                str_value = yield count(any_byte, size).parsecmap(array_to_bytes)
                s_ = s_1 + 1 + s_2 + size
                rem3 = rem3 - s_
                field = Attribute([oid, String([str_type, str_value])])
                out3 = addtotuple(out3, field)

            if rem3 != 0 or size3 <= 0:
                raise ParseError("not proper length", "", -1)

            rem2 = rem2 - 1 - s3 - size3
            out2 = addtotuple(out2, RDNset(out3))

        if rem2 != 0 or len(out2) == 0:
            raise ParseError("not proper length", "", -1)

        rem1 = rem1 - 1 - s2 - size2
        out1 = addtotuple(out1, out2)

    if rem1 != 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size1
    pop_parsers()
    return s, SubjectDN(out1)


@generate('')
def pk_rsa():
    yield string('00')
    yield string('30')
    s1, size = yield length
    s2, n = yield intgr_parser
    s3, e = yield intgr_parser
    if size != s2 + s3 or size <= 0 or n[1] <= 0 or e[1] <= 0:
        raise ParseError("not proper length", "", -1)
    s = 2 + s1 + s2 + s3

    return s, RSAkey([n, e])


@generate('')
def consume_globally():
    global temp
    p = yield count(any_byte, temp).parsecmap(array_to_bytes)

    if len(p) == 0:
        raise ParseError("not proper length", "", -1)
    return temp, p


@generate('')
def public_key():
    global temp
    yield string('03')
    s1, size = yield length
    temp = size
    s2, fields = yield try_choice(pk_rsa, consume_globally)
    if size != s2 or size <= 0:
        raise ParseError("not proper length", "", -1)
    s = 1 + s1 + s2
    return s, fields


@generate('')
def subjectPKI():
    add_parsers('subjectPKI')
    yield string('30')
    s1, size = yield length
    s2, algoid = yield algorithm_identifier_pk
    s3, pub_key = yield public_key
    if size != s2 + s3 or size <= 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + s2 + s3
    pop_parsers()
    return s, SubjectPKI([algoid, pub_key])


@generate('')
def issuerUID():
    yield string('A1')
    add_parsers('issuerUID')
    s1, size = yield length
    fields = yield count(any_byte, size)

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size
    pop_parsers()
    return s, fields


@generate('')
def subjectUID():
    yield string('A2')
    add_parsers('subjectUID')
    s1, size = yield length
    fields = yield count(any_byte, size)

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size
    pop_parsers()
    return s, fields


@generate('')
def oid_parser():
    yield string('06')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, [fields, size]


@generate('')
def bool_parser():
    yield string('01')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    return s, fields


@generate('')
def extn_others():
    add_parsers('extn_others')
    yield string('04')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size
    pop_parsers()
    return s, Unknown_extension(fields)


@generate('')
def auth_key_id():
    add_parsers('auth_key_id')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    s3, key_id = yield try_choice(aki_key_id, no_parser)
    s4, cert_iss = yield try_choice(aki_cert_issuer, no_parser)
    s5, cert_serial = yield try_choice(aki_cert_serial, no_parser)
    s = 1 + s1 + 1 + s2 + s3 + s4 + s5
    if (size1 != 1 + s2 + size2) or (size2 != s3 + s4 + s5) or size1 <= 0 or size2 <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Auth_key_id([key_id, cert_iss, cert_serial])


@generate('')
def sub_key_id():
    add_parsers('sub_key_id')
    yield string('04')
    s1, size1 = yield length
    yield string('04')
    s2, size2 = yield length
    fields = yield count(any_byte, size2).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + 1 + s2 + size2
    if size1 != 1 + s2 + size2 or size2 <= 0 or size1 <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Sub_key_id([fields, size2])


@generate('')
def key_usage():
    add_parsers('key_usage')
    yield string('04')
    s1, size1 = yield length
    yield string('03')
    s2, size2 = yield length
    padding = yield regex(r'0[0-7]').parsecmap(hex_n_bytes_to_int)
    fields = yield count(any_byte, size2 - 1)
    s = 1 + s1 + 1 + s2 + size2

    if (size1 != 1 + s2 + size2) or padding > get_ku_padding_count(fields) or size1 <= 0 or size2 <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Key_usage(map_ku(fields))


@generate('')
def ext_key_usage():
    add_parsers('ext_key_usage')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem = size2
    s3 = 0
    ekus = []
    while rem > 0:
        s_, eku = yield oid_parser
        s3 = s3 + s_
        ekus.append(eku)
        rem = rem - s_

    s = 1 + s1 + 1 + s2 + s3
    if (size1 != 1 + s2 + s3) or size2 != s3 or len(ekus) == 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Ext_key_usage(map_eku(ekus))


@generate('')
def subject_alt_name():
    add_parsers('subject_alt_name')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem = size2
    sans = ()
    while rem > 0:
        tag = yield regex(r'(A0|81|82|A3|A4|A5|86|87|88)').parsecmap(hex_n_bytes_to_int)
        s3, size3 = yield length
        value = yield count(any_byte, size3).parsecmap(array_to_bytes)
        rem = rem - 1 - s3 - size3
        sans = addtotuple(sans, GenerelName([tag, value]))
        if size3 <= 0:
            raise ParseError("not proper length", "", -1)

    if rem != 0 or size1 != 1 + s2 + size2 or len(sans) == 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + 1 + s2 + size2
    pop_parsers()
    return s, Subject_alt_name(sans)


@generate('')
def issuer_alt_name():
    add_parsers('issuer_alt_name')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem = size2
    ians = ()
    while rem > 0:
        tag = yield regex(r'(A0|81|82|A3|A4|A5|86|87|88)').parsecmap(hex_n_bytes_to_int)
        s3, size3 = yield length
        value = yield count(any_byte, size3).parsecmap(array_to_bytes)
        rem = rem - 1 - s3 - size3
        ians = addtotuple(ians, GenerelName([tag, value]))
        if size3 <= 0:
            raise ParseError("not proper length", "", -1)

    if rem != 0 or size1 != 1 + s2 + size2 or len(ians) == 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + 1 + s2 + size2
    pop_parsers()
    return s, Issuer_alt_name(ians)


@generate('')
def basic_constraints():
    add_parsers('basic_constraints')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    s3, ca = yield try_choice(bool_parser, no_parser)
    s4, pathlen = yield try_choice(intgr_parser, no_parser)
    s = 1 + s1 + 1 + s2 + s3 + s4
    if (size1 != 1 + s2 + size2) or (size2 != s3 + s4) or size1 <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Basic_constraints([map_bool(ca), pathlen])


@generate('')
def policy_qualifiers():
    yield string('30')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size
    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, fields


@generate('')
def cert_policies():
    add_parsers('cert_policies')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem2 = size2
    policy_infos = ()
    while rem2 > 0:
        yield string('30')
        s3, size3 = yield length
        rem3 = size3
        s_1, pol_id = yield oid_parser
        rem3 = rem3 - s_1
        if rem3 > 0:
            s_2, pol_qualifiers = yield policy_qualifiers
        else:
            s_2, pol_qualifiers = 0, None
        rem3 = rem3 - s_2
        if rem3 != 0 or size3 <= 0:
            raise ParseError("not proper length", "", -1)

        policy_infos = addtotuple(policy_infos, PolicyInformation([pol_id, pol_qualifiers]))
        rem2 = rem2 - 1 - s3 - size3

    if size1 != 1 + s2 + size2 or rem2 != 0 or len(policy_infos) == 0:
        raise ParseError("not proper length", "", -1)
    s = 1 + s1 + 1 + s2 + size2
    pop_parsers()
    return s, Cert_policies(policy_infos)

@generate('')
def crl_distpoint():
    yield string('A0')
    s1, size = yield length

    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, fields


@generate('')
def crl_reasons():
    yield string('81')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size

    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, fields


@generate('')
def crl_issuer():
    yield string('A2')
    s1, size1 = yield length
    rem = size1
    gen_names = ()
    while rem > 0:
        tag = yield regex(r'(A0|81|82|A3|A4|A5|86|87|88)').parsecmap(hex_n_bytes_to_int)
        s2, size2 = yield length
        value = yield count(any_byte, size2).parsecmap(array_to_bytes)
        rem = rem - 1 - s2 - size2
        gen_names = addtotuple(gen_names, GenerelName([tag, value]))
        if size2 <= 0:
            raise ParseError("not proper length", "", -1)

    if rem != 0 or len(gen_names) == 0:
        raise ParseError("not proper length", "", -1)

    s = 1 + s1 + size1

    return s, CrlIssuer(gen_names)


@generate('')
def crl_dist_points():
    add_parsers('crl_dist_points')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem2 = size2
    dist_points = ()
    while rem2 > 0:
        yield string('30')
        s3, size3 = yield length
        s_1, distpoint = yield try_choice(crl_distpoint, no_parser)
        s_2, reasons = yield try_choice(crl_reasons, no_parser)
        s_3, crlissuer = yield try_choice(crl_issuer, no_parser)
        if s_1 + s_2 + s_3 != size3:
            raise ParseError("not proper length", "", -1)

        dist_points = addtotuple(dist_points, DistributionPoint([distpoint, reasons, crlissuer]))
        rem2 = rem2 - 1 - s3 - size3

    if size1 != 1 + s2 + size2 or rem2 != 0 or len(dist_points) == 0:
        raise ParseError("not proper length", "", -1)
    s = 1 + s1 + 1 + s2 + size2
    pop_parsers()
    return s, CRL_dist_points(dist_points)


@generate('')
def acc_location():
    tag = yield regex(r'(A0|81|82|A3|A4|A5|86|87|88)').parsecmap(hex_n_bytes_to_int)
    s1, size = yield length
    value = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size
    if size <= 0:
        raise ParseError("not proper length", "", -1)

    return s, GenerelName([tag, value])


@generate('')
def authority_info_access():
    add_parsers('authority_info_access')
    yield string('04')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem2 = size2
    acc_descs = ()
    while rem2 > 0:
        yield string('30')
        s3, size3 = yield length
        s_1, a_method = yield oid_parser
        s_2, a_location = yield acc_location
        if s_1 + s_2 != size3:
            raise ParseError("not proper length", "", -1)

        acc_descs = addtotuple(acc_descs, AccessDescription([a_method, a_location]))
        rem2 = rem2 - 1 - s3 - size3

    if size1 != 1 + s2 + size2 or rem2 != 0 or len(acc_descs) == 0:
        raise ParseError("not proper length", "", -1)
    s = 1 + s1 + 1 + s2 + size2
    pop_parsers()
    return s, Authority_info_access(acc_descs)


@generate('')
def extension():
    yield string('30')
    s1, size1 = yield length
    s2, id = yield oid_parser  # extnid
    s3, crit = yield try_choice(bool_parser, no_parser)
    if id[0] == 5578019:
        s4, value = yield auth_key_id
    elif id[0] == 5577998:
        s4, value = yield sub_key_id
    elif id[0] == 5577999:
        s4, value = yield key_usage
    elif id[0] == 5578021:
        s4, value = yield ext_key_usage
    elif id[0] == 5578001:
        s4, value = yield subject_alt_name
    elif id[0] == 5578002:
        s4, value = yield issuer_alt_name
    elif id[0] == 5578003:
        s4, value = yield basic_constraints
    elif id[0] == 5578016:
        s4, value = yield cert_policies
    elif id[0] == 5578015:
        s4, value = yield crl_dist_points
    elif id[0] == 3100166514561974529:
        s4, value = yield authority_info_access
    else:
        s4, value = yield extn_others

    s = 1 + s1 + s2 + s3 + s4
    if size1 != s2 + s3 + s4:
        raise ParseError("not proper length", "", -1)

    return s, Extn([id, map_bool(crit), value])


@generate('')
def extensions():
    yield string('A3')
    add_parsers('extensions')
    s1, size1 = yield length
    yield string('30')
    s2, size2 = yield length
    rem = size2
    s3 = 0
    extns = ()
    while rem > 0:
        q, r = yield extension
        s3 = s3 + q
        extns = addtotuple(extns, r)
        rem = rem - q

    s = 1 + s1 + 1 + s2 + s3
    if (size1 != 1 + s2 + s3) or size2 != s3 or len(extns) == 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, Extns(extns)


@generate('')
def tbs_fields():
    s1, a = yield try_choice(version, no_parser)
    s2, b = yield serial
    add_parsers('signature_algorithm')
    s3, c = yield algorithm_identifier
    pop_parsers()
    s4, d = yield issuer
    s5, e = yield validity
    s6, f = yield subject
    s7, g = yield subjectPKI
    s8, h = yield try_choice(issuerUID, no_parser)
    s9, i = yield try_choice(subjectUID, no_parser)
    s10, j = yield try_choice(extensions, no_parser)
    s = s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10

    return s, [map_version(a), b, SignatureAlgorithm(c), d, e, f, g, h, i, j]


@generate('')
def tbsCertificate():
    add_parsers('tbsCertificate')
    yield string('30')
    s1, size = yield length
    s2, fields = yield tbs_fields
    s = 1 + s1 + s2

    if size != s2 or size <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return s, TbsCertificate(fields)


@generate('')
def parameter():
    tag = yield any_byte.parsecmap(hex_n_bytes_to_int)
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size
    return s, Parameter([tag, fields])


@generate('')
def algorithm_identifier():
    yield string('30')
    s1, size = yield length
    s2, oid = yield oid_parser
    if size - s2 > 0:
        s3, param = yield parameter
    else:
        s3, param = 0, None
    s = 1 + s1 + s2 + s3
    if (size != s2 + s3) or size <= 0:
        raise ParseError("not proper length", "", -1)

    if param != None and not ((param.Type == 5 and param.Value == None and (
            oid[0] == 784439383290839892228 or oid[0] == 784439383290839892229 or oid[0] == 784439383290839892235 or
            oid[0] == 784439383290839892238 or oid[0] == 784439383290839892236 or oid[0] == 784439383290839892237 or
            oid[0] == 784439383290839892234 or oid[0] == 784439383290839892226 or oid[0] == 784439383290839892227)) or (
                                      oid[0] != 784439383290839892228 and oid[0] != 784439383290839892229 and oid[
                                  0] != 784439383290839892235 and oid[0] != 784439383290839892238 and oid[
                                          0] != 784439383290839892236 and
                                      oid[0] != 784439383290839892237 and oid[0] != 784439383290839892234 and oid[
                                          0] != 784439383290839892226 and oid[0] != 784439383290839892227)):
        raise ParseError("not proper RSA signature algorithm", "", -1)

    return s, AlgorithmIdentifier([oid, param])


@generate('')
def algorithm_identifier_pk():
    yield string('30')
    s1, size = yield length
    s2, oid = yield oid_parser
    if size - s2 > 0:
        s3, param = yield parameter
    else:
        s3, param = 0, None
    s = 1 + s1 + s2 + s3
    if (size != s2 + s3) or size <= 0:
        raise ParseError("not proper length", "", -1)

    if not ((param.Type == 5 and param.Value == None and oid[0] == 784439383290839892225) or oid[
        0] != 784439383290839892225):
        raise ParseError("not proper RSA public key algorithm", "", -1)

    return s, AlgorithmIdentifier([oid, param])


@generate('')
def signature():
    add_parsers('signature')
    yield string('03')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)

    if size <= 0:
        raise ParseError("not proper length", "", -1)
    s = 1 + s1 + size
    pop_parsers()
    return s, fields


@generate('')
def cert_fields():
    s1, a = yield tbsCertificate
    add_parsers('signature_algorithm')
    s2, b = yield algorithm_identifier
    pop_parsers()
    s3, c = yield signature
    s = s1 + s2 + s3

    return s, [a, SignatureAlgorithm(b), c]


@generate('')
def certificate():
    add_parsers('certificate')
    yield string('30')
    s1, size = yield length
    s2, fields = yield cert_fields
    s = 1 + s1 + s2

    if size != s2 or size <= 0:
        raise ParseError("not proper length", "", -1)
    pop_parsers()
    return True, s, Certificate(fields)


def run(inp):
    global parsers
    parsers = []
    return program.parse(inp), int(inp, 16)


parsers = []
temp = None
whitespace = regex(r'\s')
ignore = many(whitespace)

any_byte = regex(r'[0-9A-F][0-9A-F]')
length = short_length | long_length

program = certificate
