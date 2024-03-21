from modules.helper import *
from modules.x509_ds import *
from parsec import *


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
        raise ParseError("not proper length in RSA_Signature", "", -1)

    return 1 + size, fields


@generate('')
def parameter():
    tag = yield any_byte.parsecmap(hex_n_bytes_to_int)
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(array_to_bytes)
    s = 1 + s1 + size

    if not (tag == 5 and size == 0):
        raise ParseError("not proper parameter in RSA_Signature", "", -1)

    return s, Parameter([tag, fields])


@generate('')
def oid_parser():
    yield string('06')
    s1, size = yield length
    fields = yield count(any_byte, size).parsecmap(hex_n_bytes_to_int)
    s = 1 + s1 + size

    return s, [fields, size]


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
    if (size != s2 + s3):
        raise ParseError("not proper length in RSA_Signature", "", -1)
    return s, AlgorithmIdentifier([oid, param])


@generate('')
def rsa_signature():
    yield string('00')
    yield string('01')
    padding = yield regex(r'(FF)*')  # at least 8
    if (len(padding) / 2) < 8:
        raise ParseError("not proper padding in RSA_Signature", "", -1)

    yield string('00')
    yield string('30')
    s1, size1 = yield length
    s2, algo_ident = yield algorithm_identifier
    yield string('04')
    s3, size3 = yield length
    digest = yield count(any_byte, size3).parsecmap(array_to_bytes)
    s = 1 + 1 + len(padding) / 2 + 1 + 1 + s1 + s2 + 1 + s3 + size3

    if size1 != s2 + 1 + s3 + size3:
        raise ParseError("not proper length in RSA_Signature", "", -1)
    return s, [algo_ident, digest]


def run(inp):
    x = program.parse(inp)
    if x[0] != len(inp) / 2:
        raise ParseError("not proper length in RSA_Signature", "", -1)
    return x[1]


whitespace = regex(r'\s')
ignore = many(whitespace)

any_byte = regex(r'[0-9A-F][0-9A-F]')
length = short_length | long_length

program = rsa_signature
