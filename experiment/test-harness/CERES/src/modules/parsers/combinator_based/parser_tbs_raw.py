from modules.helper import *
from parsec import *


@generate('')
def short_length():
    x = yield regex(r'[0-7][0-9A-F]')
    y = hex_n_bytes_to_int(x)
    return [x], y


@generate('')
def long_length():
    x = yield regex(r'8[1-6]')
    size = int(x) - 80
    y = yield count(any_byte, size)
    z = hex_n_bytes_to_int(y)

    if not (z >= 128):
        raise ParseError("not proper length", "", -1)
    return [x] + y, z


@generate('')
def raw_tbs():
    yield string('30')
    yield length
    t3 = yield string('30')
    t4, size4 = yield length
    t5 = yield count(any_byte, size4)
    out = array_to_bytes([t3] + t4 + t5)
    return out


def run(inp):
    return program.parse(inp)


whitespace = regex(r'\s')
ignore = many(whitespace)

any_byte = regex(r'[0-9A-F][0-9A-F]')
length = short_length | long_length

program = raw_tbs
