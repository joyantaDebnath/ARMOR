from antlr4 import *

from build.dsl_grammarLexer import dsl_grammarLexer
from customVisitor import *

import sys

inputfile = sys.argv[1]
outputfile = 'out.py'


def main():
    lexer = dsl_grammarLexer(FileStream(inputfile))
    stream = CommonTokenStream(lexer)
    parser = dsl_grammarParser(stream)

    try:
        visitor = customVisitor(outputfile)
        tree = parser.start()
        visitor.visit(tree)
    except:
        raise


if __name__ == '__main__':
    main()
    
