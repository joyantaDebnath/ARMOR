#!/bin/bash

pip3 install antlr4-python3-runtime==4.9.1 # change if needed
antlr4='java -jar antlr-4.9.1-complete.jar'

rm -rf build/
$antlr4 -Dlanguage=Python3 -o build/ -visitor "dsl_grammar.g4"

in_dsl=$1
python3 generate-code.py $in_dsl

echo "Success : generated parser out.py from input dsl grammar"
