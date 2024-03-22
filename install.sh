#!/bin/bash

set -e
git submodule update --init --remote

cd src/armor-agda && ./compile.sh && cd ../..
mv src/armor-agda/src/Main src/armor-driver/armor-bin
cd src/armor-driver && ./install.sh && cd ../..

echo "ARMOR Installation: Done"
