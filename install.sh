#!/bin/bash

set -e

cd src/armor-agda && make all && cd ../..
cd src/armor-driver && ./install.sh && cd ../..

echo "ARMOR Installation: Done"