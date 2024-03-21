#!/bin/bash -e

cur=$(pwd)
./cleanup.sh

ca_store=${1:-"/etc/ssl/certs/ca-certificates.crt"}
echo "CA certificate store: $ca_store"

mkdir ~/.ceres/

## install pre-requisite packages
sudo apt-get update
sudo apt-get -y install python3 python3-pip ghc libghc-regex-compat-dev libghc-text-icu-dev
pip3 install parsec
pip3 install pyinstaller
pip3 install pysmt

python3 src/build-ca-store.py $ca_store

tar -xzf src/extras.tar.gz -C ~/.ceres/
cd ~/.ceres/extras/stringprep
./build.sh
cd $cur

cd src/
python3 -m PyInstaller driver.py --onefile --name=ceres --distpath bin
cd ..

echo "Success : executable is located at CERES/src/bin/"
