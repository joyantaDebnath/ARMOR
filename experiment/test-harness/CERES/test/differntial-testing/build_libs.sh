#!/bin/bash

rm -rf build/
mkdir build/

cd libs/
tar -xf gnutls* -C ../build/
tar -xzf openssl* -C ../build/
tar -xzf mbedtls* -C ../build/

## install mbedtls
cd ../build/mbedtls-2.25.0/
make
cd ..

## install openssl
cd openssl-1.1.1i
mkdir BUILD; ./Configure --prefix=`pwd`/BUILD --openssldir=`pwd`/BUILD linux-generic32
make
make install_sw
cd ..
cur_dir=$(pwd)
OPENSSL_LIB_DIR="$cur_dir/openssl-1.1.1i/BUILD/lib"
export LD_LIBRARY_PATH=$OPENSSL_LIB_DIR
./openssl-1.1.1i/BUILD/bin/openssl version

## install gnutls
sudo apt-get update -y
sudo apt-get install -y nettle-dev
sudo apt-get install -y dash git-core autoconf libtool gettext autopoint
sudo apt-get install -y automake autogen nettle-dev libp11-kit-dev libtspi-dev libunistring-dev
sudo apt-get install -y guile-2.2-dev libtasn1-6-dev libidn2-0-dev gawk gperf
sudo apt-get install -y libunbound-dev dns-root-data bison gtk-doc-tools
sudo apt-get install -y texinfo texlive texlive-generic-recommended texlive-extra-utils
sudo apt-get install -y v libubsan0 libasan1
sudo apt-get install -y valgrind nodejs softhsm2 datefudge lcov libssl-dev libcmocka-dev expect libev-dev
sudo apt-get install -y dieharder openssl abigail-tools socat net-tools ppp lockfile-progs util-linux
sudo apt-get install -y libgmp3-dev


cd gnutls-3.6.15/
./configure
make
cd ../..
