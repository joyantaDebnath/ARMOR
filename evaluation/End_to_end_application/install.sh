#!/bin/bash

cd modified_boringssl && \
    mkdir -p BUILD && \
    cd BUILD && \
    cmake -DCMAKE_POSITION_INDEPENDENT_CODE=on .. && \
    cmake --build . && \
    cmake --install . && \
    cd ..
ssl_dir=`pwd`

mkdir -p lib
cd lib
ln -s ../BUILD/ssl/libssl.a
ln -s ../BUILD/crypto/libcrypto.a
cd ../../

git clone https://github.com/curl/curl.git
cd curl
mkdir -p BUILD
./buildconf
autoreconf -fi
LIBS=-lpthread ./configure --prefix=`pwd`/BUILD --with-ssl=$ssl_dir
make clean
make
make install
cd ..

./curl/BUILD/bin/curl --version
