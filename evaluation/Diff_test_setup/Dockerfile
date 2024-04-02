# Use the official Ubuntu base image
FROM ubuntu:latest

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive

# Update and install necessary packages and libraries
RUN apt-get update && \
    apt-get install -y --no-install-recommends build-essential \
        ca-certificates \
        nettle-dev dash git-core autoconf libtool \
        gettext autopoint automake autogen nettle-dev \
        libp11-kit-dev libtspi-dev libunistring-dev \
        guile-2.2-dev libtasn1-6-dev libidn2-0-dev gawk gperf \
        bison gtk-doc-tools \
        libev-dev \
        libgmp3-dev \
        git \
        cmake \
        autotools-dev \
        autoconf \
        automake \
        libtool \
        pkg-config \
        libasound2 \
        libc6-i386 \
        libc6-x32 \
        libxi6 \
        libxrender1 \
        libxtst6 \
        libfreetype6 \
        python3-pip \
        golang-go \
        wget \
        libtasn1-bin \
        libffi7 \
        sudo \
        python3-dev \
        nano \
        valgrind \
        bc \
        ocaml

RUN pip3 install jsonschema pem jinja2 certvalidator cryptography

COPY test-harness/ /home/test-harness/

WORKDIR /home/test-harness/

## openssl
RUN cd c-openssl/ && \
    git clone https://github.com/openssl/openssl.git openssl && \
    cd openssl/ && \
    mkdir BUILD; ./Configure --prefix=`pwd`/BUILD --openssldir=`pwd`/BUILD linux-generic32 && \
    make && \
    make install_sw && \
    cd .. && \
    gcc -o test_verify test_verify.c -I openssl/BUILD/include openssl/BUILD/lib/libcrypto.a  openssl/BUILD/lib/libssl.a  && \
    cd ..

## gnutls
RUN cd c-gnutls/ && \
    git clone https://github.com/gnutls/gnutls.git gnutls && \
    cd gnutls/ && \
    ./bootstrap && \
    mkdir BUILD && \
    CC=gcc CXX=g++ ./configure --prefix=`pwd`/BUILD --without-p11-kit --disable-doc --with-included-libtasn1 && \
    make -j9 && \
    make install && \
    cd .. && \
    gcc -o test_verify test_verify.c -I gnutls/BUILD/include -L gnutls/BUILD/lib -lgnutls && \
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-gnutls/gnutls/BUILD/lib && \
    cd ..

## wolfssl
RUN cd c-wolfssl/ && \
    git clone https://github.com/wolfssl/wolfssl.git wolfssl && \
    cd wolfssl && \
    ./autogen.sh && \
    mkdir BUILD && \
    ./configure --prefix=`pwd`/BUILD && \
    make && \
    make install && \
    cd .. && \
    # gcc test_verify.c -o test_verify -I wolfssl/BUILD/include wolfssl/BUILD/lib/libwolfssl.la -lm && \
    gcc test_verify.c -o test_verify -I wolfssl/BUILD/include  -L wolfssl/BUILD/lib -lwolfssl && \
    cd ..

## boringssl
RUN cd c-boringssl/ && \
    git clone https://boringssl.googlesource.com/boringssl boringssl && \
    cd boringssl && \
    mkdir BUILD && \
    cd BUILD && \
    cmake .. && \
    cmake --build . && \
    cmake --install . && \
    cd ../.. && \
    gcc -o test_verify test_verify.c -I boringssl/install/include boringssl/install/lib/libcrypto.a  boringssl/install/lib/libssl.a && \
    cd ..

## mbedtls
RUN cd c-mbedtls/ && \
    git clone https://github.com/Mbed-TLS/mbedtls.git mbedtls && \
    cd mbedtls/ && \
    git submodule update --init && \
    mkdir BUILD && \
    make && \
    make DESTDIR=BUILD install && \
    cd .. && \
    gcc test_verify.c -o test_verify -I mbedtls/BUILD/include  -L mbedtls/BUILD/lib -lmbedtls -lmbedx509 -lmbedcrypto && \
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-mbedtls/mbedtls/BUILD/lib && \
    cd ..

## matrixssl
RUN cd c-matrix/ && \
     tar -xf matrixssl.tar.xz && \
     cd matrixssl/ && \
     make && \
     cd .. && \
     gcc -o test_verify test_verify.c -I matrixssl/matrixssl -I matrixssl/crypto -I matrixssl/core/include -I matrixssl/core/config -I matrixssl/core/osdep/include matrixssl/matrixssl/libssl_s.a matrixssl/crypto/libcrypt_s.a matrixssl/core/libcore_s.a && \
     cd ..

# Download and Copy the Oracle JDK Debian package into the container
RUN wget -O jdk-20.deb "https://stonybrook365-my.sharepoint.com/:u:/g/personal/joyanta_debnath_stonybrook_edu/EZcP3EKIZixNoNIwqUx82JcB8dvEfNXB5WCTC8mZFafLig?e=02QM6M&download=1"
RUN cp jdk-20.deb /tmp

# Install the Oracle JDK
RUN dpkg -i /tmp/jdk-20.deb && \
    apt-get install -f

# Set the JAVA_HOME environment variable (replace the path with the correct one for your JDK)
ENV JAVA_HOME=/usr/lib/jvm/jdk-20
RUN echo 'export JAVA_HOME=/usr/lib/jvm/jdk-20' >> ~/.bashrc && \
    echo 'export PATH=$JAVA_HOME/bin:$PATH' >> ~/.bashrc

ENV JAVA_HOME /usr/lib/jvm/jdk-20
ENV PATH $JAVA_HOME/bin:$PATH

RUN git clone https://github.com/joyantaDebnath/CERES.git
COPY armor-driver/ /home/test-harness/armor-driver/


RUN cd /usr/lib/go/src && \
    go get github.com/grantae/certinfo

## go-crypto

## bouncy
RUN cd java-BouncyCastle && \
    make && \
    cd .. 

## sun
RUN cd java-SUN && \
    make && \
    cd ..

## certvalidator

## aeres
RUN cd /home/test-harness/armor-driver/ && \
    ./install.sh

## ceres
RUN cd /home/test-harness/CERES/ && \
    ./build-ceres.sh

RUN git clone https://github.com/wolfcw/libfaketime.git libfaketime
RUN cd libfaketime && make install && cd ..

# Clean up
RUN rm -rf /tmp/jdk-20.deb && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

## copy data to docker image
COPY Data/ /home/Data/
COPY sample_root_ca_store.pem /home/test-harness/sample_root_ca_store.pem

RUN mkdir /home/docker_results/

WORKDIR /home/test-harness/

# Set the entrypoint
CMD ["/bin/bash"]
