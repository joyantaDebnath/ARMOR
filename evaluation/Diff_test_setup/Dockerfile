# Use the official Ubuntu base image
FROM ubuntu:latest

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive

# Update and install necessary packages and libraries
RUN apt-get update && \
    apt-get install -y --no-install-recommends software-properties-common && \
    add-apt-repository -y ppa:deadsnakes/ppa && \
    apt-get update && \
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
        libasound2t64 \
        libc6-i386 \
        libc6-x32 \
        libxi6 \
        libxrender1 \
        libxtst6 \
        libfreetype6 \
        golang-go \
        wget \
        libtasn1-bin \
        libffi-dev \
        sudo \
        python3 \
        python3-pip \
        nano \
        valgrind \
        bc \
        ocaml

RUN python3 -m pip install jsonschema pem jinja2 oscrypto certvalidator cryptography --break-system-packages

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

# armor crl-revocation
# RUN ./armor-setup.sh

RUN git clone https://github.com/wolfcw/libfaketime.git libfaketime
RUN cd libfaketime && make install && cd ..

# Clean up
RUN rm -rf /tmp/jdk-20.deb && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

## copy data to docker image
COPY test_data/ /home/test_data/
COPY ca-certificates.crt /home/test-harness/ca-certificates.crt

RUN mkdir /home/docker_results/

WORKDIR /home/test-harness/

# Set the entrypoint
CMD ["/bin/bash"]
