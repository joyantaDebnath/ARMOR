#!/bin/bash

call_libs(){
    echo $1

    ## now call mbedtls library for validation
    touch outputs/mbedtls/$1.txt
    res1=$(build/mbedtls-2.25.0/programs/x509/cert_app mode=file filename=$input_dir/$1 ca_file="/etc/ssl/certs/ca-certificates.crt" 2>&1)
    echo "$res1" > outputs/mbedtls/$1.txt
    
    ## now call gnutls library for validation
    touch outputs/gnutls/$1.txt
    res2=$(build/gnutls-3.6.15/src/certtool --verify --verify-profile high --infile=$input_dir/$1 --load-ca-certificate=/etc/ssl/certs/ca-certificates.crt 2>&1)
    echo "$res2" > outputs/gnutls/$1.txt

    ## now call openssl library for validation
    touch outputs/openssl/$1.txt
    res3=$(build/openssl-1.1.1i/BUILD/bin/openssl verify -verbose -x509_strict -verify_name ssl_server -trusted /etc/ssl/certs/ca-certificates.crt -untrusted $input_dir/$1 $input_dir/$1 2>&1)
    echo "$res3" > outputs/openssl/$1.txt
    
    # # # now call CERES library for validation
    touch outputs/CERES/$1.txt
    res4=$(../../src/bin/ceres --input $input_dir/$1 2>&1)
    echo "$res4" >> outputs/CERES/$1.txt

    touch outputs/CERES_dsl/$1.txt
    res5=$(../../src/bin/ceres --input $input_dir/$1 --dsl-parser 2>&1)
    echo "$res5" >> outputs/CERES_dsl/$1.txt

    # merge results
    res1lastlinetag=$( tail -n 1 outputs/mbedtls/$1.txt )
    if [[ $res1lastlinetag == *"!"* ]]; then
        res1lastlinetagf="Rejected"
    elif [[ $res1lastlinetag == *"ok"* ]]; then
        res1lastlinetagf="Accepted"
    fi
    res2lastlinetag=$( tail -n 1 outputs/gnutls/$1.txt)
    if [[ $res2lastlinetag == *"Not verified"* ]]; then
        res2lastlinetagf="Rejected"
    elif [[ $res2lastlinetag == *"Verified"* ]]; then
        res2lastlinetagf="Accepted"
    else
        res2lastlinetagf="Rejected"
    fi
    res3lastlinetag=$( head -n 2 outputs/openssl/$1.txt)
    if [[ $res3lastlinetag == *"error"* ]]; then
        res3lastlinetagf="Rejected"
        res3lastlinetag=$(head -n 2 outputs/openssl/$1.txt | tail -n 1)
    elif [[ $res3lastlinetag == *"OK"* ]]; then
        res3lastlinetagf="Accepted"
    fi
    res4lastlinetag=$( tail -n 1 outputs/CERES/$1.txt)
    if [[ $res4lastlinetag == *"Couldn't"* ]]; then
        res4lastlinetagf="Rejected"
    elif [[ $res4lastlinetag == *"UNSAT"* ]]; then
        res4lastlinetagf="Rejected"
    elif [[ $res4lastlinetag == *"error"* ]]; then
        res4lastlinetagf="Rejected"
    elif [[ $res4lastlinetag == *"OK"* ]]; then
        res4lastlinetagf="Accepted"
    fi

    res5lastlinetag=$( tail -n 1 outputs/CERES_dsl/$1.txt)
    if [[ $res5lastlinetag == *"Couldn't"* ]]; then
        res5lastlinetagf="Rejected"
    elif [[ $res5lastlinetag == *"UNSAT"* ]]; then
        res5lastlinetagf="Rejected"
    elif [[ $res5lastlinetag == *"error"* ]]; then
        res5lastlinetagf="Rejected"
    elif [[ $res5lastlinetag == *"OK"* ]]; then
        res5lastlinetagf="Accepted"
    fi
    
    res1lastlinetag="${res1lastlinetag//','/' and '}"
    res2lastlinetag="${res2lastlinetag//','/' and '}"
    res3lastlinetag="${res3lastlinetag//','/' and '}"
    res4lastlinetag="${res4lastlinetag//','/' and '}"
    res5lastlinetag="${res5lastlinetag//','/' and '}"
    echo "$1, $res1lastlinetagf, $res1lastlinetag, $res2lastlinetagf, $res2lastlinetag, $res3lastlinetagf, $res3lastlinetag, $res4lastlinetagf, $res4lastlinetag, $res5lastlinetagf, $res5lastlinetag" >> outputs/result.csv
}

## main program
cur=$(pwd)
OPENSSL_LIB_DIR="$cur/build/openssl-1.1.1i/BUILD/lib"
export LD_LIBRARY_PATH=$OPENSSL_LIB_DIR

rm -rf outputs/
mkdir outputs
mkdir outputs/gnutls
mkdir outputs/mbedtls
mkdir outputs/openssl
mkdir outputs/CERES
mkdir outputs/CERES_dsl
touch outputs/result.csv
echo 'Filename, Mbedtls, Reasons, Gnutls, Reasons, Openssl, Reasons, CERES, Reasons, CERES_dsl, Reasons' > outputs/result.csv

c=0
input_dir=$1
for file in $input_dir/*
do
    c=$((c + 1))    
    call_libs $(basename $file)
done
