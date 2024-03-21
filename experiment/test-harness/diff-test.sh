#!/bin/bash

export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-wolfssl/wolfssl/BUILD/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-gnutls/gnutls/BUILD/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-mbedtls/mbedtls/BUILD/lib

call_libs(){
    echo $2

    new_time=$(date "+%Y-%m-%d %H:%M:%S")
    echo $new_time

    ## boringssl
    res1=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-boringssl/test_verify $1 $3 2>&1")
    if [[ $res1 == success* ]]; then
        res1Final="success"
    elif [[ $res1 == failed* ]]; then
        res1Final="failed"
    else
        res1Final="failed"
    fi
    res1Desc=$res1
    res1Desc="${res1Desc//','/' and '}"
    res1Desc="${res1Desc//$'\n'/' and '}"

    ## gnutls
    res2=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-gnutls/test_verify $1 $3 2>&1")
    if [[ $res2 == success* ]]; then
        res2Final="success"
    elif [[ $res2 == failed* ]]; then
        res2Final="failed"
    else
        res2Final="failed"
    fi
    res2Desc=$res2
    res2Desc="${res2Desc//','/' and '}"
    res2Desc="${res2Desc//$'\n'/' and '}"

    ## matrix
    res3=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-matrix/test_verify $1 $3 2>&1")
    if [[ $res3 == success* ]]; then
        res3Final="success"
    elif [[ $res3 == failed* ]]; then
        res3Final="failed"
    else
        res3Final="failed"
    fi
    res3Desc=$res3
    res3Desc="${res3Desc//','/' and '}"
    res3Desc="${res3Desc//$'\n'/' and '}"

    ## mbedtls
    res4=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-mbedtls/test_verify $1 $3 2>&1")
    if [[ $res4 == success* ]]; then
        res4Final="success"
    elif [[ $res4 == failed* ]]; then
        res4Final="failed"
    else
        res4Final="failed"
    fi
    res4Desc=$res4
    res4Desc="${res4Desc//','/' and '}"
    res4Desc="${res4Desc//$'\n'/' and '}"

    ## openssl
    res5=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-openssl/test_verify $1 $3 2>&1")
    if [[ $res5 == success* ]]; then
        res5Final="success"
    elif [[ $res5 == failed* ]]; then
        res5Final="failed"
    else
        res5Final="failed"
    fi
    res5Desc=$res5
    res5Desc="${res5Desc//','/' and '}"
    res5Desc="${res5Desc//$'\n'/' and '}"

    ## wolfssl
    res6=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; ./c-wolfssl/test_verify $1 $3 2>&1")
    if [[ $res6 == success* ]]; then
        res6Final="success"
    elif [[ $res6 == failed* ]]; then
        res6Final="failed"
    else
        res6Final="failed"
    fi
    res6Desc=$res6
    res6Desc="${res6Desc//','/' and '}"
    res6Desc="${res6Desc//$'\n'/' and '}"

    ## crypto
    res7=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; go run go-crypto/test_verify.go $1 $3 \"${new_time}\" 2>&1")
    if [[ $res7 == success* ]]; then
        res7Final="success"
    elif [[ $res7 == failed* ]]; then
        res7Final="failed"
    else
        res7Final="failed"
    fi
    res7Desc=$res7
    res7Desc="${res7Desc//','/' and '}"
    res7Desc="${res7Desc//$'\n'/' and '}"

    ## bouncy
    cd java-BouncyCastle/
    res8=$(faketime "${new_time}" java -cp ":bcprov-jdk18on-175.jar:" test_verify $1 $3 2>&1)
    if [[ $res8 == success* ]]; then
        res8Final="success"
    elif [[ $res8 == failed* ]]; then
        res8Final="failed"
    else
        res8Final="failed"
    fi
    res8Desc=$res8
    res8Desc="${res8Desc//','/' and '}"
    res8Desc="${res8Desc//$'\n'/' and '}"
    cd ..

    ## sun
    cd java-SUN/
    res9=$(faketime "${new_time}" java test_verify $1 $3 2>&1)
    if [[ $res9 == success* ]]; then
        res9Final="success"
    elif [[ $res9 == failed* ]]; then
        res9Final="failed"
    else
        res9Final="failed"
    fi
    res9Desc=$res9
    res9Desc="${res9Desc//','/' and '}"
    res9Desc="${res9Desc//$'\n'/' and '}"
    cd ..

    ## certvalidator
    res10=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; python3 py-certvalidator/test_verify.py $1 $3 2>&1")
    if [[ $res10 == success* ]]; then
        res10Final="success"
    elif [[ $res10 == failed* ]]; then
        res10Final="failed"
    else
        res10Final="failed"
    fi
    res10Desc=$res10
    res10Desc="${res10Desc//','/' and '}"
    res10Desc="${res10Desc//$'\n'/' and '}"

    ## aeres
    res11=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; python3 armor-driver/driver.py --chain $3 --trust_store $1 --purpose serverAuth 2>&1")
    if [[ $res11 == *success ]]; then
        res11Final="success"
    elif [[ $res11 == *failed ]]; then
        res11Final="failed"
    else
        res11Final="failed"
    fi
    res11Desc=$res11
    res11Desc="${res11Desc//','/' and '}"
    res11Desc="${res11Desc//$'\n'/' and '}"

    ## ceres
    res12=$(/bin/bash -c "export LD_PRELOAD=/usr/local/lib/faketime/libfaketime.so.1; export FAKETIME_NO_CACHE=1; export FAKETIME=\"${new_time}\"; CERES/src/bin/ceres --ca-store $1 --input $3 --check-purpose serverAuth 2>&1")
    if [[ $res12 == *"Couldn't"* ]]; then
        res12Final="failed"
    elif [[ $res12 == *"UNSAT"* ]]; then
        res12Final="failed"
    elif [[ $res12 == *"error"* ]]; then
        res12Final="failed"
    elif [[ $res12 == *"OK"* ]]; then
        res12Final="success"
    fi
    res12Desc="${res12//','/' and '}"
    res12Desc="${res12Desc//$'\n'/' and '}"

    echo "$2, $new_time, $res1Final, $res1Desc," >> $4/result_boringssl.csv
    echo "$2, $new_time, $res2Final, $res2Desc," >> $4/result_gnutls.csv
    echo "$2, $new_time, $res3Final, $res3Desc," >> $4/result_matrix.csv
    echo "$2, $new_time, $res4Final, $res4Desc," >> $4/result_mbedtls.csv
    echo "$2, $new_time, $res5Final, $res5Desc," >> $4/result_openssl.csv
    echo "$2, $new_time, $res6Final, $res6Desc," >> $4/result_wolfssl.csv
    echo "$2, $new_time, $res7Final, $res7Desc," >> $4/result_crypto.csv
    echo "$2, $new_time, $res8Final, $res8Desc," >> $4/result_bouncy.csv
    echo "$2, $new_time, $res9Final, $res9Desc," >> $4/result_sun.csv
    echo "$2, $new_time, $res10Final, $res10Desc," >> $4/result_certvalidator.csv
    echo "$2, $new_time, $res11Final, $res11Desc," >> $4/result_aeres.csv
    echo "$2, $new_time, $res12Final, $res12Desc," >> $4/result_ceres.csv
}

## main program
mkdir -p /root/tmp
export TMPDIR=/root/tmp

rm -rf $3
mkdir $3

input_dir=$2
root_store=$1

i=0

for file in $input_dir/*.pem
do
    i=$((i+1))
    call_libs $root_store $(basename $file) $file $3
    # fi
done
