#!/bin/bash

export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-gnutls/gnutls/BUILD/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-openssl/openssl/BUILD/lib

call_libs(){
    local chain_file="$1"
    local trusted_ca_file="$2"
    local crl_file="$3"
    local result_dir="$4"
    local dir="$5"
    local new_time=$(date "+%Y-%m-%d %H:%M:%S")

    ## gnutls
    res2=$(/bin/bash -c "./c-gnutls/test_verify $chain_file $trusted_ca_file $crl_file 2>&1")

    ## openssl
    res5=$(/bin/bash -c "./c-openssl/test_verify $chain_file $trusted_ca_file $crl_file 2>&1")

    ## crypto
    res7=$(/bin/bash -c "go run go-crypto/test_verify.go $chain_file $trusted_ca_file $crl_file 2>&1")

    ## bouncy
    cd java-BouncyCastle/
    res8=$(java -cp ":bcprov-jdk18on-175.jar:" test_verify $chain_file $trusted_ca_file $crl_file 2>&1)
    cd ..

    ## sun
    cd java-SUN/
    res9=$(java test_verify $chain_file $trusted_ca_file $crl_file 2>&1)
    cd ..

    ## certvalidator
    res10=$(/bin/bash -c "python3 py-certvalidator/test_verify.py $chain_file $trusted_ca_file $crl_file 2>&1")

    echo "$dir, $new_time, $res2," >> $result_dir/result_gnutls.csv
    echo "$dir, $new_time, $res5," >> $result_dir/result_openssl.csv
    echo "$dir, $new_time, $res7," >> $result_dir/result_crypto.csv
    echo "$dir, $new_time, $res8," >> $result_dir/result_bouncy.csv
    echo "$dir, $new_time, $res9," >> $result_dir/result_sun.csv
    echo "$dir, $new_time, $res10," >> $result_dir/result_certvalidator.csv
}

## main program

input_dir="$1"
result_dir="$2"
trusted_ca_file="$3"

rm -rf $result_dir
mkdir $result_dir

# Iterate over all directories in the given directory
for dir in "$input_dir"/*/; do
    if [ -d "$dir" ]; then
        # Define file paths
        chain_file="$dir/chain.pem"
        crl_file="$dir/crl.pem"

        # Check if both files exist
        if [ -f "$chain_file" ] && [ -f "$crl_file" ]; then
            echo "Directory: $(basename "$dir")"
            call_libs $(realpath "$chain_file") $(realpath "$trusted_ca_file") $(realpath "$crl_file") $(realpath "$result_dir") $(basename $dir)
        fi
    fi
done
