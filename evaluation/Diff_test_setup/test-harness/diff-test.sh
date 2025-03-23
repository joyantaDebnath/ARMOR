#!/bin/bash

# Set custom library paths
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-gnutls/gnutls/BUILD/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/test-harness/c-openssl/openssl/BUILD/lib

# Function to run a command and measure time + memory
run_and_measure() {
    local cmd="$1"

    # Clean temporary files
    > tmp_output.txt
    > tmp_resource.txt

    # Run the command and measure time/memory
    /usr/bin/time -f "%e,%M" -o tmp_resource.txt bash -c "$cmd" > tmp_output.txt 2>&1
    local result=$(<tmp_output.txt)

    if [[ -s tmp_resource.txt ]]; then
        local timing=$(<tmp_resource.txt)
        local time_sec=$(echo "$timing" | cut -d',' -f1)
        local mem_kb=$(echo "$timing" | cut -d',' -f2)
        if [[ -n "$mem_kb" && "$mem_kb" =~ ^[0-9]+$ ]]; then
            local mem_mb=$(awk "BEGIN {printf \"%.2f\", $mem_kb / 1024}")
        else
            local mem_mb="0.00"
        fi
    else
        local time_sec="0.00"
        local mem_mb="0.00"
    fi

    echo "$time_sec" "$mem_mb" "$result"
}

# Function to call each verification tool
call_libs(){
    local chain_file="$1"
    local trusted_ca_file="$2"
    local crl_file="$3"
    local result_dir="$4"
    local dir="$5"
    local crl_size_kb="$6"
    local crl_size_bytes="$7"
    local new_time=$(date "+%Y-%m-%d %H:%M:%S")

    echo "[INFO] CRL size: ${crl_size_kb} KB"

    echo "[INFO] Running GnuTLS..."
    read t2 m2 res2 < <(run_and_measure "./c-gnutls/test_verify $chain_file $trusted_ca_file $crl_file")
    echo "$dir, $new_time, $t2, $m2, $crl_size_kb, $res2" >> "$result_dir/result_gnutls.csv"

    echo "[INFO] Running OpenSSL..."
    read t5 m5 res5 < <(run_and_measure "./c-openssl/test_verify $chain_file $trusted_ca_file $crl_file")
    echo "$dir, $new_time, $t5, $m5, $crl_size_kb, $res5" >> "$result_dir/result_openssl.csv"

    echo "[INFO] Running Go Crypto..."
    read t7 m7 res7 < <(run_and_measure "go run go-crypto/test_verify.go $chain_file $trusted_ca_file $crl_file")
    echo "$dir, $new_time, $t7, $m7, $crl_size_kb, $res7" >> "$result_dir/result_crypto.csv"

    echo "[INFO] Running Bouncy Castle..."
    read t8 m8 res8 < <(run_and_measure "java -cp 'java-BouncyCastle/:java-BouncyCastle/bcprov-jdk18on-1.80.jar' test_verify $chain_file $trusted_ca_file $crl_file")
    echo "$dir, $new_time, $t8, $m8, $crl_size_kb, $res8" >> "$result_dir/result_bouncy.csv"

    echo "[INFO] Running Java SUN..."
    read t9 m9 res9 < <(run_and_measure "java -cp 'java-SUN/' test_verify $chain_file $trusted_ca_file $crl_file")
    echo "$dir, $new_time, $t9, $m9, $crl_size_kb, $res9" >> "$result_dir/result_sun.csv"

    # echo "[INFO] Running Python CertValidator..."
    # read t10 m10 res10 < <(run_and_measure "python3 py-certvalidator/test_verify.py $chain_file $trusted_ca_file $crl_file")
    # echo "$dir, $new_time, $t10, $m10, $crl_size_kb, $res10" >> "$result_dir/result_certvalidator.csv"

    # echo "[INFO] Running Armor..."
    # crl_max_bytes=$((60 * 1024 * 1024))
    # if [ "$crl_size_bytes" -le "$crl_max_bytes" ]; then
    #     read t11 m11 res11 < <(run_and_measure "python3 /root/armor-agda/driver.py --executable /root/armor-agda/src/Main --chain $chain_file --trust_store $trusted_ca_file --purpose serverAuth --crl $crl_file")
    #     echo "$dir, $new_time, $t11, $m11, $crl_size_kb, $res11" >> "$result_dir/result_armor.csv"
    # else
    #     echo "$dir, $new_time, NA, NA, $crl_size_kb, SKIPPED - CRL too large" >> "$result_dir/result_armor.csv"
    # fi
}

# === Main Program ===

input_dir="$1"
result_dir="$2"
trusted_ca_file="$3"

# Clean and recreate result directory
rm -rf "$result_dir"
mkdir "$result_dir"

# Process each cert directory
for dir in "$input_dir"/*/; do
    if [ -d "$dir" ]; then
        chain_file="$dir/chain.pem"
        crl_file="$dir/crl.pem"

        if [ -f "$chain_file" ] && [ -f "$crl_file" ]; then
            crl_size_bytes=$(stat -c %s "$crl_file")
            crl_size_kb=$(awk "BEGIN {printf \"%.2f\", $crl_size_bytes / 1024}")

            echo
            echo "=== Processing: $(basename "$dir") ==="
            call_libs "$(realpath "$chain_file")" "$(realpath "$trusted_ca_file")" "$(realpath "$crl_file")" "$(realpath "$result_dir")" "$(basename "$dir")" "$crl_size_kb" "$crl_size_bytes"
        fi
    fi
done

# Clean up temporary files
rm -f tmp_output.txt tmp_resource.txt
