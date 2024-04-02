## Steps Taken to Modify BoringSSL
- We adjust the `tls13_process_certificate` function found in
    [modified_boringssl/ssl/tls13_both.cc](modified_boringssl/ssl/tls13_both.cc) to capture the DER-encoded certificate bytes from the
    incoming TLS Certificate handshake message. Subsequently, we
    save these bytes to a temporary file on the local disk. 
- We modify the `ssl_crypto_x509_session_verify_cert_chain` function
    in [modified_boringssl/ssl/ssl_x509.cc](modified_boringssl/ssl/ssl_x509.cc) to employ a pipe to execute the ARMOR
    binary, specifying the paths to the root CA store and the temporary DER
    certificate file.
- We do not modify or disable the standard certificate verification
    process of BoringSSL. Rather, we determine the final result of the chain
    verification by also taking into account the outcome from ARMOR. If both
    BoringSSL and ARMOR return *true*, the certificate chain is
    accepted. If not, the connection is terminated due to a possible
    inconsistency or validation failure.

## Assumptions
- ARMOR is already built and installed
- OS: Linux
- Trusted CA Store Location: `/etc/ssl/certs/ca-certificates.crt`

## Build
`./install.sh`

## Run (Example)
`./curl/BUILD/bin/curl -s "https://www.amazon.com"`
