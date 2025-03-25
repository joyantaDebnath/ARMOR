#### mbedtls setup client

git submodule update --init --recursive
scripts/config.py full
mkdir -p BUILD
make; make DESTDIR=BUILD install

./programs/ssl/ssl_client2 server_name=localhost server_port=4443 ca_file=/home/joyanta/Desktop/ARMOR/evaluation/Diff_test_setup/tls-test/certs/ca_cert.pem crl_file=/home/joyanta/Desktop/ARMOR/evaluation/Diff_test_setup/tls-test/certs/ca_crl.pem

### boringssl setup client
./boringssl/BUILD/bssl s_client -connect localhost:4444 -root-certs ../certs/ca_cert.pem -crl ../certs/ca_crl.pem

### openssl setup client
normal by cli
./openssl/BUILD/bin/openssl s_client -connect www.google.com:443 -CAfile ../certs/ca_cert.pem -crl_check -CRL ../certs/ca_crl.pem

### wolfssl setup client
./client -h www.google.com -p 443 -A /etc/ssl/certs/ca-certificates.crt

### certvalidator
certvalidator does not do the TLS handshake — it only verifies the X.509 path

### gnutls setup client
normal by cli
./tls-gnutls/gnutls/BUILD/bin/gnutls-cli localhost:4444 --x509cafile certs/ca_cert.pem --x509crlfile certs/ca_crl.pem

### go-crypto
does not implement revocation checking

## java-sun, bouncy-castle
looks good