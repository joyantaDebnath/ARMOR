// gcc -o test_verify test_verify.c -I boringssl/install/include boringssl/install/lib/libcrypto.a  boringssl/install/lib/libssl.a
// fork of openssl

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "openssl/bio.h"
#include "openssl/err.h"
#include "openssl/pem.h"
#include "openssl/x509.h"
#include "openssl/x509_vfy.h"
#include "openssl/x509v3.h"


// Function to load CRLs from a PEM file (only if provided)
STACK_OF(X509_CRL) *load_crls(const char *crl_file) {
    STACK_OF(X509_CRL) *crls = sk_X509_CRL_new_null();
    if (!crls) {
        fprintf(stderr, "Error creating X509_CRL stack\n");
        return NULL;
    }

    BIO *bio = BIO_new_file(crl_file, "r");
    if (!bio) {
        fprintf(stderr, "Error opening CRL file: %s\n", crl_file);
        sk_X509_CRL_free(crls);
        return NULL;
    }

    X509_CRL *crl;
    while ((crl = PEM_read_bio_X509_CRL(bio, NULL, NULL, NULL))) {
        sk_X509_CRL_push(crls, crl);
    }

    BIO_free(bio);
    return crls;
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s  crl.pem\n", argv[0]);
        printf("0 - Incorrect usage\n");
        return EXIT_FAILURE;
    }

    const char *crl_file = argv[1]; // CRL file is optional

    // Load CRLs (only if provided)
    STACK_OF(X509_CRL) *crls = NULL;
    crls = load_crls(crl_file);
    if (!crls) {
        fprintf(stderr, "Failed to load CRLs.\n");
        printf("0 - Failed to load CRLs\n");
    }


    sk_X509_CRL_pop_free(crls, X509_CRL_free);

    return EXIT_SUCCESS;
}