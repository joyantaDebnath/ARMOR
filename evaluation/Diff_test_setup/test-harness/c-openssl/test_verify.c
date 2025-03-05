// gcc -o test_verify test_verify.c -I openssl/BUILD/include openssl/BUILD/lib/libcrypto.a  openssl/BUILD/lib/libssl.a

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "openssl/bio.h"
#include "openssl/err.h"
#include "openssl/pem.h"
#include "openssl/x509.h"
#include "openssl/x509_vfy.h"
#include "openssl/x509v3.h"

// Function to load certificate chain from a PEM file
STACK_OF(X509) *load_certificate_chain(const char *chain_file, X509 **end_cert) {
    STACK_OF(X509) *chain = sk_X509_new_null();
    if (!chain) {
        fprintf(stderr, "Error creating X509 stack\n");
        return NULL;
    }

    BIO *bio = BIO_new_file(chain_file, "r");
    if (!bio) {
        fprintf(stderr, "Error opening certificate chain file: %s\n", chain_file);
        sk_X509_free(chain);
        return NULL;
    }

    X509 *cert = PEM_read_bio_X509(bio, NULL, NULL, NULL);
    if (!cert) {
        fprintf(stderr, "Error reading end-entity certificate\n");
        sk_X509_free(chain);
        BIO_free(bio);
        return NULL;
    }
    *end_cert = cert; // Store the end-entity certificate

    while ((cert = PEM_read_bio_X509(bio, NULL, NULL, NULL))) {
        sk_X509_push(chain, cert);
    }

    BIO_free(bio);
    return chain;
}

// Function to load trusted CA certificates
X509_STORE *load_trusted_cas(const char *ca_file) {
    X509_STORE *store = X509_STORE_new();
    if (!store) {
        fprintf(stderr, "Error creating X509_STORE\n");
        return NULL;
    }

    X509_LOOKUP *lookup = X509_STORE_add_lookup(store, X509_LOOKUP_file());
    if (!lookup || !X509_LOOKUP_load_file(lookup, ca_file, X509_FILETYPE_PEM)) {
        fprintf(stderr, "Error loading CA certificates from %s\n", ca_file);
        X509_STORE_free(store);
        return NULL;
    }

    return store;
}

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

// Function to perform certificate chain validation (with optional CRL check)
void validate_certificate(X509 *end_cert, STACK_OF(X509) *chain, X509_STORE *store, STACK_OF(X509_CRL) *crls) {
    X509_STORE_CTX *ctx = X509_STORE_CTX_new();
    if (!ctx) {
        fprintf(stderr, "Error creating X509_STORE_CTX\n");
        printf("0 - Error creating X509_STORE_CTX\n");
        return;
    }

    // Add CRLs to the verification store if provided
    if (crls) {
        for (int i = 0; i < sk_X509_CRL_num(crls); i++) {
            X509_CRL *crl = sk_X509_CRL_value(crls, i);
            X509_STORE_add_crl(store, crl);
        }
    }

    // Initialize the verification context
    if (!X509_STORE_CTX_init(ctx, store, end_cert, chain)) {
        fprintf(stderr, "Error initializing verification context\n");
        printf("0 - Error initializing verification context\n");
        X509_STORE_CTX_free(ctx);
        return;
    }

    X509_VERIFY_PARAM *param = X509_VERIFY_PARAM_new();
    if (!param) {
        fprintf(stderr, "Error allocating X509_VERIFY_PARAM\n");
        printf("0 - Error allocating X509_VERIFY_PARAM\n");
        X509_STORE_CTX_free(ctx);
        return;
    }

    X509_VERIFY_PARAM_set_purpose(param, X509_PURPOSE_SSL_SERVER);
    X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_X509_STRICT);

    // Enable CRL check only if CRLs are provided
    if (crls) {
        X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_CRL_CHECK | X509_V_FLAG_CRL_CHECK_ALL);
    }

    X509_VERIFY_PARAM_set_depth(param, 10);
    X509_STORE_CTX_set0_param(ctx, param);

    // Perform verification
    int result = X509_verify_cert(ctx);
    if (result == 1) {
        printf("1\n"); // Print success as per requirement
    } else {
        int err = X509_STORE_CTX_get_error(ctx);
        printf("0 - %s\n", X509_verify_cert_error_string(err)); // Print failure with error reason
    }

    // // Cleanup
    X509_STORE_CTX_free(ctx);
}

int main(int argc, char *argv[]) {
    if (argc < 3 || argc > 4) {
        fprintf(stderr, "Usage: %s <chain.pem> <trusted_ca.pem> [crl.pem]\n", argv[0]);
        printf("0 - Incorrect usage\n");
        return EXIT_FAILURE;
    }

    const char *chain_file = argv[1];
    const char *ca_file = argv[2];
    const char *crl_file = (argc == 4) ? argv[3] : NULL; // CRL file is optional

    // Load Certificate Chain
    X509 *end_cert = NULL;
    STACK_OF(X509) *chain = load_certificate_chain(chain_file, &end_cert);
    if (!chain || !end_cert) {
        fprintf(stderr, "Failed to load certificate chain.\n");
        printf("0 - Failed to load certificate chain\n");
        return EXIT_FAILURE;
    }

    // Load Trusted CA Certificates
    X509_STORE *store = load_trusted_cas(ca_file);
    if (!store) {
        sk_X509_free(chain);
        X509_free(end_cert);
        fprintf(stderr, "Failed to load trusted CAs.\n");
        printf("0 - Failed to load trusted CAs\n");
        return EXIT_FAILURE;
    }

    // Load CRLs (only if provided)
    STACK_OF(X509_CRL) *crls = NULL;
    if (crl_file) {
        crls = load_crls(crl_file);
        if (!crls) {
            fprintf(stderr, "Failed to load CRLs.\n");
            printf("0 - Failed to load CRLs\n");
        }
    }

    // Validate Certificate
    validate_certificate(end_cert, chain, store, crls);

    // Cleanup
    X509_free(end_cert);
    sk_X509_pop_free(chain, X509_free);
    if (crls) {
        sk_X509_CRL_pop_free(crls, X509_CRL_free);
    }
    X509_STORE_free(store);

    return EXIT_SUCCESS;
}