// gcc test_verify.c -o test_verify -I mbedtls/BUILD/include  -L mbedtls/BUILD/lib -lmbedtls -lmbedx509 -lmbedcrypto

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mbedtls/x509_crt.h"
#include "mbedtls/x509_crl.h"
#include "mbedtls/error.h"
#include "mbedtls/platform.h"
#include "mbedtls/oid.h"

// Function to load certificates from a PEM file into an mbedtls_x509_crt structure
int load_certificates(const char *file, mbedtls_x509_crt *crt) {
    int ret = mbedtls_x509_crt_parse_file(crt, file);
    if (ret != 0) {
        char error_buf[100];
        mbedtls_strerror(ret, error_buf, sizeof(error_buf));
        fprintf(stderr, "Error loading certificate file '%s': %s\n", file, error_buf);
        return -1;
    }
    return 0;
}

// Function to load CRLs from a PEM file into an mbedtls_x509_crl structure
int load_crl(const char *file, mbedtls_x509_crl *crl) {
    int ret = mbedtls_x509_crl_parse_file(crl, file);
    if (ret != 0) {
        char error_buf[100];
        mbedtls_strerror(ret, error_buf, sizeof(error_buf));
        fprintf(stderr, "Error loading CRL file '%s': %s\n", file, error_buf);
        return -1;
    }
    return 0;
}

// Function to validate the certificate chain with optional CRL checking and EKU validation
void validate_certificate(mbedtls_x509_crt *chain, mbedtls_x509_crt *trusted_cas, mbedtls_x509_crl *crl, int use_crl) {
    uint32_t flags;
    int ret;

    // Verify certificate chain (use CRL if provided)
    ret = mbedtls_x509_crt_verify(chain, trusted_cas, use_crl ? crl : NULL, NULL, &flags, NULL, NULL);
    if (ret != 0) {
        char error_buf[200];
        mbedtls_x509_crt_verify_info(error_buf, sizeof(error_buf), "0 - ", flags);
        printf("%s\n", error_buf);
        return;  // Stop validation if chain verification fails
    }

    // Perform Extended Key Usage (EKU) check for server authentication
    ret = mbedtls_x509_crt_check_extended_key_usage(chain, MBEDTLS_OID_SERVER_AUTH, MBEDTLS_OID_SIZE(MBEDTLS_OID_SERVER_AUTH));
    if (ret != 0) {
        printf("0 - The certificate does not have Server Authentication EKU\n");
        return;  // Stop validation if EKU check fails
    }

    printf("1\n");  // Validation successful
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

    mbedtls_x509_crt chain, trusted_cas;
    mbedtls_x509_crl crl;
    mbedtls_x509_crt_init(&chain);
    mbedtls_x509_crt_init(&trusted_cas);
    mbedtls_x509_crl_init(&crl);

    // Load certificate chain
    if (load_certificates(chain_file, &chain) != 0) {
        printf("0 - Failed to load certificate chain\n");
        return EXIT_FAILURE;
    }

    // Load trusted CA certificates
    if (load_certificates(ca_file, &trusted_cas) != 0) {
        printf("0 - Failed to load trusted CAs\n");
        mbedtls_x509_crt_free(&chain);
        return EXIT_FAILURE;
    }

    // Load CRL if provided
    int use_crl = 0;
    if (crl_file) {
        if (load_crl(crl_file, &crl) == 0) {
            use_crl = 1; // Enable CRL validation if successfully loaded
        } else {
            printf("0 - Failed to load CRL\n");
        }
    }

    // Validate certificate with CRL (if available) and EKU check
    validate_certificate(&chain, &trusted_cas, &crl, use_crl);

    // Cleanup
    mbedtls_x509_crt_free(&chain);
    mbedtls_x509_crt_free(&trusted_cas);
    mbedtls_x509_crl_free(&crl);

    return EXIT_SUCCESS;
}