// gcc -o test_verify test_verify.c -I gnutls/BUILD/include -L gnutls/BUILD/lib -lgnutls
// only one DER

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <gnutls/gnutls.h>
#include <gnutls/x509.h>

#define MAX_CERT_SIZE 1000000
#define MAX_CA_SIZE 1000000000
#define MAX_CRL_SIZE 1000000000

// Function to read a text file (PEM certificates or CRLs)
char *readFile(const char *fileName, int maxsize) {
    FILE *file = fopen(fileName, "r");
    if (file == NULL) return NULL;

    char *buffer = malloc(maxsize);
    if (!buffer) {
        fclose(file);
        return NULL;
    }

    size_t n = 0;
    int c;
    while ((c = fgetc(file)) != EOF && n < maxsize - 1) {
        buffer[n++] = (char)c;
    }
    buffer[n] = '\0';

    fclose(file);
    return buffer;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) {
        printf("Usage: %s <entity_cert> <CA_bundle> [CRL_file]\n", argv[0]);
        printf("0 - Incorrect usage\n");
        return EXIT_FAILURE;
    }

    char *entity_cert_path = argv[1];
    char *ca_cert_path = argv[2];
    char *crl_path = (argc == 4) ? argv[3] : NULL;

    // Read certificates and CRLs from files
    char *entity_cert = readFile(entity_cert_path, MAX_CERT_SIZE);
    char *ca_cert = readFile(ca_cert_path, MAX_CA_SIZE);
    char *crl_data = crl_path ? readFile(crl_path, MAX_CRL_SIZE) : NULL;

    if (!entity_cert || !ca_cert || (crl_path && !crl_data)) {
        printf("0 - Error reading files\n");
        return EXIT_FAILURE;
    }

    gnutls_datum_t d1 = { (unsigned char *)entity_cert, strlen(entity_cert) };
    gnutls_datum_t d0 = { (unsigned char *)ca_cert, strlen(ca_cert) };
    gnutls_datum_t d_crl = { NULL, 0 };  // Initialize empty CRL data

    if (crl_path && crl_data) {
        d_crl.data = (unsigned char *)crl_data;
        d_crl.size = strlen(crl_data);
    }

    gnutls_x509_crt_t *certchain = NULL;
    unsigned int certchain_size;
    gnutls_x509_crt_t *cacerts = NULL;
    unsigned int cacerts_size;
    gnutls_x509_crl_t *crls = NULL;
    unsigned int crl_count = 0;
    int ret;

    gnutls_typed_vdata_st data[1];
    data[0].type = GNUTLS_DT_KEY_PURPOSE_OID;
    data[0].data = (void *)GNUTLS_KP_TLS_WWW_SERVER;
    data[0].size = 0;

    // Import entity certificate chain
    ret = gnutls_x509_crt_list_import2(&certchain, &certchain_size, &d1, GNUTLS_X509_FMT_PEM, GNUTLS_X509_CRT_LIST_IMPORT_FAIL_IF_EXCEED);
    if (ret < 0 || certchain_size < 1) {
        printf("0 - Certificate chain parsing failed\n");
        return EXIT_FAILURE;
    }

    // Import CA certificates
    ret = gnutls_x509_crt_list_import2(&cacerts, &cacerts_size, &d0, GNUTLS_X509_FMT_PEM, GNUTLS_X509_CRT_LIST_IMPORT_FAIL_IF_EXCEED);
    if (ret < 0 || cacerts_size < 1) {
        printf("0 - Root CA file parsing failed\n");
        return EXIT_FAILURE;
    }

    // Import CRLs if provided (in PEM format, handling multiple CRLs)
    if (crl_path && crl_data) {
        ret = gnutls_x509_crl_list_import2(&crls, &crl_count, &d_crl, GNUTLS_X509_FMT_PEM, GNUTLS_X509_CRT_LIST_IMPORT_FAIL_IF_EXCEED);
        if (ret < 0 || crl_count < 1) {
            printf("0 - CRL file parsing failed\n");
            return EXIT_FAILURE;
        }
    }

    // Initialize trust list
    gnutls_x509_trust_list_t tlist;
    if (gnutls_x509_trust_list_init(&tlist, 0) < 0) {
        printf("0 - Trust list initialization failed\n");
        return EXIT_FAILURE;
    }

    // Add CA certificates to trust list
    if (gnutls_x509_trust_list_add_cas(tlist, cacerts, cacerts_size, 0) <= 0) {
        printf("0 - Adding CA to trust list failed\n");
        return EXIT_FAILURE;
    }

    // Add CRLs to trust list if provided
    if (crl_path && crl_data) {
        ret = gnutls_x509_trust_list_add_crls(tlist, crls, crl_count, 0, 0);
        if (ret < 0) {
            printf("0 - Adding CRL to trust list failed\n");
            return EXIT_FAILURE;
        }
    }

    // Perform verification with optional CRL checking
    unsigned int output = 0;
    gnutls_x509_trust_list_verify_crt2(tlist, certchain, certchain_size, data, 1, 0, &output, NULL);
    
    if (output & (GNUTLS_CERT_INVALID | GNUTLS_CERT_REVOKED)) {
        gnutls_datum_t txt;
        gnutls_certificate_verification_status_print(output, GNUTLS_CRT_X509, &txt, 0);
        printf("0 - %s\n", txt.data);
        gnutls_free(txt.data);
    } else {
        printf("1\n");
    }

    // Cleanup
    if (crl_path && crl_data) {
        for (unsigned int i = 0; i < crl_count; i++)
            gnutls_x509_crl_deinit(crls[i]);
        gnutls_free(crls);
    }

    for (unsigned int i = 0; i < certchain_size; i++)
        gnutls_x509_crt_deinit(certchain[i]);
    gnutls_free(certchain);

    for (unsigned int i = 0; i < cacerts_size; i++)
        gnutls_x509_crt_deinit(cacerts[i]);
    gnutls_free(cacerts);

    free(entity_cert);
    free(ca_cert);
    free(crl_data);

    return EXIT_SUCCESS;
}
