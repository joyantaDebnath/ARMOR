// /* certverify.c
//  *
//  * Copyright (C) 2006-2018 wolfSSL Inc.
//  *
//  * This file is part of wolfSSL.
//  *
//  * wolfSSL is free software; you can redistribute it and/or modify
//  * it under the terms of the GNU General Public License as published by
//  * the Free Software Foundation; either version 2 of the License, or
//  * (at your option) any later version.
//  *
//  * wolfSSL is distributed in the hope that it will be useful,
//  * but WITHOUT ANY WARRANTY; without even the implied warranty of
//  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  * GNU General Public License for more details.
//  *
//  * You should have received a copy of the GNU General Public License
//  * along with this program; if not, write to the Free Software
//  * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
//  */

// #include <wolfssl/options.h>
// #include <wolfssl/ssl.h>
// #include <wolfssl/crl.h>
// #include <wolfssl/wolfcrypt/error-crypt.h>
// #include <wolfssl/wolfcrypt/asn.h>
// #include <wolfssl/wolfcrypt/settings.h>

// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>


// void load_certificate(const char *filename, byte **buffer, int *size) {
    
//     FILE *file = fopen(filename, "rb");
//     if (!file) {
//         WOLFSSL_MSG("Error opening file");
//         exit(EXIT_FAILURE);
//     }

//     fseek(file, 0, SEEK_END);
//     *size = ftell(file);
//     fseek(file, 0, SEEK_SET);

//     *buffer = (byte*)malloc(*size);
//     if (!*buffer) {
//         WOLFSSL_MSG("Memory allocation failed");
//         fclose(file);
//         exit(EXIT_FAILURE);
//     }

//     fread(*buffer, 1, *size, file);
//     fclose(file);
//     // wolfSSL_Debugging_OFF();
// }

// int main(int argc, char *argv[]) {
//     if (argc != 2) {
//         printf("Usage: %s crl.pem \n", argv[0]);
//         return EXIT_FAILURE;
//     }

//     const char *crl_file = argv[1];

//     // Initialize wolfSSL
//     wolfSSL_Init();
    
//     // Create Certificate Manager
//     WOLFSSL_CERT_MANAGER *cm = wolfSSL_CertManagerNew();
//     if (!cm) {
//         printf("Failed to create Cert Manager\n");
//         return EXIT_FAILURE;
//     }

//     // Load the certificate chain (end-entity + intermediate CA)    
//     byte *crls = NULL;
//     int crls_size = 0;
//     wolfSSL_Debugging_ON();
//     load_certificate(crl_file, &crls, &crls_size);
//     int x = wolfSSL_CertManagerLoadCRLFile(cm, crl_file, WOLFSSL_FILETYPE_PEM);
//     wolfSSL_Debugging_OFF();

//     // Cleanup
//     wolfSSL_CertManagerFree(cm);
//     wolfSSL_Cleanup();

//     return SSL_SUCCESS;
// }

/* certverify.c
 *
 * Copyright (C) 2006-2018 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */
#define WOLFSSL_ASN_TEMPLATE

#include <wolfssl/options.h>
#include <wolfssl/ssl.h>
#include <wolfssl/crl.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/settings.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


void load_certificate(const char *filename, byte **buffer, int *size) {
    wolfSSL_Debugging_ON();
    FILE *file = fopen(filename, "rb");
    if (!file) {
        WOLFSSL_MSG("Error opening file");
        exit(EXIT_FAILURE);
    }

    fseek(file, 0, SEEK_END);
    *size = ftell(file);
    fseek(file, 0, SEEK_SET);

    *buffer = (byte*)malloc(*size);
    if (!*buffer) {
        WOLFSSL_MSG("Memory allocation failed");
        fclose(file);
        exit(EXIT_FAILURE);
    }

    fread(*buffer, 1, *size, file);
    fclose(file);
    // wolfSSL_Debugging_OFF();
}

int main(int argc, char *argv[]) {
    if (argc != 4) {
        printf("Usage: %s <trusted_ca.pem> <chain.pem>\n", argv[0]);
        return EXIT_FAILURE;
    }

    const char *trusted_ca_file = argv[2];
    const char *chain_file = argv[1];
    const char *crl_file = argv[3];

    // Initialize wolfSSL

    wolfSSL_Init();
    


    // Create Certificate Manager
    WOLFSSL_CERT_MANAGER *cm = wolfSSL_CertManagerNew();
    if (!cm) {
        printf("Failed to create Cert Manager\n");
        return EXIT_FAILURE;
    }

    // Load trusted CA store
    if (wolfSSL_CertManagerLoadCA(cm, trusted_ca_file, NULL) != SSL_SUCCESS) {
        printf("Failed to load trusted CA store: %s\n", trusted_ca_file);
        wolfSSL_CertManagerFree(cm);
        wolfSSL_Cleanup();
        return EXIT_FAILURE;
    }

    // Load the certificate chain (end-entity + intermediate CA)
    byte *cert_chain = NULL;
    int chain_size = 0;
    load_certificate(chain_file, &cert_chain, &chain_size);
    wolfSSL_CertManagerLoadCABuffer_ex(cm, cert_chain, chain_size, WOLFSSL_FILETYPE_PEM, 1, WOLFSSL_LOAD_VERIFY_DEFAULT_FLAGS);
    
    wolfSSL_Debugging_ON();
    byte *crls = NULL;
    int crls_size = 0;
    load_certificate(crl_file, &crls, &crls_size);
    printf("%d\n", crls_size);
    int x = wolfSSL_CertManagerLoadCRLFile(cm, crl_file, WOLFSSL_FILETYPE_PEM);
    printf("%d\n", x);
    wolfSSL_Debugging_OFF();

    // Verify the certificate chain
    int ret = wolfSSL_CertManagerVerifyBuffer(cm, cert_chain, chain_size, WOLFSSL_FILETYPE_PEM);
    if (ret == SSL_SUCCESS) {
        printf("Certificate chain verification successful!\n");
    } else {
        char err[4096];
        wolfSSL_ERR_error_string(ret, err);
        printf("Certificate verification failed: %s\n", err);
    }

    // Cleanup
    free(cert_chain);
    wolfSSL_CertManagerFree(cm);
    wolfSSL_Cleanup();

    return (ret == SSL_SUCCESS) ? EXIT_SUCCESS : EXIT_FAILURE;
}
