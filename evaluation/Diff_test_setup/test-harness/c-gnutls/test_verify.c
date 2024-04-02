// gcc -o test_verify test_verify.c -I gnutls/BUILD/include -L gnutls/BUILD/lib -lgnutls

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "gnutls/gnutls.h"
#include "gnutls/x509.h"

char *readFile(char *fileName, int maxsize){
    FILE *file = fopen(fileName, "r");
    char *code;
    size_t n = 0;
    int c;

    if (file == NULL)
        return NULL; //could not open file

    code = malloc(maxsize);

    while ((c = fgetc(file)) != EOF){
        code[n++] = (char) c;
    }
    // don't forget to terminate with the null character
    code[n] = '\0';        
    return code;
}

void main(int argc, char** argv){

    char* ca_cert_path = argv[1];
	char* entity_cert_path = argv[2];

    char *mycert1 = readFile(entity_cert_path, 1000000);
    char *mycert0 = readFile(ca_cert_path, 1000000000);

    int len1 = strlen(mycert1); // certs
    int len0 = strlen(mycert0); // root cas

    gnutls_datum_t d1;
    gnutls_datum_t d0;

    d1.data = mycert1;
    d1.size = len1;
    d0.data = mycert0;
    d0.size = len0;

    gnutls_x509_crt_t *certchain = NULL;
    unsigned int certchain_size;
    gnutls_x509_crt_t *cacerts = NULL;
    unsigned int cacerts_size;
    int ret;

    gnutls_typed_vdata_st data[1];
	data[0].type = GNUTLS_DT_KEY_PURPOSE_OID;
	data[0].data = (void *)GNUTLS_KP_TLS_WWW_SERVER;
	data[0].size = 0;
    
	ret = gnutls_x509_crt_list_import2(&certchain, &certchain_size, &d1, GNUTLS_X509_FMT_PEM, 
		GNUTLS_X509_CRT_LIST_IMPORT_FAIL_IF_EXCEED);
	if (ret < 0 || certchain_size < 1 || certchain == NULL) {
        printf("failed\n");
        printf("error code = %d (Cert chain parse failed)\n", ret);
        exit(-1);
	}

	ret = gnutls_x509_crt_list_import2(&cacerts, &cacerts_size, &d0, GNUTLS_X509_FMT_PEM,
		GNUTLS_X509_CRT_LIST_IMPORT_FAIL_IF_EXCEED);
	if (ret < 0 || cacerts_size < 1 || cacerts == NULL) {
        printf("failed\n");
        printf("error code = %d (root CA file parse failed)\n", ret);
        exit(-1);
	}

    // init trust list
    gnutls_x509_trust_list_t tlist = NULL;
    if (gnutls_x509_trust_list_init(&tlist, 0) < GNUTLS_E_SUCCESS) {
        printf("failed\n");
        printf("error code = %d (root CA file init failed)\n", ret);
        exit(-1);
    }

    // add ca cert to list
    if (gnutls_x509_trust_list_add_cas(tlist, cacerts, cacerts_size, 0) <= 0) {
        printf("failed\n");
        printf("error code = %d (root CA file add failed)\n", ret);
        exit(-1);
    }

    unsigned int output = 0;
    gnutls_x509_trust_list_verify_crt2(tlist, certchain, certchain_size, data, 1, 0, &output, NULL);
    if (output & GNUTLS_CERT_INVALID) {
        gnutls_datum_t txt;
        gnutls_certificate_verification_status_print(output, GNUTLS_CRT_X509, &txt, 0);
        printf("failed\n");
        printf("error code = %d (%s)\n", output, txt.data);
        gnutls_free(txt.data);
    } else {
        printf("success\n");
    }
    
    gnutls_x509_trust_list_deinit(tlist, 1);
    gnutls_free(certchain);
    gnutls_free(cacerts);
}
