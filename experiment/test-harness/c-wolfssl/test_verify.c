// gcc test_verify.c -o test_verify -I wolfssl/BUILD/include  -L wolfssl/BUILD/lib -lwolfssl
// export LD_LIBRARY_PATH=/home/joyanta/Desktop/Research/cert_verify_harness/c-wolfssl/wolfssl/BUILD/lib

#include <stdio.h>
#include "wolfssl/options.h"
#include "wolfssl/ssl.h"
#include "wolfssl/wolfcrypt/error-crypt.h"
#include "wolfssl/test.h"

#include <stdbool.h> 

int n = 6;
int m = 1000000;
int cert_count = 0;

void readPemChain(char *fileName, char certs[n][m]){
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;

    char cert_begin[] = "BEGIN CERTIFICATE";
    char cert_end[] = "END CERTIFICATE";

    fp = fopen(fileName, "r");
    if (fp == NULL)
        return;

    while ((read = getline(&line, &len, fp)) != -1) {
    	if (strstr(line, cert_begin) != NULL) {
    		cert_count++;
    		strcpy(certs[cert_count - 1], line);

    		while ((read = getline(&line, &len, fp)) != -1) {
    			strcat(certs[cert_count - 1], line);
    			if (strstr(line, cert_end) != NULL) {
    				break;
    			}
    		}
    	}
    }

    fclose(fp);
    if (line)
        free(line);
}


void main(int argc, char** argv)
{
    int ret = -1;
    bool result = false;
    char* cacerts     = argv[1];
    char* certchain   = argv[2];

    char certs[n][m];
    readPemChain(certchain, certs);

    for (int i = cert_count - 2; i >= 0; i--) {
		wolfSSL_Init();
		WOLFSSL_CERT_MANAGER* cm = NULL;
		cm = wolfSSL_CertManagerNew();

    	if (i == cert_count - 2) {
		    wolfSSL_CertManagerLoadCA(cm, cacerts, NULL);
		    ret = wolfSSL_CertManagerVerifyBuffer(cm, certs[i], m, WOLFSSL_FILETYPE_PEM);
		    if (ret != WOLFSSL_SUCCESS) {
		    	result = false;
                break;
		    } else {result = true;}
		} else {
		    wolfSSL_CertManagerLoadCABuffer(cm, certs[i+1], m, WOLFSSL_FILETYPE_PEM);
		    ret = wolfSSL_CertManagerVerifyBuffer(cm, certs[i], m, WOLFSSL_FILETYPE_PEM);
		    if (ret != WOLFSSL_SUCCESS) {
		    	result = false;
                break;
		    } else {result = true;}
    	}
    }

	if (result == true) {
		printf("success\n");
	} else {
		printf("failed\n");
		printf("error code = %d (%s)\n", ret, wolfSSL_ERR_reason_error_string(ret));
	}

	wolfSSL_Cleanup();
}
