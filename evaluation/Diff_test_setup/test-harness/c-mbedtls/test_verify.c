// gcc test_verify.c -o test_verify -I mbedtls/BUILD/include  -L mbedtls/BUILD/lib -lmbedtls -lmbedx509 -lmbedcrypto

#include "mbedtls/x509.h"
#include "mbedtls/x509_crt.h"
#include "mbedtls/base64.h"
#include "mbedtls/error.h"
#include "mbedtls/platform.h"
#include "mbedtls/ssl.h"
#include "mbedtls/oid.h"

#include <stdio.h>
#include <string.h>

void main(int argc, char **argv)
{
	char* trust_anchor_path = argv[1];
	char* leaf_cert_path = argv[2];

	mbedtls_x509_crt chain1, chain2;
    memset(&chain1, 0, sizeof(chain1));
    memset(&chain2, 0, sizeof(chain2));

	mbedtls_x509_crt *mytrusted_chain_ptr = &chain2;
    mbedtls_x509_crt *mychain_ptr = &chain1;

	//---  parse trusted root CA cert
	int ret = mbedtls_x509_crt_parse_file(mytrusted_chain_ptr, trust_anchor_path);
	if ( ret != 0){
		printf("failed\n");
		printf("error code = %d (root CA file parse failed)\n", ret);
		exit(-1);
	}
	//---  parse cert chain
	ret = mbedtls_x509_crt_parse_file(mychain_ptr, leaf_cert_path);
	if (ret != 0 ){
		printf("error code = %d (Cert chain parse failed)\n", ret);
		exit(-1);
	}
	
	uint32_t verify_results = 0;
    ret = mbedtls_x509_crt_verify(mychain_ptr, mytrusted_chain_ptr, NULL, NULL, &verify_results, NULL, NULL);
    if (ret != 0) {
	    char vrfy_buf[1000000];
	    mbedtls_strerror(ret, vrfy_buf, sizeof(vrfy_buf));
	    printf("failed\n");
	    printf("error code = %u (%s)\n", verify_results, vrfy_buf);
    } else {
        int ret2 = mbedtls_x509_crt_check_extended_key_usage(mychain_ptr, MBEDTLS_OID_SERVER_AUTH,
                    MBEDTLS_OID_SIZE(MBEDTLS_OID_SERVER_AUTH));
        
        if (ret2 != 0) {
        	printf("failed\n");
        	printf("error code = purpose mismatch\n");
        } else {
        	printf("success\n");
        }
    }

    mbedtls_x509_crt_free(mychain_ptr);
    mbedtls_x509_crt_free(mytrusted_chain_ptr);
}