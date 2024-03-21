// gcc -o test_verify test_verify.c -I matrixssl/matrixssl -I matrixssl/crypto -I matrixssl/core/include -I matrixssl/core/config -I matrixssl/core/osdep/include matrixssl/matrixssl/libssl_s.a matrixssl/crypto/libcrypt_s.a matrixssl/core/libcore_s.a

#include <stdint.h>
#include <limits.h>
#include <string.h>

#include "matrixsslApi.h"

char *errtostr(int rc)
{
    static char e[80];  /* Not reentrant, but good enough for this test */

    switch (rc)
    {
    case 0:
    case PS_CERT_AUTH_PASS:
        return "PASS";
    case PS_PARSE_FAIL:
        return "FAIL Parse";
    case PS_CERT_AUTH_FAIL_BC:
        return "FAIL Basic Constraints";
    case PS_CERT_AUTH_FAIL_DN:
        return "FAIL Distinguished Name Match";
    case PS_CERT_AUTH_FAIL_SIG:
        return "FAIL Signature Validation";
    case PS_CERT_AUTH_FAIL_REVOKED:
        return "FAIL Certificate Revoked";
    case PS_CERT_AUTH_FAIL:
        return "FAIL Authentication Fail";
    case PS_CERT_AUTH_FAIL_EXTENSION:
        return "FAIL Extension";
    case PS_CERT_AUTH_FAIL_PATH_LEN:
        return "FAIL Path Length";
    case PS_CERT_AUTH_FAIL_AUTHKEY:
        return "FAIL Auth Key / Subject Key Match";
    default:
        Sprintf(e, "FAIL %d", rc);
        return e;
    }
}

void main(int argc, char** argv) {

    const char* ca_cert_path = argv[1];
    const char* ee_cert_path = argv[2];

    psX509Cert_t  *chainToBeChecked = NULL;
    psX509Cert_t  *tempp = NULL;
    psX509Cert_t  *trustedCerts = NULL;
    psX509Cert_t  *foundIssuerRet = NULL;
    psX509Crl_t   *crlp = NULL;
    int ret = 0;

    // parse end entity cert
    if (ret = psX509ParseCertFile(NULL, ee_cert_path, &chainToBeChecked, 0) < 0) {
        printf("failed\n");
        printf("error code = %d (Cert chain parse failed)\n", ret);
        exit(-1);
    }
    // printf("%s ret: %d\n", ee_cert_path, ret);

    if (ret = psX509ParseCertFile(NULL, ca_cert_path, &trustedCerts, 0) < 0) {
        printf("failed\n");
        printf("error code = %d (root CA file parse failed)\n", ret);
        exit(-1);
    }

    // verify chain
    matrixValidateCertsOptions_t options;
    Memset(&options, 0, sizeof(matrixValidateCertsOptions_t));
    options.flags |= VCERTS_FLAG_REVALIDATE_DATES;

    ret = matrixValidateCertsExt(NULL, chainToBeChecked, trustedCerts, NULL, &foundIssuerRet, NULL, NULL, &options);
    if (ret == 0) {
      printf("success\n");
    } else {
      printf("failed\n");
      printf("error code = %d (%s)\n", ret, errtostr(ret));
    }
}
