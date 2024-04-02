// gcc -o test_verify test_verify.c -I openssl/BUILD/include -L openssl/BUILD/lib -lcrypto

#include <stdio.h>

#include "openssl/bio.h"
#include "openssl/err.h"
#include "openssl/pem.h"
#include "openssl/x509.h"
#include "openssl/x509_vfy.h"
#include "openssl/x509v3.h"

#include <stdbool.h> 

void main(int argc, char** argv) {

  int ret = -1;
  bool result = true;
  char *ca_bundlestr = argv[1];
  char *cert_filestr = argv[2];

  BIO              *certbio = NULL;
  X509                *cert = NULL;
  X509           *extracert = NULL;
  STACK_OF(X509)  *extracerts = NULL;
  X509_NAME    *certsubject = NULL;
  X509_STORE         *store = NULL;
  X509_STORE_CTX  *vrfy_ctx = NULL;

  /* ---------------------------------------------------------- *
   * These function calls initialize openssl for correct work.  *
   * ---------------------------------------------------------- */
  OpenSSL_add_all_algorithms();
  ERR_load_crypto_strings();

  /* ---------------------------------------------------------- *
   * Create the Input/Output BIO's.                             *
   * ---------------------------------------------------------- */
  certbio = BIO_new(BIO_s_file());

  /* ---------------------------------------------------------- *
   * Initialize the global certificate validation store object. *
   * ---------------------------------------------------------- */
  store = X509_STORE_new();

  /* ---------------------------------------------------------- *
   * Create the context structure for the validation operation. *
   * ---------------------------------------------------------- */
  vrfy_ctx = X509_STORE_CTX_new();

  /* ---------------------------------------------------------- *
   * Load the certificate and cacert chain from file (PEM).     *
   * ---------------------------------------------------------- */
  BIO_read_filename(certbio, cert_filestr);
  cert = PEM_read_bio_X509(certbio, NULL, NULL, NULL);
  extracerts = sk_X509_new_null();
  while((extracert = PEM_read_bio_X509 (certbio, NULL, NULL, NULL)) != NULL ) {
    sk_X509_push(extracerts, extracert);
  }

  X509_STORE_load_locations(store, ca_bundlestr, NULL);

  /* ---------------------------------------------------------- *
   * Initialize the ctx structure for a verification operation: *
   * Set the trusted cert store, the unvalidated cert, and any  *
   * potential certs that could be needed (here we set it NULL) *
   * ---------------------------------------------------------- */
  X509_STORE_CTX_init(vrfy_ctx, store, cert, extracerts);

  X509_VERIFY_PARAM *param = X509_STORE_CTX_get0_param(vrfy_ctx);
  /* Set the purpose for certificate verification */
  X509_VERIFY_PARAM_set_purpose(param, X509_PURPOSE_SSL_SERVER);
  /* Enable strict verification */
  X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_X509_STRICT);
  X509_STORE_CTX_set0_param(vrfy_ctx, param);

  /* ---------------------------------------------------------- *
   * Check the complete cert chain can be build and validated.  *
   * Returns 1 on success, 0 on verification failures, and -1   *
   * for trouble with the ctx object (i.e. missing certificate) *
   * ---------------------------------------------------------- */
  ret = X509_verify_cert(vrfy_ctx);
  if(ret == 0 || ret == -1)
    result = false;


  if (result == true) {
    printf("success\n");
  } else {
    printf("failed\n");
    printf("error code = %d (%s)\n", X509_STORE_CTX_get_error(vrfy_ctx), X509_verify_cert_error_string(X509_STORE_CTX_get_error(vrfy_ctx)));
  }

  /* ---------------------------------------------------------- *
   * Free up all structures                                     *
   * ---------------------------------------------------------- */
  // X509_STORE_CTX_free(vrfy_ctx);
  X509_STORE_free(store);
  X509_free(cert);
  // X509_VERIFY_PARAM_free(param);
  sk_X509_pop_free(extracerts, X509_free);
  BIO_free_all(certbio);
}