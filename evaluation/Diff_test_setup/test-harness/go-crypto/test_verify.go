package main

import (
	"crypto/x509"
	"encoding/pem"
	"fmt"
	"io/ioutil"
	"os"
)

// loadCertificates reads certificates from a PEM file
func loadCertificates(filename string) ([]*x509.Certificate, error) {
	data, err := ioutil.ReadFile(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %v", err)
	}

	var certs []*x509.Certificate
	var block *pem.Block
	for {
		block, data = pem.Decode(data)
		if block == nil {
			break
		}

		cert, err := x509.ParseCertificate(block.Bytes)
		if err != nil {
			return nil, fmt.Errorf("failed to parse certificate: %v", err)
		}
		certs = append(certs, cert)
	}

	if len(certs) == 0 {
		return nil, fmt.Errorf("no valid certificates found")
	}
	return certs, nil
}

// loadCRLs reads CRLs from a PEM file
func loadCRLs(filename string) ([]*x509.RevocationList, error) {
	data, err := ioutil.ReadFile(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to read CRL file: %v", err)
	}

	var crls []*x509.RevocationList
	var block *pem.Block
	for {
		block, data = pem.Decode(data)
		if block == nil {
			break
		}

		crl, err := x509.ParseRevocationList(block.Bytes)
		if err != nil {
			return nil, fmt.Errorf("failed to parse CRL: %v", err)
		}
		crls = append(crls, crl)
	}

	if len(crls) == 0 {
		return nil, fmt.Errorf("no valid CRLs found")
	}
	return crls, nil
}

// findMatchingCRL finds a CRL that matches the issuer of the given certificate
func findMatchingCRL(cert *x509.Certificate, crls []*x509.RevocationList) *x509.RevocationList {
	for _, crl := range crls {
		if cert.Issuer.String() == crl.Issuer.String() {
			return crl
		}
	}
	return nil
}

// checkCRLSignature verifies that the CRL is properly signed by its issuer
func checkCRLSignature(crl *x509.RevocationList, issuerCert *x509.Certificate) error {
	if err := crl.CheckSignatureFrom(issuerCert); err != nil {
		return fmt.Errorf("CRL signature verification failed for issuer %s", crl.Issuer.String())
	}
	return nil
}

// checkRevocation validates the entire certificate chain except for the trusted CA
func checkRevocation(certChain []*x509.Certificate, crls []*x509.RevocationList) error {
	if len(crls) == 0 {
		// No CRLs provided, skip revocation check
		return nil
	}

	// Iterate over all certificates except the last one (trusted CA)
	for i := 0; i < len(certChain)-1; i++ {
		cert := certChain[i]
		issuer := certChain[i+1]

		// Find a matching CRL
		matchingCRL := findMatchingCRL(cert, crls)
		if matchingCRL == nil {
			return fmt.Errorf("No CRL is provided for %s", cert.Subject.String())
		}

		// Validate CRL signature
		err := checkCRLSignature(matchingCRL, issuer)
		if err != nil {
			return err
		}

		// Check if the certificate is revoked
		for _, revoked := range matchingCRL.RevokedCertificates {
			if revoked.SerialNumber.Cmp(cert.SerialNumber) == 0 {
				return fmt.Errorf("certificate issued by %s is revoked", cert.Issuer.String())
			}
		}
	}

	return nil
}

func main() {
	if len(os.Args) < 3 {
		fmt.Println("0 - Usage: verify <Certificate Chain file> <Trusted CA file> [CRL file]")
		return
	}

	chainFile := os.Args[1]
	caFile := os.Args[2]
	var crlFile string
	if len(os.Args) > 3 {
		crlFile = os.Args[3]
	}

	// Load certificate chain (Leaf + intermediates)
	certChain, err := loadCertificates(chainFile)
	if err != nil {
		fmt.Printf("0 - Error loading certificate chain: %v\n", err)
		return
	}

	// Load CA certificates (Trust Anchors)
	trustedCAs, err := loadCertificates(caFile)
	if err != nil {
		fmt.Printf("0 - Error loading trusted CA certificates: %v\n", err)
		return
	}

	// Create a CertPool for CA certificates
	rootCAs := x509.NewCertPool()
	for _, caCert := range trustedCAs {
		rootCAs.AddCert(caCert)
	}

	leafCert := certChain[0]

	// Verify the certificate chain
	intermediatePool := x509.NewCertPool()
	for _, cert := range certChain[1:] {
		intermediatePool.AddCert(cert)
	}

	opts := x509.VerifyOptions{
		Roots:         rootCAs,
		Intermediates: intermediatePool,
		KeyUsages:     []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}

	_, err = leafCert.Verify(opts)
	if err != nil {
		fmt.Printf("0 - Validation failed: %v\n", err)
		return
	}

	// Load CRLs if provided
	var crls []*x509.RevocationList
	if crlFile != "" {
		crls, err = loadCRLs(crlFile)
		if err != nil {
			fmt.Printf("0 - Error loading CRLs: %v\n", err)
			return
		}

		// Perform revocation check only if CRLs were provided
		err = checkRevocation(certChain, crls)
		if err != nil {
			fmt.Printf("0 - %v\n", err)
			return
		}
	}

	fmt.Println("1") // Success
}
