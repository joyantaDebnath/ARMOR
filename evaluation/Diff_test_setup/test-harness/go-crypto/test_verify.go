package main

import (
	"crypto/x509"
	"encoding/pem"
	"io/ioutil"
	"log"
	"os"
	"fmt"
	"time"
)

func main() {

	// Check if the required arguments are provided
	if len(os.Args) != 4 {
		fmt.Println("Usage: go run test_verify.go <root-cert-path> <intermediate-cert-path> <time>")
		return
	}

	// Read the root and intermediate certificate file paths from the command line arguments
	rootCertPath := os.Args[1]
	intermediateCertPath := os.Args[2]

	// Read the time input from the command line argument
	timeArg := os.Args[3]

	// Define the custom time layout
	customLayout := "2006-01-02 15:04:05"

	// Parse the time input
	inputTime, err := time.Parse(customLayout, timeArg)
	if err != nil {
		fmt.Printf("Error parsing time: %v\n", err)
		return
	}

	log.SetFlags(0)
	certPEM, err := ioutil.ReadFile(intermediateCertPath)
	if err != nil {
		log.Printf("failed")
		log.Printf(err.Error())
		os.Exit(-1)
	}

	intcerts := x509.NewCertPool()
	ok := intcerts.AppendCertsFromPEM([]byte(certPEM))
	if !ok {
		log.Printf("failed")
		log.Printf("failed to parse Cert chain")
		os.Exit(-1)
	}

	rootPEM, err := ioutil.ReadFile(rootCertPath)
	if err != nil {
		log.Printf("failed")
		log.Printf(err.Error())
		os.Exit(-1)
	}

	roots := x509.NewCertPool()
	ok2 := roots.AppendCertsFromPEM([]byte(rootPEM))
	if !ok2 {
		log.Printf("failed")
		log.Printf("failed to parse CA certs")
		os.Exit(-1)
	}

	block, _ := pem.Decode([]byte(certPEM))
	if block == nil {
		log.Printf("failed")
		log.Printf("failed to parse Cert chain")
		os.Exit(-1)
	}
	cert, err := x509.ParseCertificate(block.Bytes)
	if err != nil {
		log.Printf("failed")
		log.Printf(err.Error())
		os.Exit(-1)
	}

	opts := x509.VerifyOptions{
		Roots: roots,
		Intermediates: intcerts,
		CurrentTime: inputTime,
		KeyUsages: []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}

	if _, err := cert.Verify(opts); err != nil {
		log.Printf("failed")
		log.Printf(err.Error())
		os.Exit(-1)
	}

	log.Printf("success")
}
