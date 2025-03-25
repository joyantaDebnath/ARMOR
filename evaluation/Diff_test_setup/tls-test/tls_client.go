package main

import (
	"crypto/tls"
	"fmt"
	"io"
	"log"
)

func main() {
	// Define the server address (hostname:port)
	server := "www.google.com:443"

	// Configure TLS settings
	conf := &tls.Config{
		InsecureSkipVerify: false, // Set to true to skip cert verification (not recommended)
		ServerName:         "www.google.com", // Needed for SNI and hostname verification
	}

	// Establish TLS connection
	conn, err := tls.Dial("tcp", server, conf)
	if err != nil {
		log.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	fmt.Println("Connected to", conn.RemoteAddr())
	fmt.Printf("TLS handshake complete. Using %s\n", conn.ConnectionState().CipherSuite)

	// Send a basic HTTP GET request
	request := "GET / HTTP/1.1\r\nHost: www.google.com\r\nConnection: close\r\n\r\n"
	_, err = conn.Write([]byte(request))
	if err != nil {
		log.Fatalf("failed to write to server: %v", err)
	}

	// Read the response
	buf := make([]byte, 4096)
	for {
		n, err := conn.Read(buf)
		if err != nil && err != io.EOF {
			log.Fatalf("failed to read from server: %v", err)
		}
		if n == 0 {
			break
		}
		fmt.Print(string(buf[:n]))
	}
}
