import javax.net.ssl.*;
import java.io.*;
import java.net.Socket;
import java.security.cert.*;
import java.security.*;
import java.util.Collections;
import java.io.FileInputStream;
import java.io.BufferedInputStream;
import java.security.cert.*;
import java.util.*;

public class sun_client {
    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.out.println("Usage: java TlsClientWithCRL <host> <port> <ca_cert.pem> <crl.pem>");
            return;
        }

        String host = args[0];
        int port = Integer.parseInt(args[1]);
        String caPath = args[2];
        String crlPath = args[3];

        CertificateFactory cf = CertificateFactory.getInstance("X.509");

        // Read and load CA certificates into TrustAnchor set
        Set<TrustAnchor> trustAnchors = new HashSet<>();
        try (FileInputStream caStream = new FileInputStream(caPath);
             BufferedInputStream caBuffer = new BufferedInputStream(caStream)) {
            while (caBuffer.available() > 0) {
                X509Certificate caCert = (X509Certificate) cf.generateCertificate(caBuffer);
                trustAnchors.add(new TrustAnchor(caCert, null));
            }
        }

        if (trustAnchors.isEmpty()) {
            System.out.println("0 - No valid CA certificates found.");
            System.exit(0);
        }


        // Set up validation parameters
        PKIXBuilderParameters pkixParams = new PKIXBuilderParameters(trustAnchors, null);
        pkixParams.setRevocationEnabled(true); // Enable CRL checking only if provided

        // Add CRLs if provided
        if (crlPath != null) {
            try {
                Set<CRL> crls = new HashSet<>();
                try (FileInputStream crlStream = new FileInputStream(crlPath);
                    BufferedInputStream crlBuffer = new BufferedInputStream(crlStream)) {
                    while (crlBuffer.available() > 0) {
                        X509CRL crl = (X509CRL) cf.generateCRL(crlBuffer);
                        crls.add(crl);
                    }
                }

                if (!crls.isEmpty()) {
                    CertStore crlStore = CertStore.getInstance("Collection",
                            new CollectionCertStoreParameters(crls));
                    pkixParams.addCertStore(crlStore);
                } else {
                    System.out.println("0 - No valid CRLs found in the CRL file.");
                    System.exit(0);
                }
            } catch (Exception crlException) {
                System.out.println("0 - Error processing CRL: " + crlException.getMessage());
                System.exit(0);
            }
        }

        // Set up TrustManager using PKIX algorithm
        TrustManagerFactory tmf = TrustManagerFactory.getInstance("PKIX");
        tmf.init(new CertPathTrustManagerParameters(pkixParams));

        // Initialize SSLContext with the TrustManager
        SSLContext sslContext = SSLContext.getInstance("TLS");
        sslContext.init(null, tmf.getTrustManagers(), null);

        // Connect using SSLSocket
        SSLSocketFactory factory = sslContext.getSocketFactory();
        SSLSocket socket = (SSLSocket) factory.createSocket(host, port);

        System.out.println("Starting TLS handshake...");
        socket.startHandshake();
        System.out.println("TLS handshake successful (with CRL validation)");

        // Optional: send basic HTTP request
        BufferedWriter out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        out.write("GET / HTTP/1.1\r\nHost: " + host + "\r\n\r\n");
        out.flush();

        BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        String line;
        while ((line = in.readLine()) != null) {
            System.out.println(line);
        }

        socket.close();
    }
}
