import javax.net.ssl.*;
import java.io.*;
import java.net.Socket;
import java.security.*;
import java.security.cert.*;
import java.util.*;

import org.bouncycastle.jce.provider.BouncyCastleProvider;

public class bouncy_client {
    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.out.println("Usage: java bouncy_client <host> <port> <ca_cert.pem> <crl.pem>");
            return;
        }

        // Register Bouncy Castle as a provider
        Security.addProvider(new BouncyCastleProvider());

        String host = args[0];
        int port = Integer.parseInt(args[1]);
        String caPath = args[2];
        String crlPath = args[3];

        CertificateFactory cf = CertificateFactory.getInstance("X.509", "BC");

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
            System.err.println("No valid CA certificates found.");
            System.exit(1);
        }

        // Required: non-null CertSelector for PKIXBuilderParameters
        X509CertSelector certSelector = new X509CertSelector();

        // Set up PKIX parameters
        PKIXBuilderParameters pkixParams = new PKIXBuilderParameters(trustAnchors, certSelector);
        pkixParams.setRevocationEnabled(true); // Enable CRL checking

        // Load and add CRLs
        Set<CRL> crls = new HashSet<>();
        try (FileInputStream crlStream = new FileInputStream(crlPath);
             BufferedInputStream crlBuffer = new BufferedInputStream(crlStream)) {
            while (crlBuffer.available() > 0) {
                X509CRL crl = (X509CRL) cf.generateCRL(crlBuffer);
                crls.add(crl);
            }
        }

        if (crls.isEmpty()) {
            System.err.println("No valid CRLs found in the CRL file.");
            System.exit(1);
        }

        CertStore crlStore = CertStore.getInstance("Collection",
                new CollectionCertStoreParameters(crls), "BC");
        pkixParams.addCertStore(crlStore);

        // Set up TrustManagerFactory with PKIX algorithm
        TrustManagerFactory tmf = TrustManagerFactory.getInstance("PKIX");
        tmf.init(new CertPathTrustManagerParameters(pkixParams));

        // Initialize SSLContext with the TrustManager
        SSLContext sslContext = SSLContext.getInstance("TLS");
        sslContext.init(null, tmf.getTrustManagers(), null);

        // Create and connect SSL socket
        SSLSocketFactory factory = sslContext.getSocketFactory();
        SSLSocket socket = (SSLSocket) factory.createSocket(host, port);

        System.out.println("Starting TLS handshake...");
        socket.startHandshake();
        System.out.println("TLS handshake successful (with CRL validation)");

        // Optional: Send a simple HTTP request
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
