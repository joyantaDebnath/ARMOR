import java.io.FileInputStream;
import java.io.BufferedInputStream;
import java.security.Security;
import java.security.cert.*;
import java.util.*;

import org.bouncycastle.jce.provider.BouncyCastleProvider;

public class test_verify {
    public static void main(String[] args) {
        if (args.length < 2) {
            System.out.println("0 - Usage: java VerifyCertificateBC <Certificate Chain file> <Trusted CA file> [CRL file]");
            System.exit(0);
        }

        // Register Bouncy Castle as the security provider
        Security.addProvider(new BouncyCastleProvider());

        String chainPath = args[0];
        String caPath = args[1];
        String crlPath = (args.length > 2) ? args[2] : null;

        try {
            CertificateFactory cf = CertificateFactory.getInstance("X.509", "BC");

            // Load CA certificates into TrustAnchor set
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

            // Read the certificate chain (Leaf + intermediates)
            List<X509Certificate> certChain = new ArrayList<>();
            try (FileInputStream chainStream = new FileInputStream(chainPath);
                 BufferedInputStream chainBuffer = new BufferedInputStream(chainStream)) {
                while (chainBuffer.available() > 0) {
                    X509Certificate cert = (X509Certificate) cf.generateCertificate(chainBuffer);
                    certChain.add(cert);
                }
            }

            if (certChain.isEmpty()) {
                System.out.println("0 - No valid certificates found in the chain file.");
                System.exit(0);
            }

            CertPath certPath = cf.generateCertPath(certChain);

            // Set up validation parameters
            CertPathValidator cpv = CertPathValidator.getInstance("PKIX", "BC");
            PKIXParameters pkixParams = new PKIXParameters(trustAnchors);
            pkixParams.setRevocationEnabled(crlPath != null); // Enable CRL checking only if provided

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
                                new CollectionCertStoreParameters(crls), "BC");
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

            // Check for Server Authentication (OID: 1.3.6.1.5.5.7.3.1)
            X509Certificate leafCert = certChain.get(0);
            try {
                List<String> keyUsages = leafCert.getExtendedKeyUsage();
                if (keyUsages == null || !keyUsages.contains("1.3.6.1.5.5.7.3.1")) {
                    System.out.println("0 - Certificate is not valid for server authentication.");
                    System.exit(0);
                }
            } catch (Exception ex) {
                System.out.println("0 - Error checking certificate key usage: " + ex.getMessage());
                System.exit(0);
            }

            // Set target certificate constraints
            X509CertSelector targetConstraints = new X509CertSelector();
            targetConstraints.setCertificate(leafCert);
            pkixParams.setTargetCertConstraints(targetConstraints);

            // Validate the certificate chain
            cpv.validate(certPath, pkixParams);
            System.out.println("1"); // Success
            System.exit(1);
        } catch (CertPathValidatorException e) {
            System.out.println("0 - Validation failed: " + e.getMessage());
        } catch (CertificateException e) {
            System.out.println("0 - Certificate error: " + e.getMessage());
        } catch (Exception e) {
            System.out.println("0 - Unexpected error: " + e.getMessage());
        }
        System.exit(0);
    }
}