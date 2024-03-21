import java.io.FileInputStream;
import java.io.BufferedInputStream;
import java.util.Set;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;
import java.lang.System;
import java.security.Security;
import java.security.cert.*;
import java.util.Arrays;
import java.util.Collections;
import org.bouncycastle.jce.provider.BouncyCastleProvider;

/*
 *  how to compile: javac -cp bcprov-jdk18on-171.jar verify.java
 *  how to run: (e.g.) java -cp ";bcprov-jdk18on-171.jar;." verify ca.pem leaf.pem
 *  in linux-like system, the delimiter should be ":", e.g., java -cp ":bcprov-jdk18on-171.jar:." verify ca.pem leaf.pem
 */

public class test_verify {
    public static void main(String[] args) {
        Security.addProvider(new BouncyCastleProvider());   // add provider

        String caPath = args[0];
        String entityPath = args[1];

        try{
            CertificateFactory cf = CertificateFactory.getInstance("X.509", "BC");

            // read ca certs
            FileInputStream caStream = new FileInputStream(caPath);
            BufferedInputStream caBuffer = new BufferedInputStream(caStream);
            X509Certificate x509Cert;
            // create trust anchor set
            Set<TrustAnchor> trustAnchor = new HashSet<TrustAnchor>();

            while ( caBuffer.available() > 0 ) {
                x509Cert = (X509Certificate) cf.generateCertificate(caBuffer);
                // System.out.println(x509Cert);
                trustAnchor.add(new TrustAnchor(x509Cert, null));
            }
            caBuffer.close();
            caStream.close();


            // read ee cert
            X509Certificate entityCert = (X509Certificate) cf.generateCertificate(new FileInputStream(entityPath));
            
            // create an array of certs
            List<X509Certificate> ee = new ArrayList<X509Certificate>();
            FileInputStream eeStream = new FileInputStream(entityPath);
            BufferedInputStream eeBuffer = new BufferedInputStream(eeStream);
            while ( eeBuffer.available() > 0 ) {
                x509Cert = (X509Certificate) cf.generateCertificate(eeBuffer);
                // System.out.println(x509Cert);
                ee.add(x509Cert);
            }
            eeBuffer.close();
            eeStream.close();

            CertPath cp = cf.generateCertPath(ee);
            // CertPath cp = cf.generateCertPath(Arrays.asList(
            //         new X509Certificate[] { entityCert }
            // ));

            
            CertPathValidator cpv = CertPathValidator.getInstance("PKIX", "BC");
            // PKIXParameters pkixParams = new PKIXParameters(
            //         Collections.singleton(trustAnchor)
            // );
            PKIXParameters pkixParams = new PKIXParameters(trustAnchor);
            pkixParams.setRevocationEnabled(false);
            // Create a certificate selector with the desired purpose
            X509CertSelector targetConstraints = new X509CertSelector();
            targetConstraints.setExtendedKeyUsage(Collections.singleton("1.3.6.1.5.5.7.3.1")); // "serverAuth"
            pkixParams.setTargetCertConstraints(targetConstraints);
//            System.out.println(cpv.getProvider());
            try {
                cpv.validate(cp, pkixParams);
                System.out.println("success");
                System.exit(0);
            } catch (Exception e) {
                System.out.println("failed");
                System.out.println(e);
                System.exit(-1);
            }
        } catch (Exception e) {
            System.out.println("failed");
            System.out.println(e);
            System.exit(-1);
        }
    }
}