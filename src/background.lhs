\section{Background and Problem Definition}
In this section, we first present a brief introduction to X.509 certificates and their validation logic. We then present our objective of this paper and the related technical challenges, with our insights to address them.

\subsection{Preliminaries on X.509 Certificate}
X.509 certificate is a digitally signed document that binds a public key to a specific identity to assure that the certificate holder is indeed the entity it claims to be. Though the X.509 standard is primarily defined in the X.509 ITU-T Recommendation~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use X.509 certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of Certificate Revocation List (CRL) and extensions.

\subsubsection{Certificate Structure} An X.509 certificate comprises three top-level fields: \texttt{TbsCertificate}, \texttt{SignatureAlgorithm}, and  \texttt{SignatureValue}, as shown in Figure~\ref{cert_chain}. The \texttt{TbsCertificate} field contains various information, such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (i.e., subject). It also includes the public key, the algorithm employed by the issuer for signing the certificate, and a few optional fields like unique identifiers and a sequence of extensions, specifically for version 3 of the X.509 standard. The issuer signs the entire \texttt{TbsCertificate} content, generating a signature, denoted as \texttt{SignatureValue}, which is appended to the certificate's end, creating a digitally secure and tamper-proof document. The \texttt{SignatureAlgorithm} field specifies the algorithm used by the certificate issuer or signer for generating the signature.

\subsubsection{Certificate Chain} A certificate chain, also known as a certification path, is a sequence of X.509 certificates originating from an end-entity certificate (the one being authenticated) and ending with a root CA certificate. This chain is based on the concept of trust transitivity that means if Certificate A is trusted by Certificate B and Certificate B is trusted by Certificate C, then Certificate A is inherently trusted by Certificate C. Each certificate in the chain is signed by the owner of the subsequent certificate, and the process continues until reaching the root certificate. This root certificate is a self-signed certificate issued by a trusted CA, which forms the root of trust in the X.509 PKI.

\begin{figure*}[h]
\centering
\scriptsize
\includegraphics[scale=0.8]{img/cert_chain.pdf}
\caption{Typical structures of X.509 certificate and certificate chain}
\label{cert_chain}
\end{figure*}

\subsubsection{Certificate Chain Validation Logic} Certificate chain validation logic (CCVL) defines the process to verify the authenticity of a certificate chain. This CCVL involves parsing and validating each certificate in the chain, based on the restrictions primarily described in RFC 5280~\cite{cooper2008internet}. Below we present the notable checks performed in the context of a client validating the certificate chain received from a server.

    \textbf{Name Chaining Check:} The client needs to verify whether the issuer of a certificate is the same as the subject of the subsequent certificate in the chain, except the root CA certificate has the same issuer and subject name.
    
    \textbf{Validity Period Check:} The client must verify that the current time falls inside the certificate validity period.

    \textbf{Signature Verification:} The client must use the public key of the issuer certificate to verify the digital signature on the current certificate.

    \textbf{Trust Anchor Check:} It is required to check whether the client trusts the root CA. That means whether the root CA is part of the client's trust anchors.

    \textbf{Hostname Verification:} The client needs to compare the hostname used to initiate the connection with the name bound in the server's certificate.

    \textbf{Revocation Check:} Due to unexpected events such as private key compromise, the issuer can revoke a certificate before its scheduled expiration date. The client should check the Certificate Revocation List (CRL) or use the Online Certificate Status Protocol (OCSP) to ensure the certificate has not been revoked.

While the aforementioned checks give an overview of certificate validation process, it is crucial to understand that the actual CCVL implementation encompasses several additional constraints during both the parsing and semantic validation phases.



\subsection{Overarching Objective}
The overarching objective of this work is to develop a formally verified RFC 5280-compliant reference implementation for the X.509 CCVL. This goal entails formulating a precise formal specification that aligns with the requirements of RFC 5280, ensuring its logical consistency, developing a system capable of executing all the required security policy checks, and, importantly, applying formal verification techniques to confirm the system's adherence to the established specifications. The fulfillment of these sequential steps would result in a reliable implementation for X.509 certificate chain validation, offering high confidence in its operational correctness and resilience against security vulnerabilities.

\subsection{Technical Challenges}
There are several challenges to our work. In general, interpreting the RFC 5280 specification, which is written in natural language (English), presents a significant challenge due to its inherent inconsistencies, ambiguities, and potential for misinterpretation. Prior studies have also identified these issues, pointing out several problematic clauses in RFC 5280~\cite{debnath2021re}. For instance, there are discrepancies regarding the allowed range of values for certificate serial numbers and ambiguities in the structure of the CRL Distribution Point extension. Moreover, RFC 5280 does not only encompass rules for certificate issuers but also for the applications that validate certificates. This intertwined set of rules further complicates the specification, making it challenging to determine how client-side CCVL implementations should respond-- whether to accept or reject a certificate chain. There are additional challenges that we describe below.

\subsubsection{Parsing Challenges} The internal data structure of an X.509 certificate, while described in the ASN.1 notation~\cite{}, is eventually serialized based on the X.690 Distinguished Encoding Rules (DER)~\cite{}. To make this binary data more human-readable and easier to debug, it is then encoded into the Privacy Enhanced Mail (PEM)~\cite{} format using base64 encoding. Upon receiving such a certificate in the PEM format, one must reverse this process to extract and interpret the information stored within. Firstly, the base64 decoding must be applied to convert the textual PEM certificate back into its original binary format. This DER-encoded binary data then needs to be parsed using a DER certificate parser, which extracts all the information from the certificate and transforms it into an intermediate representation for processing the certificate data during subsequent semantic validation phase. Figure~\ref{encoding} clearly shows the encoding and decoding steps of an X.509 certificate.

\begin{figure}[h]
    \centering
    \scriptsize
    \includegraphics[scale=0.68]{img/encoding.pdf}
    \caption{Steps for encoding and decoding a certificate}
    \label{encoding}
    \end{figure}

However, this DER representation of the certificate internally follows a $<T, L, V>$ structure to represent each certificate field, where $T$ denotes the type, $V$ indicates the actual content, and $L$ signifies the length of the $V$ field. Additionally, the $V$ field can include nested $<T, L, V>$ structures, adding additional layers of complexity to the binary data. Parsing such a binary data is challenging since it always requires passing the value of the $L$ field (length) to accurately parse the subsequent $V$ field. In other words, the internal grammar an of DER-encoded certificate is context-sensitive, and developing an error-free parser for such a context-sensitive language is generally a complex task.

After parsing, correctly interpreting the values of a certificate field is also crucial. Take the example of the UTCTime format used in RFC 5280 for certificate validity periods. It uses a two-digit year representation, YY, and here lies the potential for misinterpretation. In this format, values from 00 to 49 are deemed to belong to the 21st century and are thus interpreted as 20YY. On the other hand, values from 50 to 99 are associated with the 20th century and are consequently translated into 19YY. This peculiarity of the UTCTime format allows the representation of years from 1950 to 2049. Therefore, when constructing a valid internal representation of a certificate, the decoder must correctly interpret this two-digit year to avoid potential validation errors, especially for certificates that are valid over long periods or those straddling centuries. Misinterpretation of these values could lead to incorrect conclusions about a certificate's validity and, ultimately, compromise the overall integrity of the validation process.

\subsubsection{Semantic Validation Challenges} 
Once the certificates have been parsed into intermediate representations, client applications must undertake a series of steps to authenticate the parsed certificates. Initially, a valid certification path should be constructed from the end-user certificate to the root CA certificate. Following this, string canonicalization is performed, a type of string transformation to ensure that all the strings in the certificate are in a normalized form. After these initial stages, the process moves onto semantic validation, a more in-depth verification procedure, where, several checks are performed, such as signature verification, trust anchor check, and certificate validity period check. Following all the required semantic checks, the application can make an informed decision regarding accepting or rejecting the certificate chain. 

However, each of these steps presents challenges. For example, building a valid chain can be difficult as there can be multiple paths, circular paths, or missed certificates. Converting strings to normalized format is also a complex process since the number of character sets is humongous considering all the languages worldwide. In addition, prior to Signature verification, one needs to carefully parse the contents of the Signature field again to prevent attacks based on a signature forgery. Therefore, while these steps are conceptually straightforward, implementing them in a robust, secure, and efficient manner is a significant challenge.

\subsubsection{Formal Verification Challenges} 
X.509 CCVL involves cryptographic operations, including public key operations and digital signature verification. These operations are based on mathematical theories and are computationally complex, making them challenging to formally model and verify. In addition, guaranteeing soundness and completeness of the CCVL implementation further intensifies the task. Soundness, ensuring that every certificate chain the process marks as valid is indeed valid according to RFC 5280 specifications, demands a comprehensive approach that leaves no corner case or unusual behavior unchecked, a significant challenge given the complexity of the X.509 standard. Completeness, however, requires the system to confirm the validity of all genuinely valid certificate chains per RFC 5280. Achieving this necessitates an exhaustive exploration of all potential valid states and configurations, a daunting endeavor given the broad parameter space and potential variations in X.509 certificates, chains, and cryptographic procedures.

\subsection{Our Insights} Now, we briefly present our insights on addressing the challenges of developing a formally verified CCVL implementation.

\subsubsection{Drawing Boundary} Drawing a clear boundary between the parsing and semantic rules is pivotal in formally verifying X.509 CCVL. However, having a balance is also vital; too many semantic checks incorporated into the parsing process can lead to an overly complex parser while excluding all semantic checks can result in an overly lenient parser. Our strategy lies somewhere in the middle, taking inspiration from the reengineering work by Debath et al. We categorize DER-related rules (including length bound check) as part of the parsing rules, and the rest are left for semantic checks. This approach contributes to a more manageable parser that maintains necessary rigor without becoming overly complex. [Example]

\subsubsection{Moudlarity} Adopting a modular approach to implementing the X.509 CCVL can significantly mitigate some of these challenges. The entire process can be broken down into smaller, manageable components or modules. Each module is designed to perform a specific function, such as DER parsing, certificate chain construction, string canonicalization, and semantic checks. Such modularization allows us to precisely specify the requirements for each module and independently establish their correctness. In addition, instead of trying to accomplish everything in a single step, this modularization allows us to undertake the validation task in multiple passes, increasing the simplicity and manageability of the overall process.

\subsubsection{Specificity} ??