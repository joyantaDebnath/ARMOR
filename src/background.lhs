\section{Background and Problem Definition}
In this section, we first present a brief introduction to X.509 certificates and their validation logic. We then present our objective of this paper and the related technical challenges, with our insights to address them.

\subsection{Preliminaries on X.509 Certificate}
X.509 certificate is a digitally signed document that binds a public key to a specific identity to assure that the certificate holder is indeed the entity it claims to be. Though the X.509 standard is primarily defined in the X.509 ITU-T Recommendation~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use X.509 certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of Certificate Revocation List (CRL) and extensions.

\subsubsection{Structure of a Certificate} An X.509 certificate comprises three top-level fields: \texttt{TbsCertificate}, \texttt{SignatureAlgorithm}, and  \texttt{SignatureValue}, as shown in Figure~\ref{cert_chain}. The \texttt{TbsCertificate} field contains various information, such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (i.e., subject). It also includes the public key, the algorithm employed by the issuer for signing the certificate, and a few optional fields like unique identifiers and a sequence of extensions, specifically for version 3 of the X.509 standard. The issuer signs the entire \texttt{TbsCertificate} content, generating a signature, denoted as \texttt{SignatureValue}, which is appended to the certificate's end, creating a digitally secure and tamper-proof document. The \texttt{SignatureAlgorithm} field specifies the algorithm used by the certificate issuer or signer for generating the signature.

\subsubsection{Certificate Chain} A certificate chain, also known as a certification path, is a sequence of X.509 certificates originating from an end-entity certificate (the one being authenticated) and ending with a root CA certificate. This chain is based on the concept of trust transitivity that means if Certificate A is trusted by Certificate B and Certificate B is trusted by Certificate C, then Certificate A is inherently trusted by Certificate C. Each certificate in the chain is signed by the owner of the subsequent certificate, and the process continues until reaching the root certificate. These root certificates are self-signed certificates issued by trusted CAs, which form the root of trust in the X.509 ecosystem.

\begin{figure}[h]
\centering
\scriptsize
\includegraphics[scale=0.5]{img/cert_chain.pdf} \\
Fields marked with * are optional \\
\vspace{0.2cm}
\caption{Graphical representation of X.509 certificate chain}
\label{cert_chain}
\end{figure}

\subsubsection{Certificate Chain Validation Process} 
\label{cert_val_proc}
Certificate chain validation logic (CCVL) defines the process to verify the authenticity of a certificate chain. This CCVL involves parsing and validating each certificate in the chain, based on the restrictions primarily described in RFC 5280~\cite{cooper2008internet}. Below we briefly present some notable checks performed in the context of a client validating a server's certificate chain. \\
    \textbf{Name Chaining Check:} The client needs to verify whether the issuer of a certificate is the same as the subject of the subsequent certificate in the chain, except the root CA certificate has the same issuer and subject name. \\
    \textbf{Validity Period Check:} The client must verify that the current time falls inside the certificate validity period. \\
    \textbf{Signature Verification:} Public key of the issuer certificate must be used to verify signature on the current certificate. \\
    \textbf{Trust Anchor Check:} The client must check whether the root CA is trusted according to its pre-defined trust anchors. \\
    \textbf{Hostname Verification:} The client needs to compare the hostname used to initiate the connection with the name bound in the server's certificate. \\
    \textbf{Revocation Check:} Due to some unexpected events such as private key compromise, the issuer may revoke a certificate before its scheduled expiration date. The client should check the CRL~\cite{cooper2008internet} or use the OCSP~\cite{ocsp} protocol to verify that the certificate has not been revoked.

While the aforementioned checks gives an overview of the certificate chain validation, the actual implementation encompasses more restrictions and steps, which we discuss in detail in the subsequent sections.

\subsection{Our Objective}
The overarching objective of this work is to develop a formally verified reference implementation for the X.509 CCVL. This goal entails formulating a precise formal specification that aligns with the requirements of RFC 5280, ensuring its logical consistency, developing an implementation capable of enforcing all the requirements, and, lastly, applying some formal verification techniques to confirm the implementation's adherence to the formalized specification. For the verification step, we aim to prove the soundness and completeness of our implementation as the top-level properties, which are defined below. \\
\textbf{Soundness:} If the CCVL implementation ($I$) accepts an input certificate chain ($cc$), then the formal specification ($FS$) also accepts the certificate chain (cc). That means, $\forall cc, I(cc) \implies FS(cc)$. \\
\textbf{Completeness:} If the formal specification ($FS$) accepts an input certificate chain ($cc$), then the CCVL implementation ($I$) also accepts the certificate chain (cc). That means, $\forall cc, FS(cc) \implies \exists I(cc)$.

Soundness and completeness together ensure that an implementation behaves exactly as specified. A sound system does not produce false positives (invalid inputs presented as valid), and a complete system does not produce false negatives (valid inputs presented as invalid). Thus, these properties guarantee that the implementation will always behave as expected.


\subsection{Technical Challenges}
There are several challenges to our work. In general, interpreting the RFC 5280 specification, which is written in natural language (English), presents a significant challenge due to its inherent inconsistencies, ambiguities, and potential for misinterpretation. Prior studies have also identified these issues~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}, pointing out several problematic clauses in RFC 5280. Moreover, RFC 5280 does not only encompass rules for certificate issuers but also for the applications that validate certificates. This intertwined set of rules further complicates the specification, making it challenging to determine how the CCVL implementations should respond in certain cases (whether to accept or reject an input). We now describe additional challenges specific to parsing, semantic checks, and formal verification.


\subsubsection{Parsing Challenges} 
\label{parse}
The internal data structure of an X.509 certificate, while described in the Abstract Syntax Notation One (ASN.1), is eventually serialized based on the X.690 Distinguished Encoding Rules (DER)~\cite{rec2002x}. To make this binary data more human-readable and easier to debug, it is then encoded into the Privacy Enhanced Mail (PEM)~\cite{balenson1993privacy} format using base64 encoding. Upon receiving such a certificate in the PEM format, one must reverse the whole encoding process to extract and interpret the information stored within it. Firstly, the base64 decoding must be applied to convert the textual PEM certificate back into its original binary format. This DER-encoded binary data then needs to be parsed using a DER certificate parser, which extracts all the information from the certificate and transforms it into an intermediate representation for the subsequent semantic validation phase. This intermediate representation provides detailed information contained within a certificate and has a one-to-one correspondence with its ASN.1 certificate representation. Figure~\ref{encoding} clearly shows the encoding and decoding steps of an X.509 certificate.

\begin{figure}[h]
    \centering
    \scriptsize
    \includegraphics[scale=0.68]{img/encoding.pdf}
    \caption{Steps for encoding and decoding a certificate}
    \label{encoding}
    \end{figure}

However, this DER representation of the certificate internally follows a $<T, L, V>$ structure to represent each certificate field, where $T$ denotes the type, $V$ indicates the actual content, and $L$ signifies the length of the $V$ field. Additionally, the $V$ field can include nested $<T, L, V>$ structures, adding additional layers of complexity to the binary data. Parsing such a binary data is challenging since it always requires passing the value of the $L$ field (length) to accurately parse the subsequent $V$ field. Therefore, the internal grammar an of DER-encoded certificate is context-sensitive, and developing a parser for such a context-sensitive language is generally a complex task~\cite{kaminsky2010pki, debnath2021re}.

In some cases, the parsing process also involves correctly interpreting the parsed data. Take the example of the UTCTime format used for certificate validity periods. It uses a two-digit year representation, $YY$, and here lies the potential for misinterpretation. In this format, values from $00$ to $49$ are deemed to belong to the 21st century and are thus interpreted as $20YY$. In contrast, values from $50$ to $99$ are associated with the 20th century and are consequently translated into $19YY$. This peculiarity of the UTCTime format allows the representation of years from $1950$ to $2049$. Therefore, when constructing a valid internal representation of a certificate, the DER parser must correctly interpret this two-digit year to avoid potential validation errors.

\subsubsection{Semantic Validation Challenges} 
\label{sem}
One advantage of using the PEM format is that the server can include its own certificate as well as the associated issuer CA certificates in one single file. Once these certificates are parsed into their corresponding intermediate representations, the client application must undertake a series of semantic checks, as mentioned in Section~\ref{cert_val_proc}. However, the CA certificates can come out-of-order or miss one or more required certificates. This is why prior to enforcing the semantic checks, a valid certificate chain should be constructed from the end-entity certificate to the root CA certificate. In addition, string canonicalization needs to be performed for each certificate, which is a type of string transformation to ensure ll the strings in a certificate are in normalized form. We can move to the semantic validation only after such intermediate steps. Figure~\ref{cert_validation} shows the stages for certificate chain validation.

\begin{figure}[h]
    \centering
    \scriptsize
    \includegraphics[scale=0.7]{img/cert_validation.pdf} \\
    \caption{Sequential stages for certificate chain validation}
    \label{cert_validation}
    \end{figure}

However, each of these intermediate steps presents challenges. For example, building a valid chain can be difficult due to the lack of specific directions as well as the possibility of having multiple valid certificate chains since a single certificate can be cross-signed by more than one CA. In addition, converting strings to normalized form is also a complex process since the number of character sets is humongous considering all the languages worldwide. Finally, before signature verification, the implementation needs to carefully parse the contents of the \texttt{SignatureValue} field to prevent attacks based on the RSA signature forgery~\cite{finney2006bleichenbacher, bleichenbacher1998chosen}. While these intermediate steps are conceptually straightforward, implementing them in a robust and secure manner is a significant challenge.


\subsubsection{Formal Verification Challenges} 
X.509 CCVL involves cryptographic operations, particularly during signature verification. Such cryptographic operations are based on mathematical theories and are computationally complex, making them challenging to formally model and verify. In addition, guaranteeing soundness and completeness of the implementation further intensifies the task. Soundness, ensuring that every certificate chain the process marks as valid is indeed valid according to RFC 5280 specifications, demands a comprehensive approach that leaves no corner case or unusual behavior unchecked, a significant challenge given the complexity of the X.509 standard. Completeness, however, requires the system to confirm the validity of all genuinely valid certificate chains per RFC 5280. Achieving completeness necessitates an exhaustive exploration of all potential valid states and configurations, a daunting endeavor given the broad parameter space and flexibility in the X.509 standard.

\subsection{Technical Insights} We now present our insights on solving the challenges of developing a formally verified CCVL implementation.

\subsubsection{Drawing Boundary} A clear separation between the parsing and semantic checks is pivotal in formally specifying the CCVL requirements. However, having a balance is also important-- too many semantic checks incorporated into the parsing process can lead to an overly complex parser while excluding all semantic checks during parsing can result in an overly lenient parser. Our strategy lies somewhere in the middle, taking inspiration from the reengineering effort by Debath et al~\cite{debnath2021re}. Similar to that prior work, we categorize DER restrictions as part of the parsing rules, and the rest are left for semantic checks. We enforce the semantic check on DER's $<T, L, V>$ length boundness into the parsing side, contributing to a manageable parser that maintains necessary rigor without becoming overly complex.

\subsubsection{Moudlarity} Adopting a modular approach to implementing the X.509 CCVL can significantly mitigate some challenges. The entire process can be broken down into smaller, manageable components or modules. Each module is designed to perform a specific function, such as DER parsing, certificate chain building, string canonicalization, and semantic checks. Such modularization allows us to precisely specify the requirements for each module and independently establish their correctness. In addition, instead of trying to accomplish everything in a single step, this modularization allows us to undertake the validation task in multiple passes, increasing the simplicity and manageability of the overall process.

\subsubsection{Specificity} While the RFC 5280 is comprehensive and details numerous possibilities and extensions, in reality, not all aspects of the RFC are uniformly or widely used. Therefore, we aim to create a formally verified reference implementation that focuses primarily on the most commonly used fragments of the RFC 5280.