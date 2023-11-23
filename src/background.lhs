\section{Background and Problem Definition}
This section provides a brief discussion on \xfon certificate chain validation, highlighting prior works on detecting its implementation flaws, particularly logical bugs, in order to underline the motivation and challenges of this work.

\subsection{Preliminaries on \xfon Certificate Chain}
Though the \xfon standard is primarily defined in the ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use \xfon certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of different extensions.

\textbf{Internal Structure of a Certificate.} A version 3 certificate comprises three top-level fields: \texttt{TBSCertificate}, \texttt{SignatureAlgorithm}, and  \texttt{SignatureValue}. The \texttt{TBSCertificate} field contains various information, such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (\ie, subject). It also includes the public-key, the algorithm employed by the issuer for signing the certificate, and a few \emph{optional} fields like unique identifiers and a sequence of extensions, specifically for version 3 of the \xfon standard. The issuer CA signs the entire \texttt{TBSCertificate} content, generating a signature, denoted as \texttt{SignatureValue}, which is appended to the certificate's end, creating a digitally secure and tamper-proof document. The \texttt{SignatureAlgorithm} field specifies the algorithm used by the issuer CA for generating the signature.

\textbf{Overview on Certificate Chain Validation.} A certificate chain is represented as a sequence of certificates, $C_1 \rightarrow C_2 \rightarrow \ldots \rightarrow C_{n-1} \rightarrow C_n$, where $C_1$ is the root CA certificate and is inherently trusted by the validator (denoted by $T(C_1) = \text{true}$), $C_2$ to $C_{n-1}$ are intermediate CA certificates, and $C_n$ is the end-user certificate. The chain's hierarchy is depicted as each certificate $C_i$ is issued by its predecessor $C_{i-1}$ (see Figure~\ref{cert_chain}). For validating such a chain, each certificate $C_i$ undergoes parsing (denoted by $P(C_i)$) and semantic-checking (denoted by $SCP(C_i)$). While parsing enforces syntactic restrictions on different certificate fields, semantic-checking involves decoding and checking the values in a single certificate (\eg, the certificate is not expired with respect to current system time). In addition, semantic-checking on subsequent certificates in a chain (\eg, matching subject and issuer names, signature verification) is represented by a function $CCP(C_i, C_{i-1})$, which must return \emph{true} for all $i \ge 2$. Hence, the overall legitimacy of a certificate chain is denoted by the following expression.
\[
\bigwedge_{i=1}^{n} P(C_i) \land \bigwedge_{i=1}^{n} SCP(C_i) \land \bigwedge_{i=2}^{n} CCP(C_i, C_{i-1}) \land T(C_1)
\]

\begin{figure}[]
  \centering
  \scriptsize
  \includegraphics[scale=0.58]{img/cert_chain.drawio.pdf} \\
  Fields marked with * are optional \\
  \vspace{0.2cm}
  \caption{Representation of an \xfon certificate chain}
  \label{cert_chain}
  \end{figure}

\subsection{Testing Efforts to Detect Implementation Flaws}
\fuzzing\footnote{\fuzzing operates by mutating valid seed certificates to generate irregular inputs, which can reveal unexpected, potentially problematic behaviors in the implementation under scrutiny.}~\cite{frank, mucert, nezha, quan2020sadt, chen2023sbdt} and \symex\footnote{\symex systematically explores all possible paths a program could take during its execution, helping to reveal more deeply embedded logical bugs.}~\cite{rfcguided, symcert} had been shown previously as powerful tools for uncovering \emph{logical flaws} in the certificate chain validation code of many open-source TLS libraries.. While these techniques have successfully identified numerous noncompliance issues (\ie, being not compliant with respect to the standard specification), they naturally bear the risk of false negatives-- some logical flaws remain undetected, especially when those are common across all the tested implementations. In addition, they often fall short of providing any formal guarantees regarding correctness of an \xfon implementation. This is corroborated through many high impact bugs and vulnerabilities found in some widely used applications and open-source libraries over the last decade~\cite{CVE-2019-5275, CVE-2014-0161, CVE-2020-5523, CVE-2019-15604, CVE-2020-13615, CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2021-34558, CVE-2020-36477, CVE-2021-43527, CVE-2022-3602, CVE-2022-3786, CVE-2022-3996, CVE-2022-47630, CVE-2022-4203, CVE-2023-0464, CVE-2023-2650, CVE-2023-33201, CVE-2023-40012, CVE-2023-39441}. This paper aims to avoid such implementation flaws by providing a formally-verified \xfon implementation, which could serve as a benchmark standard for developing and testing other implementations, ensuring their reliability and correctness.





% \subsubsection{Certificate Chain Validation Algorithm} 
% \label{cert_val_proc}
% Certificate chain validation logic (\ie, CCVL) defines the process to verify the authenticity of a certificate chain. This CCVL involves parsing and validating each certificate in the chain, based on the restrictions primarily described in RFC 5280~\cite{cooper2008internet}. Below we briefly present some notable checks performed in the context of a client validating a server's certificate chain. \\
%     \textbf{Name Chaining Check:} The client needs to verify whether the issuer of a certificate is the same as the subject of the subsequent certificate in the chain, except the root CA certificate has the same issuer and subject name. \\
%     \textbf{Validity Period Check:} The client must verify that the current time falls inside the certificate validity period. \\
%     \textbf{Signature Verification:} Public-key of the issuer certificate must be used to verify signature on the current certificate. \\
%     \textbf{Trust Anchor Check:} The client must check whether the root CA is trusted according to its pre-defined trust anchors (\ie, set of trusted CAs). \\
%     \textbf{Hostname Verification:} The client needs to compare the hostname used to initiate the connection with the name bound in the server's certificate. \\
%     \textbf{Revocation Check:} Due to some unexpected events such as private key compromise, the issuer may revoke a certificate before its scheduled expiration date. The client should check the CRL~\cite{cooper2008internet} or use the OCSP~\cite{ocsp} protocol to verify that the certificate has not been revoked.

% While the aforementioned checks gives an overview of the certificate chain validation, the actual implementation encompasses more restrictions and steps, which we discuss in detail in the subsequent sections.


















\subsection{Goal and Challenges}
The overarching goal of this work is to \emph{design and develop a high-assurance
  reference implementation for the \xfon certificate chain validation algorithm, whose compliance with the standard is established by formal, machine-checked proofs}. This goal entails formulating a precise formal specification that aligns with the requirements of RFC 5280~\cite{cooper2008internet}, ensuring its logical consistency, developing an implementation capable of enforcing all the requirements, and, lastly, applying some formal verification techniques to confirm the implementation's adherence to the formalized specification.

  \says{joy}{should we mention here which assurances we will provide?}

% For the verification step, we aim to prove the \soundness and \completeness of
% our implementation as the top-level properties, which are 
% defined below. \todo{\footnotesize CJ: don't we prove sound, complete for parsing only, not
%   all CCVL?} \\ 
% \textbf{Soundness:} If the CCVL implementation ($I$) accepts an input certificate chain ($cc$), then the formal specification ($FS$) also accepts the certificate chain (cc). That means, $\forall cc, I(cc) \implies FS(cc)$. \\
% \textbf{Completeness:} If the formal specification ($FS$) accepts an input certificate chain ($cc$), then the CCVL implementation ($I$) also accepts the certificate chain (cc). That means, $\forall cc, FS(cc) \implies \exists I(cc)$.

% \Soundness and \completeness together ensure that an implementation behaves exactly as specified. A sound system does not produce false positives (\ie, invalid inputs presented as valid), and a complete system does not produce false negatives (\ie, valid inputs presented as invalid). Thus, these properties guarantee that the implementation will always behave as expected.


\noindent\textbf{Challenges.} We now discuss the challenges of this work.

\textit{a. Natural Language Specifications:} The \xfon specification is distributed 
across many different documents (\eg, ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet}, RFC 6125~\cite{saint2011rfc}, RFC 4158~\cite{cooper2005rfc}, RFC 2527~\cite{rfc2527}, RFC 4518~\cite{zeilenga2006lightweight}) and specified in natural language, which have been shown to suffer from inconsistencies, ambiguities, and under-specification~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}. Moreover, the specification for version 3 \xfon certificates, RFC 5280, does not only encompass rules for certificate issuers (\ie, producer rules) but also for the implementations that validate certificate chains (\eg, consumer rules). This intertwined set of rules further complicates the specification, making it challenging to determine how the \xfon implementations should respond in certain cases (\ie, whether to accept or reject an input chain).

\textit{b. Parsing Complexities:} The internal data structure of an \xfon certificate, while described in the
\emph{Abstract Syntax Notation One} (\asnone), is eventually serialized based
on the \xsno Distinguished Encoding Rules (\der)~\cite{rec2002x}. However, this \der representation of the certificate bytestream internally follows a $<T, L, V>$ structure to represent each certificate field, where $T$ denotes the
type, $V$ indicates the actual content, and $L$ signifies the length in bytes of
the $V$ field. Additionally, the $V$ field can include nested $<T, L, V>$ structures,
adding additional layers of complexity to the binary data. Parsing such a binary
data is challenging since it always requires passing the value of the $L$ field
(length) to accurately parse the subsequent $V$ field. Therefore, the internal
grammar of a \der-encoded certificate is \emph{context-sensitive}, and developing a
parser for such a grammar with \emph{correctness guarantees} is not a trivial
task~\cite{kaminsky2010pki, debnath2021re}. 

To make matters worse, parsing just the \asnone structure from the certificate bytestream 
is insufficient because the relevant certificate field value may need to be further 
decoded from the parsed \asnone value.
Take the example of the \texttt{UTCTime} format used for certificate validity
periods.
It uses a two-digit year representation, $YY$, and here lies the potential for
misinterpretation.
In this format, values from $00$ to $49$ are deemed to belong to the $21st$
century and are thus interpreted as $20YY$.
In contrast, values from $50$ to $99$ are associated with the $20th$ century and
are consequently translated into $19YY$.
This peculiarity of the \texttt{UTCTime} format allows the representation of
years from $1950$ to $2049$.
Therefore, one needs to be very careful to decode the actual value of \texttt{UTCTime}
to avoid potential certificate chain validation errors, 
a mistake previously made by MatrixSSL, axTLS, and tropicSSL~\cite{symcert}.



% To make this
% binary data more human-readable\todo{CJ: Human readable?! Isn't it to avoid
%   misinterpreting bytes as escape sequences?} and easier to debug, it is then encoded into the Privacy Enhanced Mail (\pem)~\cite{balenson1993privacy} format using \basesf encoding. Upon receiving such a certificate in the \pem format, one must reverse the whole encoding process to extract and interpret the information stored within it. Firstly, the \basesf decoding must be applied to convert the textual \pem certificate back into its original binary format. This \der-encoded binary data then needs to be parsed using a \der certificate parser, which extracts all the information from the certificate and transforms it into an intermediate representation for the subsequent semantic validation phase. This intermediate representation provides detailed information contained within a certificate and has a one-to-one correspondence with its \asnone certificate representation. Figure~\ref{encoding} shows the encoding and decoding steps of an \xfon certificate.

\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.73]{img/stages.drawio.pdf} \\
  \caption{Sequential stages for certificate chain validation}
  \label{cert_validation}
\end{figure}

% \begin{figure}[h]
%     \centering
%     \scriptsize
%     \includegraphics[scale=0.68]{img/encoding.pdf}
%     \caption{\says{joy}{redraw picture}Steps for encoding and decoding a certificate}
%     \label{encoding}
%     \end{figure}


    



\textit{c. Overall Complexities:} The \xfon certificate chain validation algorithm can be conceptually decomposed into different stages (see Figure~\ref{cert_validation}). Upon receiving a \emph{Privacy Enhanced Mail} (\pem)~\cite{balenson1993privacy} formatted certificate chain, which is internally encoded in \basesf, the \basesf decoder is used to convert the textual \pem certificate back into its original binary format (\ie, \der). This \der certificate then needs to be parsed using a \der parser into an intermediate representation for the next validation stages (see Figure~\ref{encoding}). In addition, prior to enforcing the semantic checks (\eg, expiration date checks, signature verification), as specified in RFC 5280~\cite{cooper2008internet}, a valid certification path must be constructed from the verifier's trust anchor to the end-entity certificate~\cite{cooper2005rfc}. Moreover, string canonicalization needs to be performed for each parsed certificate, which is a type of string conversion to ensure all the strings in a certificate are decoded in \emph{normalized} form~\cite{zeilenga2006lightweight}.

However, each of these validation stages present their own challenges. For example, building a valid certification path can be difficult due to the lack of concrete
directions as well as the possibility of having multiple valid certificate
chains, since a single certificate can be cross-signed by more than one CA~\cite{path}.
Similarly, converting strings to \emph{normalized} form is also a complex
process since the number of character sets is humongous considering all the
languages worldwide. Moreover, before the signature verification, the implementation needs to carefully
parse the actual contents of the \texttt{SignatureValue} field to prevent attacks based
on the \emph{RSA signature forgery}~\cite{finney2006bleichenbacher,
  bleichenbacher1998chosen}.
While these intermediate stages are conceptually straightforward, implementing
them in a robust and secure manner is a daunting task.

\says{joy}{should formal verification challenges come as 4th point?}

% \todo{CJ: We
%   should say at each step the formal guarantees we offer, \eg, no formal
%   guarantees for string prep.}



% One advantage of using the \pem format is that the sender can include its own certificate (\ie, end-entity certificate) as well as the associated issuer CA certificates in one single file. Once these certificates are parsed into their corresponding intermediate representations, the verifier must undertake a series of semantic checks, as specified in RFC 5280. However, the input CA certificates can come out-of-order or miss one or more required CA certificates to construct a valid chain. This is why prior to enforcing the semantic checks, a valid certificate chain should be constructed from the verifier's trust anchor to the end-entity certificate~\cite{path, cooper2005rfc}. In addition, . We can move to the semantic validation only after such intermediate steps.





% (\ie, PEM parsing, Base64 decoding, \asnone \der parsing, decoding \asnone values, string canonicalization, chain building, semantic rule checking, cryptographic signature verification, hostname verification, revocation checking), each of which can be complex by itself (see~\cite{path, yahyazadeh2021morpheus, pkcsndss}).

% \label{sem}
% One advantage of using the \pem format is that the server can include its own certificate as well as the associated issuer CA certificates in one single file. Once these certificates are parsed into their corresponding intermediate representations, the client application must undertake a series of semantic checks, as mentioned in Section~\ref{cert_val_proc}. However, the CA certificates can come out-of-order or miss one or more required certificates. This is why prior to enforcing the semantic checks, a valid certificate chain should be constructed from the end-entity certificate to the root CA certificate~\cite{path, cooper2005rfc}. In addition, string transformation needs to be performed for each certificate, which is a type of string conversion to ensure all the strings in a certificate are in \emph{normalized} form~\cite{zeilenga2006lightweight}. We can move to the semantic validation only after such intermediate steps. Figure~\ref{cert_validation} shows the stages for certificate chain validation.


% However, each of these intermediate steps presents challenges.
% For example, building a valid chain can be difficult due to the lack of specific
% directions as well as the possibility of having multiple valid certificate
% chains since a single certificate can be cross-signed by more than one CA.
% In addition, converting strings to \emph{normalized} form is also a complex
% process since the number of character sets is humongous considering all the
% languages worldwide.
% Finally, before signature verification, the implementation needs to carefully
% parse the contents of the \texttt{SignatureValue} field to prevent attacks based
% on the \emph{RSA signature forgery}~\cite{finney2006bleichenbacher,
%   bleichenbacher1998chosen}.
% While these intermediate steps are conceptually straightforward, implementing
% them in a robust and secure manner is a significant challenge.\todo{CJ: We
%   should say at each step the formal guarantees we offer, \eg, no formal
%   guarantees for string prep.}


% \subsubsection{Formal Verification Challenges} 
% \xfon CCVL involves cryptographic operations, particularly during signature
% verification.
% Such cryptographic operations are based on mathematical theories and are
% computationally complex, making them challenging to formally model and verify.
% In addition, guaranteeing \soundness and \completeness of the implementation
% further intensifies the task.
% \Soundness, ensuring that every certificate chain the process marks as valid is
% indeed valid according to RFC 5280 specifications, demands a comprehensive
% approach that leaves no corner case or unusual behavior unchecked, a significant
% challenge given the complexity of the \xfon standard.
% \Completeness, however, requires the system to confirm the validity of all
% genuinely valid certificate chains per RFC 5280.
% Achieving \completeness necessitates an exhaustive exploration of all potential
% valid states and configurations, a daunting endeavor given the broad parameter
% space and flexibility in the \xfon standard. 

% \subsection{Technical Insights} We now present our insights on solving the challenges of developing a formally-verified CCVL implementation.

% \subsubsection{Drawing Boundary} A clear separation between the parsing and semantic checks is pivotal in formally specifying the CCVL requirements. However, having a balance is also important-- too many semantic checks incorporated into the parsing process can lead to an overly complex parser while excluding all semantic checks during parsing can result in an overly lenient parser. Our strategy lies somewhere in the middle, taking inspiration from the re-engineering effort by Debnath \etal~\cite{debnath2021re}. Similar to that prior work, we categorize \der restrictions as part of the parsing rules, and the rest are left for semantic checks. We enforce the semantic check on \der's $<T, L, V>$ length bound into the parsing side, contributing to a manageable parser that maintains necessary rigor without becoming overly complex.

% \subsubsection{Modularity} Adopting a modular approach to implementing the \xfon CCVL can significantly mitigate some challenges. The entire process can be broken down into smaller, manageable components or modules. Each module is designed to perform a specific function, such as \der parsing, certificate chain building, string transformation, and semantic checks. Such modularization allows us to precisely specify the requirements for each module and independently establish their correctness. In addition, instead of trying to accomplish everything in a single step, this modularization allows us to undertake the validation task in multiple passes, increasing the simplicity and manageability of the overall process.

% \subsubsection{Specificity} While the \xsno \der and RFC 5280 are comprehensive and detail numerous restrictions and possibilities, in reality, not all aspects of the specifications are uniformly or widely used. For example, not all the extensions specified in the standard are used in real-world certificates. In addition, RFC 5280 puts additional restrictions on certain \der rules to be used for the Internet. Therefore, we aim to create a formally-verified reference implementation that focuses primarily on the most commonly used fragments of the standard specifications.