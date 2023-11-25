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


\subsection{Goal and Challenges}
The overarching goal of this work is to \emph{design and develop a high-assurance
  reference implementation for the \xfon certificate chain validation algorithm, whose compliance with the standard is established by formal, machine-checked proofs}. This goal entails formulating a precise formal specification that aligns with the requirements of RFC 5280~\cite{cooper2008internet}, ensuring its logical consistency, developing an implementation capable of enforcing all the requirements, and, lastly, applying some formal verification techniques to confirm the implementation's adherence to the formalized specification.

  
% \noindent\textbf{Challenges.} We now discuss the challenges of this work.

% \textit{a. Natural Language Specifications:} The \xfon specification is distributed 
% across many different documents (\eg, ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet}, RFC 6125~\cite{saint2011rfc}, RFC 4158~\cite{cooper2005rfc}, RFC 2527~\cite{rfc2527}, RFC 4518~\cite{zeilenga2006lightweight}) and specified in natural language, which have been shown to suffer from inconsistencies, ambiguities, and under-specification~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}. Moreover, the specification for version 3 \xfon certificates, RFC 5280, does not only encompass rules for certificate issuers (\ie, producer rules) but also for the implementations that validate certificate chains (\eg, consumer rules). This intertwined set of rules further complicates the specification, making it challenging to determine how the \xfon implementations should respond in certain cases (\ie, whether to accept or reject an input chain).

% \textit{b. Parsing Complexities:} The internal data structure of an \xfon certificate, while described in the
% \emph{Abstract Syntax Notation One} (\asnone), is eventually serialized based
% on the \xsno Distinguished Encoding Rules (\der)~\cite{rec2002x}. However, this \der representation of the certificate bytestream internally follows a $<T, L, V>$ structure to represent each certificate field, where $T$ denotes the
% type, $V$ indicates the actual content, and $L$ signifies the length in bytes of
% the $V$ field. Additionally, the $V$ field can include nested $<T, L, V>$ structures,
% adding additional layers of complexity to the binary data. Parsing such a binary
% data is challenging since it always requires passing the value of the $L$ field
% (length) to accurately parse the subsequent $V$ field. Therefore, the internal
% grammar of a \der-encoded certificate is \emph{context-sensitive}, and developing a
% parser for such a grammar with \emph{correctness guarantees} is not a trivial
% task~\cite{kaminsky2010pki, debnath2021re}. 

% To make matters worse, parsing just the \asnone structure from the certificate bytestream 
% is insufficient because the relevant certificate field value may need to be further 
% decoded from the parsed \asnone value.
% Take the example of the \texttt{UTCTime} format used for certificate validity
% periods.
% It uses a two-digit year representation, $YY$, and here lies the potential for
% misinterpretation.
% In this format, values from $00$ to $49$ are deemed to belong to the $21st$
% century and are thus interpreted as $20YY$.
% In contrast, values from $50$ to $99$ are associated with the $20th$ century and
% are consequently translated into $19YY$.
% This peculiarity of the \texttt{UTCTime} format allows the representation of
% years from $1950$ to $2049$.
% Therefore, one needs to be very careful to decode the actual value of \texttt{UTCTime}
% to avoid potential certificate chain validation errors, 
% a mistake previously made by MatrixSSL, axTLS, and tropicSSL~\cite{symcert}.


% \begin{figure}[h]
%   \centering
%   \scriptsize
%   \includegraphics[scale=0.73]{img/stages.drawio.pdf} \\
%   \caption{Sequential stages for certificate chain validation}
%   \label{cert_validation}
% \end{figure}



%     \textit{c. Overall Complexities:} The \xfon certificate chain validation algorithm can be conceptually decomposed into different stages (see Figure~\ref{cert_validation}). Upon receiving a \emph{Privacy Enhanced Mail} (\pem)~\cite{balenson1993privacy} formatted certificate chain, which is internally encoded in \basesf, the \basesf decoder is used to convert the textual \pem certificate back into its original binary format (\ie, \der). This \der certificate then needs to be parsed using a \der parser into an intermediate representation for the next validation stages (see Figure~\ref{encoding}). In addition, prior to enforcing the semantic checks (\eg, expiration date checks, signature verification), as specified in RFC 5280~\cite{cooper2008internet}, a valid certification path must be constructed from the verifier's trust anchor to the end-entity certificate~\cite{cooper2005rfc}. Moreover, string canonicalization needs to be performed for each parsed certificate, which is a type of string conversion to ensure all the strings in a certificate are decoded in \emph{normalized} form~\cite{zeilenga2006lightweight}.

% However, each of these validation stages present their own challenges. For example, building a valid certification path can be difficult due to the lack of concrete
% directions as well as the possibility of having multiple valid certificate
% chains, since a single certificate can be cross-signed by more than one CA~\cite{path}.
% Similarly, converting strings to \emph{normalized} form is also a complex
% process since the number of character sets is humongous considering all the
% languages worldwide. Moreover, before the signature verification, the implementation needs to carefully
% parse the actual contents of the \texttt{SignatureValue} field to prevent attacks based
% on the \emph{RSA signature forgery}~\cite{finney2006bleichenbacher,
%   bleichenbacher1998chosen}.
% While these intermediate stages are conceptually straightforward, implementing
% them in a robust and secure manner is a daunting task.










% \subsubsection{Modularity} Adopting a modular approach to implementing the \xfon CCVL can significantly mitigate some challenges. The entire process can be broken down into smaller, manageable components or modules. Each module is designed to perform a specific function, such as \der parsing, certificate chain building, string transformation, and semantic checks. Such modularization allows us to precisely specify the requirements for each module and independently establish their correctness. In addition, instead of trying to accomplish everything in a single step, this modularization allows us to undertake the validation task in multiple passes, increasing the simplicity and manageability of the overall process.

