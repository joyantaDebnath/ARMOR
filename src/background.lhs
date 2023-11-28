\section{Background and Problem Definition}
This section provides a brief discussion on \xfon certificate chain validation,
highlighting prior works on testing open-source \xfon implementations and
emphasizing the motivation for our work.

\subsection{Preliminaries on \xfon Certificate Chain}
Though the \xfon standard is primarily defined in the ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use \xfon certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of different extensions, which is the focus of this work.

\textbf{Internal Structure of a Certificate.} A version 3 certificate comprises three top-level fields: \texttt{TBSCertificate}, \texttt{SignatureAlgorithm}, and  \texttt{SignatureValue}. The \texttt{TBSCertificate} field contains information such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (\ie, subject). It also includes the public-key, the algorithm employed by the issuer for signing the certificate, and a few \emph{optional} fields like unique identifiers and a sequence of extensions, specifically for version 3 of the \xfon standard. The issuer CA signs the entire \texttt{TBSCertificate} content, generating a signature, denoted as \texttt{SignatureValue}, which is appended to the certificate's end, creating a digitally secure and tamper-proof document. The \texttt{SignatureAlgorithm} field specifies the algorithm used by the issuer CA for generating the signature.

\textbf{Overview on Certificate Chain Validation.} Without loss of generality, a certificate chain is
represented as a sequence of certificates, $C_1 \rightarrow C_2 \rightarrow
\ldots \rightarrow C_{n-1} \rightarrow C_n$, where $C_1$ is the root CA
certificate and is inherently trusted by the validator (denoted by $T(C_1) =
\text{true}$), $C_2$ to $C_{n-1}$ are intermediate CA certificates, and $C_n$ is
the end-user certificate. The chain's hierarchy is depicted\todo{\tiny I'm not
  sure how what follows is a depiction} as each certificate $C_i$ is issued by its predecessor $C_{i-1}$ (see Figure~\ref{cert_chain}). For validating such a chain, each certificate $C_i$ undergoes parsing (denoted by $P(C_i)$) and semantic checking (denoted by $\mathit{SCP}(C_i)$). While parsing enforces syntactic requirements on the structure of different certificate fields, semantic checking involves decoding and checking the values in a single certificate (\eg, the certificate is not expired with respect to current system time). In addition, semantic checking on subsequent certificates in a chain (\eg, matching subject and issuer names, signature verification) is represented by a function $\mathit{CCP}(C_i, C_{i-1})$, which must return \emph{true} for all $i \ge 2$. Hence, the overall legitimacy of a certificate chain is denoted by the following boolean expression.
\[
\bigwedge_{i=1}^{n} P(C_i) \land \bigwedge_{i=1}^{n} \mathit{SCP}(C_i) \land \bigwedge_{i=2}^{n} \mathit{CCP}(C_i, C_{i-1}) \land T(C_1)
\]

\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.58]{img/cert_chain.drawio.pdf} \\
  Fields marked with * are optional \\
  \vspace{0.2cm}
  \caption{Representation of an \xfon certificate chain}
  \label{cert_chain}
  \end{figure}

\subsection{Testing \xfon Implementations for Correctness}
\fuzzing\footnote{\fuzzing operates by mutating valid seed certificates to
  generate irregular inputs, which can reveal unexpected, potentially
  problematic behaviors in the implementation under scrutiny.}~\cite{frank,
  mucert, nezha, quan2020sadt, chen2023sbdt} and \symex\footnote{\symex
  systematically explores all possible paths a program could take during its
  execution, helping to reveal more deeply embedded logical
  bugs.}~\cite{rfcguided, symcert} had been shown previously as powerful
tools\todo{\tiny Footnotes might be exessive} for uncovering \emph{logical
  flaws} in the certificate chain validation code of many open-source TLS
libraries. While these techniques coupled with differential testing\footnote{Differential testing is a method of testing software by comparing the output of two or more implementations for the same input. It is used to find bugs where one implementation behaves differently from others.} have successfully identified numerous
noncompliance issues (\ie, being not compliant with respect to the standard
specification), they naturally bear the risk of false negatives since some logical flaws remain undetected in differential testing, especially when those are common across all the tested implementations. In addition, \fuzzing and \symex often fall short of providing any \emph{formal guarantees regarding correctness} of an \xfon implementation. This is corroborated through many high impact bugs and vulnerabilities found in some widely used applications and open-source libraries over the last decade~\cite{CVE-2020-5523, CVE-2020-13615, CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2021-34558, CVE-2020-36477, CVE-2021-43527, CVE-2022-3602, CVE-2022-3786, CVE-2022-3996, CVE-2022-47630, CVE-2022-4203, CVE-2023-0464, CVE-2023-2650, CVE-2023-33201, CVE-2023-40012, CVE-2023-39441}. In contrast, a formally-verified implementation for \xfon certificate validation can provide mathematical assurances that the implementation behaves
correctly, setting a benchmark for developing other such implementations.
Such a formally-verified implementation, however, is currently
missing, and our work is a major step towards filling this gap.

\subsection{Our Objective and High-level Challenges}
This paper addresses the aforementioned research gap by \emph{designing and developing a formally-verified implementation for \xfon certificate chain validation, named \armor}.
Concretely, our primary goal is to \emph{check whether a given X.509
  implementation is compliant with the X.509 specification}.\todo{\tiny Not
  congruent with intro (\armor as app library)} In general, to prove the
compliance of a given X.509 implementation ($I$), we have to formally specify
the requirements ($\phi$) of valid X.509 certificate chains and then prove that
the implementation $I$ satisfies the formal specification $\phi$ (\ie, $I
\models \phi$), writing machine-checked proofs using any interactive theorem
prover.\todo{\tiny not doing this for arbitrary implementations}

\subsubsection*{Challenges} There exists several challenges to develop a formally-verified X.509 implementation.

\textbf{a. Natural Language Specifications:} The \xfon specification is distributed 
across different documents (\eg, ITU-T \xfon~\cite{rec2005x}, RFC
5280~\cite{cooper2008internet}, RFC 6125~\cite{saint2011rfc}, RFC
4158~\cite{cooper2005rfc}, RFC 2527~\cite{rfc2527}, RFC
4518~\cite{zeilenga2006lightweight}), and its natural language specification has been shown to suffer from inconsistencies, ambiguities, and under-specification~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}\says{joy}{need an example}. Moreover, the specification for version 3 \xfon certificates, RFC 5280, does not only encompass rules for certificate issuers (\ie, producer rules) but also for the implementations that validate certificate chains (\eg, consumer rules). Additionally, RFC 5280 can be categorized into syntactic and semantic rules. The syntactic rules are concerned with the parsing of an X.509 certificate serialized as a byte stream, while the semantic rules impose constraints on the values of individual fields within a certificate and on the relationships between field values across different certificates in a chain. These intertwined sets of rules further complicate the specification, making it challenging to determine how \xfon implementations should respond in certain cases (\ie, whether to accept or reject an input).

\textbf{b. Parsing and Decoding Complexities:} The internal data structure of an \xfon certificate, while described in the
\emph{Abstract Syntax Notation One} (\asnone), is eventually serialized using
the \xsno Distinguished Encoding Rules (\der)~\cite{rec2002x}.
This \der representation of the certificate byte stream internally follows a $<T, L, V>$ structure to represent each certificate field, where $T$ denotes the
type, $V$ indicates the actual content, and $L$ signifies the length in bytes of
the $V$ field. Additionally, the $V$ field can include nested $<T, L, V>$ structures,
adding additional layers of complexity to the binary data. Parsing such a binary
data is challenging since it always requires passing the value of the $L$ field
(length) to accurately parse the subsequent $V$ field. Therefore, the internal
grammar of a \der-encoded certificate is \emph{context-sensitive}, and developing a
\emph{correct} parser for such a grammar is not trivial~\cite{kaminsky2010pki, debnath2021re}. 

To make matters worse, just correctly parsing the \asnone structure from the certificate byte stream 
is insufficient because the relevant certificate field value may need to be further 
decoded from the parsed \asnone value.
Take the \emph{example} of \xfon specification for using \texttt{UTCTime} format in certificate validity
field.
It uses a two-digit year representation, $YY$, and here lies the potential for
misinterpretation.
In this format, values from $00$ to $49$ are deemed to belong to the $21st$
century and are thus interpreted as $20YY$. In contrast, values from $50$ to $99$ are associated with the $20th$ century and
are consequently translated into $19YY$.
This peculiarity of the \texttt{UTCTime} format allows the representation of
years from $1950$ to $2049$.
Therefore, library developers need to be very careful to decode the actual value of \texttt{UTCTime}
to avoid potential certificate chain validation errors, 
a mistake previously made by MatrixSSL, axTLS, and tropicSSL~\cite{symcert}.


\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.73]{img/stages.drawio.pdf} \\
  \caption{Conceptual workflow of certificate chain validation}
  \label{cert_validation}
\end{figure}


\textbf{c. Overall Complexities:} The \xfon certificate chain validation
algorithm can be conceptually decomposed into different stages (see
Figure~\ref{cert_validation}). In general, the algorithm receives two
\emph{Privacy Enhanced Mail} (\pem)~\cite{balenson1993privacy} formatted
certificate files and the current system time as inputs. One \pem file contains
the end-user certificate and the relevant CA certificates to assist building
legitimate chains, while the other \pem file contains the certificates of
trusted CAs. \emph{First}, \circled{1} these \pem inputs are parsed to get each
certificate in their \basesf format, and then \circled{2} the \basesf decoder is
applied to each certificate to get its serialized byte stream in \der.
\circled{3} Each \der certificate is then parsed into an intermediate
representation for the next validation stages. Prior to \circled{6} enforcing
the semantic checks (\eg, expiration date check, signature verification), as
specified in RFC 5280~\cite{cooper2008internet}, \circled{4} string
canonicalization and \circled{5} chain building are sequentially performed.
String canonicalization is a type of string conversion to ensure all the strings
in a certificate are decoded in their \emph{normalized}
forms~\cite{zeilenga2006lightweight}, and chain building generates a candidate
certification path from a trusted CA to the end-user certificate~\cite{cooper2005rfc}.

Each of these validation stages present their own challenges. For example, building a valid certification path can be difficult due to the lack of concrete
directions as well as the possibility of having multiple valid certificate
chains, since a single certificate can be cross-signed by more than one CA~\cite{path}.
Converting strings to their \emph{normalized} forms is also a complex
process, since the number of character sets is humongous considering all the
languages worldwide. Moreover, before the signature verification (as part of semantic validation), the implementation needs to carefully
parse the actual contents of the \texttt{SignatureValue} field with cryptographic operations to prevent attacks (\eg, \emph{RSA signature forgery}~\cite{finney2006bleichenbacher,
  bleichenbacher1998chosen}).
While these intermediate stages are conceptually straightforward, implementing
them securely is nontrivial.



% \subsubsection{Modularity} Adopting a modular approach to implementing the \xfon CCVL can significantly mitigate some challenges. The entire process can be broken down into smaller, manageable components or modules. Each module is designed to perform a specific function, such as \der parsing, certificate chain building, string transformation, and semantic checks. Such modularization allows us to precisely specify the requirements for each module and independently establish their correctness. In addition, instead of trying to accomplish everything in a single step, this modularization allows us to undertake the validation task in multiple passes, increasing the simplicity and manageability of the overall process.

