\section{Background and Problem Definition}
This section provides a brief discussion on \xfon certificate chain validation,
highlighting prior works on testing open-source \xfon implementations and
finally emphasizing the motivation for our work.

\subsection{Preliminaries on \xfon Certificate Chain}
Though the \xfon standard is primarily defined in the ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use \xfon certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of different extensions, which is the main focus of this work.

\textbf{Internal Structure of a Certificate.} A version 3 certificate comprises three top-level fields: \texttt{TBSCertificate}, \texttt{SignatureAlgorithm}, and  \texttt{SignatureValue}. The \texttt{TBSCertificate} field contains information such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (\ie, subject). It also includes the public-key, the algorithm employed by the issuer for signing the certificate, and a few \emph{optional} fields like unique identifiers and a sequence of extensions, specifically for version 3 of the \xfon standard. The issuer CA signs the entire \texttt{TBSCertificate} content, generating a signature, denoted as \texttt{SignatureValue}, which is appended to the certificate's end, creating a digitally secure and tamper-proof document. The \texttt{SignatureAlgorithm} field specifies the algorithm used by the issuer CA for generating the signature.

\textbf{Certificate Chain Validation.} A certificate chain is
represented as a sequence of certificates, $C_1 \rightarrow C_2 \rightarrow
\ldots \rightarrow C_{n-1} \rightarrow C_n$, where $C_1$ to $C_{n-1}$ are the CA certificates, $C_n$ is
the end-user certificate, and each certificate $C_i$ is issued by its predecessor $C_{i-1}$ (see Figure~\ref{cert_chain}). For validating such a chain, each certificate $C_i$ undergoes parsing (denoted by $P(C_i)$) and semantic validation (denoted by $\mathit{SCP}(C_i)$). While parsing enforces syntactic requirements on the structure of different certificate fields, semantic validation involves decoding and checking the values in a single certificate (\eg, the certificate is not expired with respect to current system time). In addition, semantic validation on subsequent certificates in a chain (\eg, matching subject and issuer names, signature verification) is represented by a function $\mathit{CCP}(C_i, C_{i-1})$, which must return \emph{true} for all $i \ge 2$. Finally, the chain must be checked to ensure it starts from a trust anchor of the validator, that means, $C_1$ must be a trusted CA certificate (denoted by $T(C_1) =
\text{true}$). This allows to extend the absolute trust through the intermediate CA certificate ($C_2$ to $C_{n-1}$), all the way down to the end-user certificate ($C_n$). Hence, the legitimacy of a certificate chain can be denoted by the following boolean expression.

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


\emph{Note that}, the entire process of certificate chain validation is more complicated than what we have described so far. For example, the implementation may not receive the certificates in the proper hierarchical order, may miss some CA certificates, or may contain duplicate CA certificates. In that case, the implementation needs to build a proper certificate chain from the received certificates and its trust anchor. This chain building process may also generate multiple candidate certificate chains since some certificates can be cross-signed by multiple CAs~\cite{path}. However, if at least one such candidate chain passes the semantic validation, the algorithm successfully completes. More details on certificate chain validation is discussed in Section 3.

\subsection{Testing \xfon Implementations for Correctness}
\fuzzing~\cite{frank,
  mucert, nezha, quan2020sadt, chen2023sbdt} and \symex~\cite{rfcguided, symcert} had been shown previously as powerful
tools for uncovering \emph{logical
  flaws} in the certificate chain validation code of many open-source TLS
libraries. While \fuzzing operates by mutating valid seed certificates to
generate irregular inputs, which can reveal unexpected, potentially
problematic behaviors in the implementation under scrutiny, \symex
systematically explores all possible paths a program could take during its
execution, helping to reveal more deeply embedded logical
bugs. While these techniques coupled with differential testing\footnote{Differential testing is a method of testing software by comparing the output of two or more implementations for the same input. It is used to find bugs where one implementation behaves differently from others.} have successfully identified numerous
noncompliance issues (\ie, being not compliant with respect to the standard
specification), they naturally bear the risk of false negatives since some logical flaws remain undetected in differential testing, especially when those are common across all the tested implementations. In addition, \fuzzing and \symex often fall short of providing any \emph{formal guarantees regarding correctness} of an \xfon implementation. This is corroborated through many high impact bugs and vulnerabilities found in some widely used applications and open-source libraries over the last decade~\cite{CVE-2020-5523, CVE-2020-13615, CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2021-34558, CVE-2020-36477, CVE-2021-43527, CVE-2022-3602, CVE-2022-3786, CVE-2022-3996, CVE-2022-47630, CVE-2022-4203, CVE-2023-0464, CVE-2023-2650, CVE-2023-33201, CVE-2023-40012, CVE-2023-39441}. In contrast, a formally-verified implementation for \xfon certificate validation can provide mathematical assurances that the implementation behaves
correctly, setting a benchmark for developing other such implementations.
Such a formally-verified implementation, however, is currently
missing, and our work is a major step towards filling this research gap.


\subsection{Overarching Objective}
This paper addresses the aforementioned research gap by \emph{designing and developing a high-assurance implementation for \xfon certificate chain validation, named \armor, with machine-checked proofs for its correctness guarantees}. In general, to achieve this goal, we have to formally specify the requirements ($\phi$) of valid X.509 certificate chains and then prove that
our implementation $I$ satisfies the formal specification $\phi$ (\ie, $I
\models \phi$), using a suitable interactive interactive theorem
prover. Although the current paper, to the best of our knowledge, presents the first high-assurance implementation of \xfon certificate chain validation with correctness guarantees, it draws inspirations from prior work in the area 
\cite{nqsb-tls, barenghi2018systematic, ramananandro2019everparse, tao2021dice, debnath2021re, ni2023asn1}. 
% For example, we rely on the re-engineering efforts of the \xfon specification and implementation~\cite{debnath2021re, nqsb-tls} to distinguish between the syntactic and semantic requirements to design \armor in a modular way. 
However, in comparison to \armor, prior work has at least one of the following 
limitations: (1) Lacks any formal guarantees~\cite{nqsb-tls, debnath2021re}; (2) Focuses only on parsing and lacks formal correctness guarantees
of semantic aspects~\cite{}; (3) Lacks explicit proof of \emph{soundness} and \emph{completeness} of certificate 
parsing~\cite{}; (4) Focuses only on verified encoding of certificates, not parsing~\cite{}. Since \armor offers higher assurances than these prior work, we expect it to substantially improve the security and privacy of applications that rely on \xfon for authentication and public-key distribution.


