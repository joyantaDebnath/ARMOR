\newcommand{\field}[1]{\ensuremath{\mathsf{\small #1}}\xspace}
\renewcommand{\chain}{\ensuremath{\mathcal{C}}\xspace}
\section{Background and Motivation of \armor}
This section presents a primer on \xfon certificates and  
certificate chain validation, the motivation of \armor, and 
the underlying problem \armor aims to address. 

%a brief discussion on \xfon certificate chain validation,
%highlighting prior works on testing open-source \xfon implementations and
%finally emphasizing the motivation for our work.

\subsection{Preliminaries on \xfon Certificate Chain}
Though the \xfon standard is primarily defined in the ITU-T \xfon~\cite{rec2005x}, RFC 5280~\cite{cooper2008internet} provides additional restrictions and directions to use \xfon certificate for the Internet domain. Particularly, RFC 5280 concentrates on version 3 of the certificate standard and the usage of different extensions, which is the main focus of this work.

\textbf{Internal Structure of a Certificate.} A version 3 certificate comprises of three top-level fields, namely, \field{TBSCertificate}, \field{SignatureAlgorithm}, and \field{SignatureValue}. The \field{TBSCertificate} field contains information such as the certificate version, a unique serial number, the validity period, the certificate issuer's name, and the certificate owner's name (\ie, subject). It also includes the public-key, the algorithm employed by the issuer for signing the certificate, and a few \emph{optional} fields such as the unique identifiers and a sequence of extensions, specifically for version 3 of the \xfon standard. The issuer CA signs the entire \field{TBSCertificate} content, generating a signature, denoted as \field{SignatureValue}, which is appended to the end of the certificate, creating a digitally secure and tamper-proof container. The \field{SignatureAlgorithm} field specifies the algorithm used by the issuer CA for generating the signature.

\textbf{Certificate Chain Validation.} A certificate chain \chain can be \emph{conceptually} 
viewed as an ordered sequence of certificates, $\chain = [C_1, C_2, \ldots, C_{n-1}, C_n]$, in which $C_1$ to $C_{n-1}$ are the (intermediate) CA certificates whereas $C_n$ is
the end-user certificate. Each certificate $C_i$ is issued by its
predecessor $C_{i-1}$ (see Figure~\ref{cert_chain}). Roughly speaking, 
the certificate chain validation can be \emph{conceptually} decomposed into the 
following stages: \emph{parsing}, \emph{semantic condition checking},  
\emph{signature verification}, and \emph{trust anchor verification}.

The parsing stage checks to see whether each certificate $C_i$ in \chain  
is syntactically well-formed. After parsing, the semantic condition checking 
stage checks to see whether the standard-prescribed 
semantic conditions are fulfilled. These conditions 
can be on a single certificate (e.g.,the certificate is not expired) or across certificates (e.g., 
the subject name of the certificate $C_{i-1}$ is the same as the issuer name of the 
certificate $C_i$). 
The next stage is to check whether the digital signature 
present in each certificate $C_i$ can be verified. 
Finally, one checks to see 
whether $C_1$ is present in the trusted root store. All of these checks 
together allows one to extend 
the unconditional trust of $C_1$ through the intermediate CA certificates
($C_2$ to $C_{n-1}$), all the way down to the end-user certificate ($C_n$). 

%For validating such a
%chain \chain, each certificate $C_i$ undergoes parsing (denoted by $P(C_i)$) and
%semantic validation (denoted by $\mathit{SCP}(C_i)$). While parsing enforces
%syntactic requirements on the structure of different certificate fields,
%semantic validation involves decoding and checking the values in a single
%certificate (\eg, the certificate is not expired with respect to current system
%time). In addition, semantic validation on subsequent certificates in a chain
%(\eg, matching subject and issuer names, signature verification) is represented
%by a function $\mathit{CCP}(C_i, C_{i-1})$, which must return \emph{true} for
%all $i \ge 2$. Finally, the chain must be checked to ensure it starts from a
%trust anchor of the validator, meaning that $C_1$ must be a trusted CA
%certificate (denoted by $T(C_1) = \text{true}$).
%This allows to extend the absolute trust through the intermediate CA certificate
%($C_2$ to $C_{n-1}$), all the way down to the end-user certificate ($C_n$).
%Hence, the legitimacy of a certificate chain can be denoted by the following Boolean expression.

%\[
%\bigwedge_{i=1}^{n} P(C_i) \land \bigwedge_{i=1}^{n} \mathit{SCP}(C_i) \land \bigwedge_{i=2}^{n} \mathit{CCP}(C_i, C_{i-1}) \land T(C_1)
%\]

\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.58]{img/cert_chain.drawio.pdf} \\
  Fields marked with * are optional \\
  \vspace{0.2cm}
  \caption{Representation of an \xfon certificate chain}
  \label{cert_chain}
  \end{figure}

For ease of exposition, the certificate chain validation described here is intentionally 
left to be simple. An implementation has to address different corner cases. 
As an example, the presented certificate chain \chain may not be in the 
correct hierarchical order, and also may not contain some CA certificates or may 
contain duplicates. It is the implementation's responsibility to address these cases. 
For a faithful description of the whole certificate chain validation, interested readers 
can consult the  RFC 5280 
\cite{cooper2008internet}. 
%Note that the entire process of certificate chain validation is more complicated
%than what we have described so far. For example, the implementation may not
%receive the certificates in the proper hierarchical order, may miss some CA
%certificates, or may contain duplicate CA certificates. In that case, the
%implementation needs to build a proper certificate chain from the received
%certificates and its trust anchor. This chain building process may also generate
%multiple candidate certificate chains since some certificates can be
%cross-signed by multiple CAs~\cite{path}.
%However, if at least one such candidate chain passes the semantic validation,
%the algorithm successfully completes.
%We discuss certificate chain validation in more detail in Section 3.

\subsection{Motivation of \armor}
A majority of the existing work focuses on testing the logical correctness 
of the certificate chain validation. These efforts can be categorized into 
approaches that use \fuzzing~\cite{frank,  mucert, nezha, quan2020sadt, 
chen2023sbdt} and \symex~\cite{rfcguided, symcert}. One of the main challenges 
all of these approaches have to address is a lack of \emph{test oracle}. Most 
of the prior approaches rely on differential testing whether different implementations 
are used as \emph{cross-checking test oracles}. These approaches, however, can potentially 
suffer from undetected bugs, especially in the case that the implementations under test 
have the same logical error. Having a formally verified \emph{test oracle} can substantially 
decrease the change of undetected bugs. In addition, these approaches cannot 
provide any mathematical assurance of correctness for the tested implementations. 
This is corroborated through many high impact bugs and  vulnerabilities found in 
some widely used applications and open-source libraries over the last decade~\cite{CVE-2020-5523, CVE-2020-13615, CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2021-34558, CVE-2020-36477, CVE-2021-43527,  CVE-2022-3602, CVE-2022-3786, CVE-2022-3996, CVE-2022-47630, CVE-2022-4203, CVE-2023-0464, CVE-2023-2650, CVE-2023-33201, CVE-2023-40012, CVE-2023-39441}. In contrast, a formally verified implementation of \xfon certificate validation like \armor 
can give mathematical assurance that it does not suffer from such logical bugs. 

%\fuzzing~\cite{frank,
%  mucert, nezha, quan2020sadt, chen2023sbdt} and \symex~\cite{rfcguided,
%  symcert} have previously been shown to be powerful tools for uncovering
%\emph{logical flaws} in the certificate chain validation code of many
%open-source TLS libraries.
%While \fuzzing operates by mutating valid seed certificates to
%generate irregular inputs, which can reveal unexpected, potentially
%problematic behaviors in the implementation under scrutiny, \symex
%systematically explores all possible paths a program could take during its
%execution, helping to reveal more deeply embedded logical
%bugs. While these techniques coupled with differential testing have successfully identified numerous
%noncompliance issues (\ie, not being compliant with respect to the standard
%specification), they naturally bear the risk of false negatives since some logical flaws remain undetected in differential testing, especially when those are common across all the tested implementations. In addition, \fuzzing and \symex often fall short of providing any \emph{formal guarantees regarding correctness} of an \xfon implementation. This is corroborated through many high impact bugs and vulnerabilities found in some widely used applications and open-source libraries over the last decade~\cite{CVE-2020-5523, CVE-2020-13615, CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2021-34558, CVE-2020-36477, CVE-2021-43527, CVE-2022-3602, CVE-2022-3786, CVE-2022-3996, CVE-2022-47630, CVE-2022-4203, CVE-2023-0464, CVE-2023-2650, CVE-2023-33201, CVE-2023-40012, CVE-2023-39441}. In contrast, a formally-verified implementation for \xfon certificate validation can provide mathematical assurances that the implementation behaves
%correctly, setting a benchmark for developing other such implementations.
%Such a formally-verified implementation, however, is currently
%missing, and our work is a major step towards filling this research gap.


%\subsection{Overarching Objective}
%This paper addresses the aforementioned research gap by \emph{designing and developing a high-assurance implementation for \xfon certificate chain validation, named \armor, with machine-checked proofs for its correctness guarantees}. In general, to achieve this goal, we have to formally specify the requirements ($\phi$) of valid \xfon certificate chains and then prove that
%our implementation $I$ satisfies the formal specification $\phi$ (\ie, $I
%\models \phi$).
%
%\textbf{Difference with prior work.} Although the current paper presents the first high-assurance implementation of \xfon certificate chain validation with correctness guarantees, it draws inspirations from prior work in the area.
%As an example, we rely on the 
%prior re-engineering effort of the \xfon specification and implementation
%(nqsb-TLS~\cite{nqsb-tls}, CERES~\cite{debnath2021re},
%Hammurabi~\cite{ni2023asn1}) to distinguish between the syntactic and semantic
%requirements of \xfon and design \armor in a modular way. However, in comparison
%to \armor, these works lack any formal correctness guarantees. Although
%Ramananandro \etal proposed EverParse~\cite{ramananandro2019everparse}, a
%framework for generating verified parsers and serializers from Type-Length-Value
%(\tlv) binary message format descriptions, with memory safety, functional
%correctness (\ie, parsing is the inverse of serialization and vice versa), and
%non-malleable guarantees, it only focuses on parsing, and lacks formal correctness guarantees of other stages of the
%certificate chain validation.
%Barenghi \etal proposed an approach to automatically generate a parser for \xfon
%with the \antlr parser generator~\cite{barenghi2018systematic}, however they  do
%major simplifications of the \xfon grammar to avoid complexities in parsing.
%Tao \etal developed a memory-safe and formally correct encoder for \xfon
%certificates~\cite{tao2021dice}, while our work does the reverse task,
%\emph{certificate decoding}.
%






% However, in comparison to \armor, prior work has at least one of the following 
% limitations: (1) Lacks any formal guarantees~\cite{nqsb-tls, debnath2021re}; (2) Focuses only on parsing and lacks formal correctness guarantees
% of semantic aspects~\cite{}; (3) Lacks explicit proof of \emph{soundness} and \emph{completeness} of certificate 
% parsing~\cite{}; (4) Focuses only on verified encoding of certificates, not parsing~\cite{}. Since \armor offers higher assurances than these prior work, we expect it to substantially improve the security and privacy of applications that rely on \xfon for authentication and public-key distribution.


