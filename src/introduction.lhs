\section{Introduction}

The \xfon PKI standard \cite{RFC5280} provides a scalable way to verify the binding of an entity's identity with its public key. 
The identity-public-key binding of an entity is represented as an \xfon certificate, which is digitally signed by an issuer 
(\eg, certificate authority or CA)\footnote{The issuer of an \xfon certificate can also be the entity itself, 
whose identity and public-key binding is vouched for in the certificate. Such certificates are commonly known as self-signed certificates.}, 
signifying the issuer's trust in the authenticity and integrity of this binding. For scalably establishing the authenticity and integrity 
of a certificate, the \xfon standard takes advantage of the \emph{transitivity} of this ``\emph{trust}'' relationship. 
This intuition is realized in the \xfon standard \cite{RFC5280} through \emph{a certificate chain validation algorithm}. Concretely, when an 
entity $e_1$ wants to check whether the certificate of another entity $e_2$ is authentic, this algorithm starts with the certificate of a  
trust anchor (i.e., an issuer who is unconditionally trusted by $e_1$) and then attempts to extend this trust through a chain of input certificates, 
all the way down to $e_2$. 

The \xfon certificate chain validation implementation, hailed as the ``\emph{most dangerous code in the world}'' \cite{mdcode}, is thus critical 
to ensuring the authentication guarantees promised by the \xfon PKI~\cite{rec2005x}. Along with its authentication guarantees, 
\xfon also provides a scalable and flexible mechanism for public-key distribution. These desirable guarantees of \xfon PKI 
are often used as fundamental building blocks for achieving other security assurances such as \emph{confidentiality}, \emph{integrity}, and 
\emph{non-repudiation} in many applications, including but not limited to SSL/TLS, IPSec, HTTPS, Email, DNS over HTTPS/TLS, WiFi, code signing, 
secure boot, firmware/software verification, and secure software update. 


Given its pivotal role in the overall system, software, and communication security, ensuring the correctness 
of \xfon certificate validation is of utmost importance. Incorrect validation could lead to a system accepting a malicious or invalid certificate, 
potentially exposing the system to man-in-the-middle (MITM) and impersonation attacks. Similarly, incorrectly rejecting a valid certificate could 
give rise to interoperability issues. A majority of the prior work focuses on developing testing mechanisms for checking the correctness of 
different libraries \cite{frank, mucert, nezha, quan2020sadt, chen2023sbdt, rfcguided, symcert}. While these methods 
have been beneficial in identifying numerous vulnerabilities, they often fall short of providing any guarantee regarding correctness. 
In contrast, a formally verified \xfon certificate chain validation implementation can provide mathematical assurances that the implementation 
behaves correctly, setting a benchmark for developing other such implementations. Such a formally verified implementation, however, is currently 
missing from the literature. \emph{The current paper addresses this research gap by designing and developing a library for \xfon certificate chain validation, 
named \armor, whose compliance with the standard is mathematically proven correct}.  

Although the current paper, to the best of our knowledge, presents the first implementation of \xfon certificate 
chain validation with a machine-checked proof of correctness, it draws inspirations from a number of prior work in the area 
\cite{debnath2021re, ramananandro2019everparse, ni2023asn1, tao2021dice, barenghi2018systematic, nqsb-tls}. 
% As an example, we rely on the 
% prior re-engineering effort of the \xfon specification and implementation \cite{debnath2021re, nqsb-tls} to distinguish between the syntactic 
% and semantic requirements to design \armor in a modular way. 
In comparison to \armor, prior work, however, suffers from at least one of the following 
limitations: (1) Lacks any formal guarantees; (2) Focuses only on parsing; (3) Lacks explicit proof of soundness and completeness of certificate 
parsing; (4) Focuses only on verifiable encoding of certificates, not parsing; (5) Lacks formal correctness guarantees of semantic aspects.  

% Previous testing efforts have leveraged methods like \fuzzing~\cite{frank, mucert, nezha, quan2020sadt, chen2023sbdt}, which involves feeding a range of invalid inputs to the system to find vulnerabilities, and \symex~\cite{rfcguided, symcert}, a method of analyzing a program to determine what inputs cause each part of the program to execute. While these methods have been beneficial in identifying numerous vulnerabilities, they often fall short of providing a guarantee of correctness. Though a recent re-engineering effort by Debnath \etal has developed a high-assurance implementation for \xfon certificate validation leveraging \smtsolver~\cite{debnath2021re}, their approach also does not provide formal correctness. However, a formally-verified reference implementation can provide mathematical assurance that the implementation behaves as expected as the requirements of the standard specifications and may set a benchmark for developing other implementations. Hence, there is a clear motivation for \textit{developing a formally-verified reference implementation for \xfon certificate validation}, which is the research gap we address in this paper.

% chain building~\cite{cooper2005rfc, path}

% \textbf{Technical Challenges:} 
Developing \armor required addressing the following technical challenges. 
\emph{Firstly}, the specifications we need to follow are written in natural language (\eg, English) and often unclear and under-specified~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}, making them tricky to interpret correctly. 
\emph{Secondly}, formalizing the specification accurately requires a lot of manual effort and technical expertise. 
 \emph{Thirdly}, building a provably correct parser to decode the structure of a \der (Distinguished Encoding Rule)~\cite{rec2002x} encoded binary certificate is quite complex due to the \emph{context-sensitive} nature of the certificate's internal grammar~\cite{kaminsky2010pki, debnath2021re}. \emph{Fourthly}, before we can check an already parsed certificate for semantic errors, we need to correctly perform some intermediate transformations like  string transformation~\cite{zeilenga2006lightweight}. \emph{Finally}, proving the partial correctness guarantees, especially completeness, is technically very demanding and requires handling different case splits and discharging their proofs manually. 

% daunting task of modeling and demonstrating the correctness of the cryptographic operations can pose a significant challenge, demanding sophisticated mathematical techniques and a deep understanding of the underlying cryptographic principles while ensuring the focus remains on the core certificate validation process.

% \textbf{Technical Insights:} 
% Developing \armor takes advantage of the following technical insights. 
% First, we can modularly decompose the whole \xfon certificate chain validation 
% process into different stages. Such modularity facilitates both ease of implementation, 
% manageability of the implementation, and also formal verification. Particularly, one can 
% decompose the overall guarantees that need to be proven into guarantees for each modules, 
% which can then be discharged independently. We want to emphasize that such modularity has 
% been promoted and demonstrated in essence by prior work \cite{debnath2021re, nqsb-tls}, 
% which conjectured that it can simplify the formal verification. We show it is indeed the case 
% that it substantially simplifies the proof of correctness. Second,   

% inspired by prior re-engineering effort of the \xfon specification 
% and implementation \cite{debnath2021re, nqsb-tls}, it is possible to decompose 
% the requirements of \xfon into syntactic and semantic requirements to ensure a 
% simpler parser. As we will show, such a methodology facilitates the development of a manageable parser that does not compromise on the necessary rigor. \textit{Furthermore}, we leverage a modular implementation, breaking the process into distinct modules. Such an approach aids in simplifying the overall certificate validation process, as it allows for the detailed specification of the requirements and establishes the correctness of each module independently. \textit{Finally}, backed by measurements, we recognize that not all aspects of the \xsno \der~\cite{rec2002x} and RFC-5280~\cite{cooper2008internet} specifications are used in practice, we primarily focus on the most commonly employed fragments of these standards, thereby ensuring the relevance and usability of our formally-verified implementation.

% \textbf{ARMOR's Approach:} 
\armor is designed and developed with modularity in mind. Inspired by prior work \cite{debnath2021re, nqsb-tls}, 
we modularly decompose the whole \xfon certificate chain validation 
process into several stages. Such modularity facilitates both ease of implementation, 
manageability of the implementation, and also formal verification. Particularly, we 
decompose the overall guarantees that need to be proven into guarantees for each modules, 
which can then be discharged independently. Concretely, \armor, is organized into four main modules: 
the \driver, \parser, \stringtransformer, and \semantic. The \driver, implemented in \python, 
takes as input a certificate chain to be validated as well as some other 
necessary inputs (e.g., system time, trusted root store), and returns a pair $\langle r, k\rangle$ 
in which the result of the validation process $r\in \{\mathsf{Invalid}, \mathsf{Valid}\}$ 
and $k$ is the public-key of the entity whose certificate is being validated. The other 
modules, namely \parser, \stringtransformer, and \semantic, are written in \agda~\cite{bove2009brief}, 
a dependently typed functional programming language. \agda not only allows one to write programs 
but also allows one to prove properties about these programs through interactive theorem proving. 
We prove the different guarantees of the different modules. Notable among these verification efforts, 
is the first machine-checked proof of partial correctness (i.e., \soundness and \completeness) of the \parser module. 
For proving the completeness of the parser, we also prove two necessary properties of our formalization of the 
grammar of an \xfon certificate, namely, \emph{unambiguity} and \emph{uniqueness}, which our parser also 
enjoys. These formal guarantees signifies that it is possible to develop efficient parsers for \xfon, although 
the grammar itself is context-sensitive. 

As \armor is as good as its specification, it is crucial to ensure that our interpretation of the specification is consistent 
with other implementations. To check the correctness of the specification, we differentially test \armor against $11$ open-source 
\xfon libraries. To carry out this differential analysis, we use the following two datasets of input certificate chains: 
(1) a dataset of $2$ million certificates randomly selected from a snapshot of $1.5$ billion real certificates gathered from the \censys~\cite{censys} certificate repository; 
(2) a dataset of $X$ certificates generated by the Frankencert tool \cite{frank} to mimic bad inputs. 
We observe that \armor agrees with most libraries 
at least $99.49\%$ of the time. For the remaining $0.51\%$, we notice 
that \armor strictly follows the requirements in RFC 5280, whereas the other libraries 
have a more relaxed enforcement of these requirements. 
Finally, to evaluate the practical usability of \armor, we measure its runtime overhead in terms of computational time and memory consumption. 
We notice that \armor has a much higher overhead compared to libraries in our analysis 
that are written in \cpp (\eg, \openssl~\cite{openssl}, \gnutls~\cite{gnutls}, \boringssl~\cite{boringssl}, \mbedtls~\cite{mbedtls}, \wolfssl~\cite{wolfssl}, \matrixssl~\cite{matrixssl}). 
Compared to libraries in our evaluation written in Python, Java, and Go, we observe that 
\armor either outperforms them  or has similar performance. 
The empirical evaluation signify that \armor may be reasonable choice in some application domains where formal correctness 
is more important than runtime overhead. 

% Our formally-verified implementation, \armor, is organized into four main modules: the \driver, \parser, \stringtransformer, and \semantic. The \driver, implemented in \python, processes certificate inputs provided in a \pem (Privacy Enhanced Mail)~\cite{balenson1993privacy} file format, pre-assuming an ordered sequence of end-entity and CA certificates constituting a valid certification path. We leverage \agda~\cite{bove2009brief}, a dependently typed functional programming language and theorem prover, to formally verify the \parser, \stringtransformer, and \semantic modules. We demonstrate both \soundness and \completeness in our verification step as overarching properties. \soundness guarantees that when \armor accepts a certificate chain, the formal specification will also. Conversely, \completeness ensures that if the formal specification accepts a certificate chain, \armor does too. By attaining both properties, we confirm that our implementation performs precisely as stipulated in the specification.


% \textbf{Evaluation and Notable Findings:} We aim to evaluate \armor's correctness in interpreting the specification, its performance as a benchmark, and its runtime and memory overhead. Therefore, we conduct differential testing against $11$ open-source \xfon implementations. Our evaluation uses a dataset of $2$ million certificates randomly selected from a snapshot of $1.5$ billion real certificates gathered from the \censys~\cite{censys} certificate repository. Our analysis shows that \armor enforces stricter validation rules compared to most libraries, rejecting $10,222$ certificate chains accepted by other libraries due to their violations of RFC-5280 requirements. \armor also showed no discrepancies compared to high-assurance implementation like \ceres~\cite{debnath2021re}. In terms of runtime and memory overhead, \armor consumes a considerable amount of memory compared to other libraries, yet its execution time is competitive, especially when compared to \ceres. These results suggest that despite not outperforming the \cpp libraries (\eg, \openssl~\cite{openssl}, \gnutls~\cite{gnutls}, \boringssl~\cite{boringssl}, \mbedtls~\cite{mbedtls}, \wolfssl~\cite{wolfssl}, \matrixssl~\cite{matrixssl}) regarding memory and runtime, \armor's correctness guarantees and reasonable runtime make it a viable choice for real-world scenarios.

% \textbf{Our Contributions:} 
This paper makes the following technical contributions. 
\begin{enumerate}
\item We present a formalization of the requirements of the \xfon standard and a modular decomposition of them enabling development of other such formally-verified implementations in the future. 
\item We present the design and implementation of \armor, which enjoys the soundness and completeness guarantees with respect to our specification.  
\item We prove that our interpretation of the syntactic requirements of \xfon enjoys some specific properties that indicate the development of efficient parsers. 
\item We evaluate \armor with respect to its specificational accuracy and runtime overhead against $11$ widely used libraries, and demonstrate its reasonable performance and effectiveness in practice.
\end{enumerate}

% Our work presents significant contributions to the field of \xfon PKI, as stated below.

% \begin{enumerate}
%     \item We have articulated a formal specification of the \xfon standard using our unique interpretation, leading to a better understanding and clear representation of the standard. 

%     \item We have developed \armor, an implementation that accurately conforms to this formal specification, providing a correct and specification-compliant solution for certificate validation.


%     \item Our evaluation of \armor is extensive and comprehensive, as it has been tested against $11$ open-source \xfon libraries, demonstrating its reasonable performance and effectiveness in practice.
% \end{enumerate}