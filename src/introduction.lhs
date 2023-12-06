% -*- eval: (flyspell-mode); -*-
\section{Introduction}
\label{sec:introduction}

The \xfon PKI standard~\cite{cooper2008internet} provides a scalable way to verify the authenticity of the binding of an entity's identity with its public key. 
This identity-public-key binding is represented as an \xfon certificate, which is digitally signed by an issuer 
%\footnote{The issuer of an \xfon certificate can also be the entity itself, 
%whose identity and public-key binding is vouched for in the certificate. Such
%certificates are commonly known as self-signed certificates.} 
(\eg, certificate authority or CA), 
signifying the issuer's trust in the authenticity and integrity of this binding. For scalably establishing the authenticity and integrity of a certificate, the \xfon standard takes advantage of the \emph{transitivity} of this ``\emph{trust}'' relationship. 
This intuition is realized in the \xfon standard~\cite{cooper2008internet} through a \emph{certificate chain validation} algorithm. Concretely, when an 
entity $e_1$ wants to check whether the certificate (given, as part of an input chain of certificates) of another entity $e_2$ is authentic, this algorithm \emph{conceptually} 
starts with the certificate of a  
trust anchor (\ie, an issuer who is unconditionally trusted by $e_1$) and then attempts to extend this absolute trust through a chain of the input certificates, 
all the way down to $e_2$.

Implementations of \xfon certificate chain validation, hailed
as the ``\emph{most dangerous code in the world}''~\cite{mdcode}, are thus
critical for ensuring the authentication guarantees promised by \xfon
PKI~\cite{cooper2008internet}.
Along with its authentication guarantees, \xfon also provides a scalable and
flexible mechanism for public-key distribution.
These desirable guarantees of \xfon PKI are often used as fundamental building
blocks for achieving other security assurances such as \emph{confidentiality},
\emph{integrity}, and  \emph{non-repudiation} in many applications, including
but not limited to SSL/TLS, IPSec, HTTPS, Email, 
%DNS over HTTPS/TLS, 
WiFi, code
signing,  secure boot, firmware/software verification, and secure software
update.
% 
% 
Given its pivotal role in the overall system, software, and communication security, ensuring the \emph{correctness} 
of \xfon certificate validation is of utmost importance. Incorrect validation could lead to a system accepting a malicious or invalid certificate, 
potentially exposing the system to man-in-the-middle (MITM) and impersonation attacks. Similarly, incorrectly rejecting a valid certificate could 
give rise to interoperability issues. 

The majority of prior work focuses on developing software testing mechanisms specialized for checking the correctness of 
different \xfon libraries~\cite{frank, mucert, nezha, quan2020sadt, chen2023sbdt, rfcguided, symcert}. While these methods 
have been beneficial in identifying numerous vulnerabilities, they often fall short of providing any formal guarantees regarding correctness. 
This is corroborated through many high impact bugs and vulnerabilities in some widely used applications and open-source libraries 
\cite{CVE-2020-14039, CVE-2016-11086, CVE-2020-1971, CVE-2020-35733, CVE-2020-36229, CVE-2023-33201, CVE-2023-40012}.   
In contrast, a formally-verified implementation of \xfon certificate chain
validation can provide mathematical assurances that the implementation behaves
correctly, setting a benchmark for developing other such implementations.
Such a formally-verified implementation, however, is currently missing from the
literature. \emph{The current paper takes a major step to addresses this
  research gap by designing and developing a high-assurance application for \xfon certificate chain validation, named \armor, whose compliance with the standard is established by formal,
machine-checked proofs.}

Although the current paper, to the best of our knowledge, presents the first implementation of \xfon certificate 
chain validation with machine-checked proofs of correctness, it draws inspirations from prior work in the area 
\cite{nqsb-tls, barenghi2018systematic, ramananandro2019everparse, tao2021dice, debnath2021re, ni2023asn1}. 
However, in comparison to \armor, prior work has at least one of the following 
limitations: (1) lacks any formal guarantees; (2) focuses only on parsing and lacks formal correctness guarantees
of semantic aspects; (3) lacks explicit proof of \emph{soundness} and \emph{completeness} of certificate 
parsing; (4) focuses only on verified encoding of certificates, not parsing.


\noindent\textbf{Challenges}. Developing \armor required addressing the following technical challenges. 
 \emph{First}, the \xfon specification is distributed 
across many documents (\eg, ITU-T \xfon~\cite{rec2005x}, RFC
5280~\cite{cooper2008internet}, RFC 6125~\cite{saint2011rfc}, RFC
4158~\cite{cooper2005rfc}, RFC 2527~\cite{rfc2527}, RFC
4518~\cite{zeilenga2006lightweight}), and its natural language specification has
been shown to suffer from inconsistencies, ambiguities, and under-specification~\cite{debnath2021re, larisch2022hammurabi, yen2021tools}. \emph{Second}, the format 
of an \xfon certificate is complex and nested, represented in \asnone \xsno DER (Distinguished Encoding Rules)
\cite{rec2002x}, and one requires a \emph{context-sensitive} grammar to enforce the
syntactic requirements of an \xfon certificate~\cite{kaminsky2010pki, debnath2021re}.
Thus, proving total correctness of the parser is quite complicated.
To make matters worse, parsing just the \asnone structure from the certificate byte stream 
is insufficient because the relevant certificate field value may need to be further 
decoded from the parsed \asnone DER value. \emph{Finally}, the \xfon chain validation can be conceptually decomposed into different stages (\ie, PEM parsing, Base64 decoding, \xsno DER parsing, string canonicalization, chain building, semantic validation, signature verification), each of which can be complex by itself (see~\cite{path, yahyazadeh2021morpheus, pkcsndss}).

\noindent\textbf{Approach}. \armor is designed and developed with modularity in mind. 
Inspired by prior work~\cite{debnath2021re, nqsb-tls}, 
we modularly decompose the whole \xfon certificate chain validation 
process into several modules, making manageable both the implementation and
formal verification efforts.
In particular, we formulate correctness guarantees for each module, which can
then be discharged independently.
\armor is organized into five modules: parser, chain builder, string canonicalizer, semantic validator, and driver. The \emph{driver}, written in \python, stitches together 
the different components and exposes an interface expected from an \xfon implementation. 
%takes as input a certificate chain to be validated as well as some other 
%necessary inputs (\eg, current system time, trust anchors), and returns a pair $\langle r, k\rangle$ 
%in which the result of the validation process $r\in \{\mathsf{Invalid}, \mathsf{Valid}\}$ 
%and $k$ is the public-key of the entity whose certificate is being validated. 
The  rest of the modules, written in the dependently typed functional
programming language \agda~\cite{bove2009brief, No07_agda}, implement all the
intermediate stages of certificate chain validation.
Notably, one can both write programs in \agda and also prove their correctness using 
%using an 
%\agda not only allows one to write programs 
%but also to prove correctness properties about those programs through 
\emph{interactive theorem proving}. 

Our general approach of verification carefully separates the specificational 
elements from the implementation elements by using relational specifications. 
As an example, for our approach to parser verification, we use \emph{relational,
  parser-independent} specifications of the PEM, \xsno DER, and \xfon formats.
Compared to approaches that verify parsers with respect to serializers, our
approach greatly reduces the complexity of the specifications and provides a
clear distinction between correctness properties of the \emph{language} and the
\emph{parser}.
To illustrate this distinction, for our \xsno DER and \xfon \emph{parsers} we have
proven \emph{soundness} (any bytestring accepted by the parsers conforms to the
format specification) and \emph{completeness} (any bytestring that conforms to
the format specification is accepted by the parser). For our \xsno DER and
\xfon \emph{language formalizations}, we have proven \emph{unambiguousness}
(e.g., one bytestring cannot be the encoding of two distinct \xfon certificates)
and \emph{non-malleability} (e.g., two distinct bytestrings cannot be the
encoding of the same \xfon certificate) required for the above guarantees.
For the full listing of properties proven, see
Table~\ref{tab:app-formal-guarantees} in the Appendix.
Once these proof obligations are discharged, we use \agda's extraction
mechanism to obtain an executable, which is then invoked by the driver.
%can then be used as an application invoked
%through any imperative programming language (\eg, \python). 


% We proved the following correctness properties for the parsers: \emph{soundness} (any input deemed syntactically valid by our implementation is indeed 
% a valid input), \emph{completeness} (any input deemed syntactically valid by the specification is indeed valid according to our implementation),  \emph{termination} of parser and semantic checker (the implementation terminates for all finite certificate
% chains), \emph{unambiguousness} of specification (one bytestring cannot be the encoding
% of two distinct \xfon certificates), and \emph{non-malleability} of specification (two distinct
% bytestrings cannot be the encoding of the same \xfon certificate)
% \cite{ramananandro2019everparse}. Once these different proof obligations 
% are discharged, we use \agda's extraction mechanism to obtain \haskell code, which can then be used as a 
% library invoked through the foreign function interfaces of different programming languages (\eg, \python). 

% Note that, using \agda 
% as the tool of choice for formally-verification is motivated primarily by its
% small \emph{trusted computing base}.\todo{\tiny Coq has a much smaller TCB}




% We prove the different guarantees of the different modules. Notable among these verification efforts, 
% is the first machine-checked proof of correctness (\ie, \soundness and \completeness) of the \parser module. 
% For proving the completeness of the parser, we also prove two necessary properties of our formalization of the 
% grammar of an \xfon certificate: \emph{no substrings} (\ie, parsers have no degrees of freedom over which prefix of the 
% input it consumes) and \emph{unambiguity} (\ie, parsers have no degrees of freedom in decoding a particular input).
% These formal guarantees signify that it is possible to develop efficient parsers
% for \xfon, although the grammar itself is context-sensitive. 

\noindent\textbf{Evaluation}. As \armor, or any formally verified software, is only as
good as its specification, it is crucial that we compare \armor{} 
to other implementations to gain assurance that our formalization of the natural
language specification is indeed correct.
%To check the correctness of our specification, we employ \emph{differential
%  testing}, a testing methodology for identifying software bugs by looking for
%discrepancies in the output of two or more implementations of the same algorithm
%invoked on the same input.
We \emph{differentially test} \armor against $11$ open-source \xfon libraries, using
around 3 million certificates from four different datasets. 
%the 
%following two datasets for input certificate chains: (1) a dataset of $2$
%million certificates randomly selected from a snapshot of $1.5$ billion real
%certificates gathered from the \censys~\cite{censys} certificate repository; (2)
%a dataset of $1$ million certificates generated by the \frankencert
%tool~\cite{frank} to mimic bad inputs.
We observe that \armor agrees with most libraries 
at least $99\%$ of the time. For the remaining $1\%$, we notice 
that \armor strictly follows the requirements in RFC 5280~\cite{cooper2008internet}, whereas the other libraries 
have a more relaxed enforcement of these requirements. 
Finally, to evaluate the practicality of \armor, 
we measure its runtime overhead in terms of computational time and memory consumption. 
We notice that \armor has a much higher overhead compared 
to the \xfon libraries that are written in \cpp, \python, \java, and \go.
% (\eg, \openssl~\cite{openssl}, \gnutls~\cite{gnutls}, \boringssl~\cite{boringssl}, \mbedtls~\cite{mbedtls}, \wolfssl~\cite{wolfssl}, \matrixssl~\cite{matrixssl}). 
% Compared to libraries in our evaluation written in Python, Java, and Go, we observe that  \armor either outperforms them or has similar performance. 
Our empirical evaluation signifies that \emph{\armor may be a reasonable choice of \xfon certificate validation application in some application domains where formal correctness 
is more important than runtime overhead}.

% Our formally-verified implementation, \armor, is organized into four main modules: the \driver, \parser, \stringtransformer, and \semantic. The \driver, implemented in \python, processes certificate inputs provided in a \pem (Privacy Enhanced Mail)~\cite{balenson1993privacy} file format, pre-assuming an ordered sequence of end-entity and CA certificates constituting a valid certification path. We leverage \agda~\cite{bove2009brief}, a dependently typed functional programming language and theorem prover, to formally-verify the \parser, \stringtransformer, and \semantic modules. We demonstrate both \soundness and \completeness in our verification step as overarching properties. \soundness guarantees that when \armor accepts a certificate chain, the formal specification will also. Conversely, \completeness ensures that if the formal specification accepts a certificate chain, \armor does too. By attaining both properties, we confirm that our implementation performs precisely as stipulated in the specification.


% \textbf{Evaluation and Notable Findings:} We aim to evaluate \armor's correctness in interpreting the specification, its performance as a benchmark, and its runtime and memory overhead. Therefore, we conduct differential testing against $11$ open-source \xfon implementations. Our evaluation uses a dataset of $2$ million certificates randomly selected from a snapshot of $1.5$ billion real certificates gathered from the \censys~\cite{censys} certificate repository. Our analysis shows that \armor enforces stricter validation rules compared to most libraries, rejecting $10,222$ certificate chains accepted by other libraries due to their violations of RFC-5280 requirements. \armor also showed no discrepancies compared to high-assurance implementation like \ceres~\cite{debnath2021re}. In terms of runtime and memory overhead, \armor consumes a considerable amount of memory compared to other libraries, yet its execution time is competitive, especially when compared to \ceres. These results suggest that despite not outperforming the \cpp libraries (\eg, \openssl~\cite{openssl}, \gnutls~\cite{gnutls}, \boringssl~\cite{boringssl}, \mbedtls~\cite{mbedtls}, \wolfssl~\cite{wolfssl}, \matrixssl~\cite{matrixssl}) regarding memory and runtime, \armor's correctness guarantees and reasonable runtime make it a viable choice for real-world scenarios.


\noindent\textbf{Impact.} \armor can substantially improve the security 
%and privacy 
of critical applications that rely on 
\xfon PKI (e.g., SSL/TLS). 
%for authentication and public-key distribution. 
%Notable among these applications is SSL/TLS. 
As an example, the existing formally verified TLS 1.2 implementation \cite{bhargavan2016mitls}
requires a correct \xfon PKI implementation to ensure its guarantees, which 
\armor can fulfill. 
%and ensure a strong guarantee. %and achieve a fully formally verified \xfon implementation.  
%assumes 
%, however, 
%Although there is a formally verified implementation of TLS
%1.2~\cite{bhargavan2016mitls}, it 
%assumes that the \xfon certificate validation
%implementation is correct.
%\armor can remove this critical assumption. 
%as a
%drop-in replacement for the chain validation task.
To evaluate the practicality of using \armor as part of 
a TLS implementation, we integrate it with the TLS 1.3 implementation 
of \boringssl~\cite{boringssl} and evaluate its performance. 
%of this claim, we integrated \armor with the TLS 1.3
%implementation of \mbedtls and tested with the widely-used data transfer tool
%\curl. 
We observe that \armor introduces significant overhead during TLS handshake.
\armor can also be used as an oracle for testing other \xfon 
implementations. 
%Another use case of \armor is as a \emph{test oracle} during software testing of
%\xfon implementations for finding logical bugs.
Finally, our relational language specifications can serve as a separate,
formal reference for programmers to consult. 
%seeking to understand the natural language
%documents specifying \xfon DER and \xsno.

% \says{JD}{need to be more specific on which modules are formally proved. soundess and completeness are part of parser, not semantic validation. also, the properties are defined in terms of chain. are we sure?}

% \textbf{Our Contributions:} 
\noindent\textbf{Contributions.} We make five technical contributions.

% \says{CJ}{Add parser-independent spec of grammar.}
\begin{enumerate}\setlength{\itemsep}{0em}
\item We present a formalization of the requirements of the \xfon standard and a modular decomposition of them, facilitating development of other such formally-verified implementations in the future. 
\item We prove that our formalization of the \xfon syntactic requirements is \emph{unambiguous} and \emph{non-malleable}.
\item We present the design and implementation of \armor, whose verified modules enjoy total correctness 
%\emph{soundness} and \emph{completeness} 
guarantees 
%of the parsers 
with respect to our formalized specification.  
% \item We prove that our interpretation of the syntactic requirements of \xfon
%   enjoys some specific properties, indicating that it is possible to develop
%   efficient parsers.\todo{\tiny This needs clarification.}
\item We evaluate \armor with respect to its specificational accuracy and overhead against $11$ open-source libraries, and analyze its performance and effectiveness in practice.
\item We show an end-to-end application of \armor, integrating it with TLS 1.3 implementation of \boringssl and testing with the widely-used application \curl~\cite{curl}.
\end{enumerate}

% Our work presents significant contributions to the field of \xfon PKI, as stated below.

% \begin{enumerate}
%     \item We have articulated a formal specification of the \xfon standard
% using our unique interpretation, leading to a better understanding and clear representation of the standard. 

%     \item We have developed \armor, an implementation that accurately conforms to this formal specification, providing a correct and specification-compliant solution for certificate validation.


%     \item Our evaluation of \armor is extensive and comprehensive, as it has been tested against $11$ open-source \xfon libraries, demonstrating its reasonable performance and effectiveness in practice.
% \end{enumerate}