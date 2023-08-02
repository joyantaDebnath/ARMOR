\section{Design and Implementation of ARMOR} 
In this section, we present the required toolchain for our formally verified CCVL implementation, its high-level architecture, and finally discuss the implementation details.

\subsection{Preliminaries on Toolchain}
We use the \agda theorem prover~\cite{bove2009brief} for formally verifying the CCVL implementation and the formally verified oracle of \morpheus~\cite{yahyazadeh2021morpheus} for signature verification. Now, we present a brief overview of these tools.

\subsubsection{Agda Theorem Prover}
\label{sec:design-agda}
\agda~\cite{bove2009brief} is a powerful and expressive programming language that combines functional programming and formal verification. At its core, \agda is a \textit{dependently-typed} functional programming language, which allows types to be predicated on values. This capability helps express rich properties in types and ensures that the programs conform to these properties. In other words, if a program compiles, it is also proven to meet the specifications described by the types. Another important feature is that \agda supports interactive theorem proving. Programmers can write proofs interactively by filling in parts of proofs, referred to as ``proof holes'' while the \agda compiler checks that every step is correct. This makes \agda a powerful tool for ensuring the correctness of an implementation. 

% Note that we can generate an executable binary of the implementation by first compiling the \agda source code into \haskell and then using a \haskell compiler to compile the generated \haskell code into a binary. 

As an example of \agda's syntax, consider representing the \agda boolean values in their \xsno \der counterparts. As per the Basic Encoding Rules (\ber)~\cite{rec2002x}, boolean values must comprise a singular octet, with $False$ denoted by setting all bits to $0$ and $True$ denoted by setting at least one bit to $1$. The \der further mandates that the value $True$ is signified by setting all bits to $1$. We capture these requirements of \der boolean in \agda by defining a type that holds not only the boolean value and its $8$-bit numerical representation but also a proof that this representation is correct. To further illustrate, let us look at the \agda code below. 

\begin{figure}[h]
  \centering
  \begin{code}
data BoolRep : Bool -> UInt8 -> Set where
  falser : BoolRep false (UInt8.fromN 0)
  truer  : BoolRep true (UInt8.fromN 255)


record BoolValue (@0 bs : List UInt8) : Set where
  constructor mkBoolValue
  field
    v     : Bool
    @0 b  : UInt8
    @0 vr : BoolRep v b
    @0 bseq : bs == [ b ]
  \end{code}
  \caption{\agda example for representing \der boolean type}
  \label{fig:code1}
\end{figure}

Here, |BoolRep| is a dependent type representing a binary relationship between \agda |Bool| values (\ie, true, false) and |UInt8| (\ie, 8-bit unsigned integers or octet values stipulated by the \xsno \der), where the |falser| constructor associates the false boolean value with $0$, and the |truer| constructor associates true with $255$. The function |UInt8.fromN| transforms a non-negative unbounded integer into its equivalent |UInt8| representation. It is important to note that this transformation is contingent upon \agda's ability to automatically verify that the provided number is less than $256$. Also, the keyword |Set| (referred to as the type of types) defines the type of |BoolRep|, indicating that |BoolRep| maps specific pairs of |Bool| and |UInt8| values to unique types. Subsequently, we can construct a dependent and parameterized record type, |BoolValue|, to represent the boolean value defined by \xsno. This record type, essentially a predicate over byte-strings, includes the boolean value |v|, its byte-string representation |b|, a proof |vr| that |b| is the correct representation of |v|, and a proof |bseq| that the byte-string representation |bs| of this grammatical terminal is a singleton list containing |b|. The |@0| annotations applied to types and fields specify that these values are erased at runtime to minimize execution overhead and to mark parts of the formalization used solely for verification purposes. In short, |BoolRep| verifies the correct mapping between boolean values and their numerical representations, while |BoolValue| holds the boolean value, its numerical representation, and the proof of the correctness of this representation, returned by the |BoolRep|.

\subsubsection{The Oracle of Morpheus}
\label{mor}
\morpheus~\cite{yahyazadeh2021morpheus} provides a rigorously validated oracle of the RSA $PKCS\#1-v1.5$~\cite{moriarty2016pkcs} signature verification, the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. The system accepts several parameters as input, such as a hexadecimal list of bytes representing the structure obtained after performing the modular exponentiation of the \texttt{SignatureValue} using the public exponent of the certificate issuer's RSA public key, the length of the public modulus of the RSA public key, the hash value of \texttt{TbsCertificate} in bytes, and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, returning true if the signature verification passes and false if it does not.



\subsection{Design of ARMOR}

\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.67]{img/arch.pdf} \\
  \caption{Overview of \armor}
  \label{armor}
  \end{figure}

Figure~\ref{armor} shows the high-level architecture of \armor, which consists of four core modules: \driver, \parser, \stringtransformer, and \semantic. As discussed in Section~\ref{sem}, the \driver module, written in \python, takes the input certificates in a single \pem file. We assume the input \pem file contains all the certificates in order. That means we rely on the sender to provide the end-entity and CA certificates with a valid certification path. Therefore, we do not include the \chain module in our implementation to ease our verification steps. However, we formally verified the most challenging steps, such as parsing, string transformation, and semantic validation using the \agda theorem prover. Note that we execute signature verification and trust anchor check outside our verified \semantic module. Finally, our \driver module manages the I/O operations and directs the external calls needed to execute signature verification (based on the oracle of \morpheus) and trust anchor check. As mentioned in Section~\ref{mor}, some inputs to the \morpheus's oracle require pre-processing with cryptographic operations, such as \textit{modular exponentiation} and \textit{hashing}, for which we leverage \python's \cryptography library~\cite{crypto}. 



\subsection{Implementation Details}
\label{imp}
Now we provide details on our implementation, including the reasons behind specific design choices.


\subsubsection{Parser Module} The \parser module includes both a \basesf decoder and a \der certificate parser. In our current configuration, we support $10$ certificate extensions, similar to previous study~\cite{debnath2021re}. These extensions are selected based on their high frequency of occurrence in practice, providing a comprehensive coverage for the most common scenarios encountered in certificate parsing and semantic checking. The list of extensions supported by \armor are-- Basic Constraints, Key Usage, Extended Key Usage, Authority Key Identifier, Subject Key Identifier, Subject Alternative Name, Issuer Alternative Name, Certificate Policy, CRL Distribution Points, and Authority Information Access.

% \begin{table}[h]
%   \setlength\extrarowheight{1.2pt}
%   \setlength{\tabcolsep}{1.5pt}
%   \centering
%   \sffamily\tiny
%   \caption{TODO: Fix this table}
%   \sffamily\tiny
%   \begin{tabular}{||l||c||c||l||c||c||}
%   \hline
%   \textbf{Extension}                                  & \textbf{Freq.} & \textbf{Perc.} & \textbf{Extension}                              & \multicolumn{1}{||c||}{\textbf{Freq.}} & \multicolumn{1}{||c||}{\textbf{Perc.}} \\ \hline
%   {\color[HTML]{00009B} Basic Constraints}            & 1,182,963,794           & 95.85\%             & {\color[HTML]{00009B} Issuer Alternative Names} & 1,577,915                                   & 0.12\%                                   \\ \hline
%   {\color[HTML]{00009B} Authority Key Identifier}     & 1,179,639,634           & 95.57\%             & Subject Directory Attributes                    & 14,881                                     & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Subject Alternative Name}     & 1,172,888,944           & 95.03\%             & Name Constraints                                & 7,600                                      & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Subject Key Identifier}       & 1,170,590,756           & 94.85\%             & Freshest CRL                                    & 6,587                                      & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Key Usage}                    & 1,155,599,607           & 93.63\%             & Policy Constraints                              & 451                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Extended Key Usage}           & 1,151,884,357           & 93.33\%             & Policy Mapping                                  & 347                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Authority Information Access} & 1,141,133,734           & 92.46\%             & Subject Information Access                      & 337                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Certificate Policy}           & 1,138,776,440           & 92.27\%             & Inhibit Policy                                  & 253                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} CRL Distribution Points}      & 278,689,659            & 22.58\%             & \multicolumn{3}{l}{}     \\ \hline                                                                                                           
%   \end{tabular}
%   \label{ext_freq}
%   \end{table}

\subsubsection{String-transformer Module} To verify the semantic check related to name chaining, our approach involves matching the issuer name from a certificate with the subject name present in its issuer CA certificate. This matching algorithm is defined in Section 7.1 of RFC-5280 and necessitates all the strings to undergo a preprocessing phase using the LDAP \stringprep profile, as described in RFC-4518~\cite{zeilenga2006lightweight}. However, the wide variety of languages and character sets present many cases to cover, leading to considerable complexity. Our initial implementation, which encapsulated all the transformations in a single \agda module, overwhelmed the compiler due to the sheer volume of cases. As a solution, we have divided the transformations across $16$ sub-modules, allowing for their sequential compilation, thereby enhancing the system's efficiency and manageability without compromising the comprehensiveness of the transformations.

\subsubsection{Semantic-checker Module}
\label{sec:semantic-checker}
We currently support $28$ semantic properties; Of these, $18$ properties are applicable for verifying compliance within a single certificate, while the remaining ten are related to checking properties across different certificates in a chain. The specific semantic properties we cover are listed in Table~\ref{scp} and~\ref{ccp} of the Appendix~\ref{app}. Note that we conduct the signature verification and trust anchor check outside the verified \agda code due to the computational complexity of these tasks and the requirements of external cryptographic libraries. \\
\textbf{Signature Verification:} We currently support only RSA signature verification, primarily because over $95\%$ of certificates employ RSA public keys, corroborated by our measurement studies on $1.5$ billion real certificates in the \censys dataset~\cite{censys}. However, the RSA Signature verification process necessitates the application of specific cryptographic operations on the \texttt{SignatureValue} field, parsing the signed data's hash digest, and the execution of the actual verification process. Given that we do not model and verify cryptography in the \agda code, we utilize \python's \cryptography library and \morpheus's formally verified code to perform the signature verification externally. This approach allows us to focus on leveraging \agda's strengths in formal verification of the parsing and validation logic while outsourcing the computationally-intensive cryptographic operations to established, trusted libraries in \python and \morpheus. \\
\textbf{Trust Anchor Check:} The trust anchor check generally involves verifying if the root CA certificate is present in the trusted CA store of the verifier's system. However, in practice, this root store can also include intermediate CA certificates or even the end-entity certificate itself. This allows the validation process to proceed in reverse order, starting from the end-entity certificate and moving toward the root CA certificate until a match is found in the trusted CA store. Given that this process can be accomplished by directly mapping the \der bytestring of the input certificates to those in the trusted store, we delegate this task to our driver module as the final step in the validation process. This division of labor allows us to leave the straightforward task of bytestring comparison to the \driver module.


\subsubsection{Verified Agda Code to Executable Binary} \agda is primarily a proof assistant, not commonly used to produce executable binaries directly. However, we can indirectly produce executable binaries by compiling \agda code to \haskell and then using \ghc~\cite{ghc} to generate an executable. This process begins with creating an \agda program, enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an executable binary using the \ghc \haskell compiler. However, the generated executable may not be as efficient as code written directly in \haskell.



\subsubsection{Driver Module}
The \driver module, written in \python, is a crucial intermediary that links the call to the executable \agda binary with the input certificate chain. It also manages the calls to the external processes responsible for signature verification and trust anchor check. After all these semantic checks, the driver module collates the result of certificate chain validation to present to the verifier.



\subsubsection{Trusted Computing Base (TCB)} Our TCB comprises the \agda toolchain, which includes its native type-checker, compiler, and standard library. In addition, we trust the correctness of the \ghc \haskell compiler to generate the executable binary. Furthermore, we assume the cryptographic operations provided by \python's \cryptography library are correct. Lastly, we assume that the verifier's trust anchor (\ie, the trusted root CA store) is up-to-date and does not contain any malicious certificates.
