\section{Implementation}
We now discuss implementation details of \armor.

\subsection{Driver} 
The Armor's driver module is developed using both Python and Agda programming languages. The Python component is responsible for the user interface, handling inputs such as certificates in DER or PEM formats, trusted CA certificates in PEM format, and optionally, the intended purpose of the end-user certificate (like serverAuth, clientAuth, codeSigning, emailProtection, timeStamping, or OCSPSigning). After receiving these inputs, the Python part forwards them to the Agda component. On the Agda side, the system time is read directly. This component then invokes the necessary parsers, builds the candidate certificate chains, and conducts semantic validation as required. Finally, it returns feedback with some parsed information (\ie, \texttt{Key Usage} purposes, \texttt{TBSCertificate} bytes, \texttt{SignatureValue} bytes, \texttt{SignatueAlgorithm}) to the Python side. Subsequently, the Python side takes over to perform signature verification (details on Section~\ref{sigver}) and to check the consistency of the specified purpose in the end-user certificate. The final result of the chain validation process is determined and provided by the Python implementation. This dual-implementation approach leverages the strengths of both Python and Agda to ensure efficient and secure certificate validation.

\subsection{Chain Builder} 
\subsection{String Canonicalizer}
\subsection{Semantic Validator}

\subsection{Signature Verifier} \label{sigver}
We currently support only RSA signature verification, primarily because over
$96\%$ of certificates employ RSA public keys, corroborated by our measurement
studies on the $1.5$ billion \censys~\cite{censys} certificates.
However, the RSA signature verification process necessitates the application of specific cryptographic operations, calculating modular exponentiation over the \texttt{SignatureValue} field, computing hash of \texttt{TBSCertificate}, and the execution of the actual verification process. Given that we do not model and verify cryptography in the \agda code, we use \python's ``cryptography'' library for doing \emph{modular exponentiation}. However, for high-assurance, we utilize \haclstar~\cite{zinzindohoue2017hacl} and \morpheus~\cite{yahyazadeh2021morpheus}. \haclstar is a formally-verified cryptographic library developed in $F^*$ and can be compiled into $C$ programs while retaining all its verified properties (\eg, memory safety, resistance to timing side-channel attacks, and functional correctness). In \armor, we specifically utilize \haclstar's \emph{hash function} implementations. In contrast, \morpheus is an oracle of the RSA $\mathit{PKCS\#1-v1.5}$~\cite{moriarty2016pkcs} signature verification, the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. This oracle accepts several parameters as input, such as a hexadecimal list of bytes representing the structure obtained after performing the modular exponentiation of the \texttt{SignatureValue} using the public exponent of the certificate issuer's RSA public key, the length of the public modulus of the RSA public key, the hash value of \texttt{TBSCertificate} in bytes, and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, returning true if the signature verification passes and false if it does not.


\subsection{Supported Extensions}
In our current configuration of \armor, we support $14$ certificate extensions for parsing -- Basic Constraints, Key Usage, Extended Key Usage, Authority Key Identifier, Subject Key Identifier, Subject Alternative Name, Issuer Alternative Name, Certificate Policy, Policy Mapping, Policy Constraints, Inhibit anyPolicy, CRL Distribution Points, Name Constraints, and Authority Information Access. These extensions are selected based on their frequency of occurrence in practice, providing a comprehensive coverage for the most common scenarios encountered in certificate parsing~\cite{debnath2021re}. When any other extension is present, we only consume the corresponding bytes of the extension to continue parsing rest of the certificate fields. Our supported semantic validation rules are spread across the following $5$ extensions -- Basic Constraints, Key Usage, Extended Key Usage, Subject Alternative Name, and CRL Distribution Points.

% \begin{table}[h]
%   \captionsetup{font=footnotesize}
%   \centering
%        \setlength\extrarowheight{1.5pt}
%        \setlength{\tabcolsep}{1.5pt}
%        \sffamily\scriptsize
%   \caption{Frequencies of extensions in \censys certificates}
%   \sffamily\scriptsize
%   Freq = Frequency \quad  Perc = Percentage \enskip
%         \vspace{0.5em}
%         \label{extfreq}
%         \sffamily\tiny
%     \centering
%   \begin{tabular}{||l||c||c||l||c||c||}
%   \hline
%   \textbf{Extension}                                  & \textbf{Freq} & $\approx$ \textbf{Perc} & \textbf{Extension}                              & \multicolumn{1}{||c||}{\textbf{Freq}} & \multicolumn{1}{||c||}{$\approx$ \textbf{Perc}} \\ \hline
%   {\color[HTML]{00009B} Basic Constraints}            & 1,381,870,876           & 92\%             & {\color[HTML]{00009B} Issuer Alternative Names} & 2,36,050                                   & 0\%                                   \\ \hline
%   {\color[HTML]{00009B} Authority Key Identifier}     & 1,292,396,530           & 86\%             & Subject Directory Attributes                    & 5,090                                     & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Subject Alternative Name}     & 1,415,148,751           & 94\%             & Name Constraints                                & 33,821                                      & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Subject Key Identifier}       & 1,305,739,909           & 87\%             & Freshest CRL                                    & 1,171                                      & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Key Usage}                    & 1,335,398,382           & 89\%             & Policy Constraints                              & 34                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Extended Key Usage}           & 1,357,755,474           & 91\%             & Policy Mapping                                  & 9                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Authority Information Access} & 1,257,051,609           & 84\%             & Subject Information Access                      & 19                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} Certificate Policy}           & 1,272,318,842           & 85\%             & Inhibit Policy                                  & 7                                       & 0\%                                      \\ \hline
%   {\color[HTML]{00009B} CRL Distribution Points}      & 1,45,932,655            & 9\%             & \multicolumn{3}{c||}{\textbf{Total Certificates} = 1,500,000,000}     \\ \hline                                                                                                          
%   \end{tabular}
%   \end{table}


\subsection{From Agda to Executable Binary} \agda is primarily a proof assistant, not commonly used to produce executable binaries directly. However, we can indirectly produce executable binary by compiling the \agda code to \haskell and then using the \haskell compiler \ghc~\cite{ghc} to generate an executable. This process begins with enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an executable binary using the \ghc compiler. However, in terms of runtime performance, the generated executable may not be as efficient as the code written directly in \haskell.