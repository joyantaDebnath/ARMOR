\section{Implementation}
% We now discuss implementation details of \armor.

\noindent\textbf{Driver and Input Interface.} 
The \armor's driver module is developed using both \python and \agda programming languages. 
The \python component is responsible for the user interface, handling inputs such as certificates 
in DER or PEM formats, trusted CA certificates in PEM format, and optionally, the intended purpose 
of the end-user certificate (e.g., Server Authentication, Client Authentication, Code Signing). 
% Email Protection, Time Stamping, or OCSP Signing). 
After receiving these inputs, the \python driver invokes the \agda component. 
On the \agda side, the current time is read directly from the system. 
This component then invokes the necessary parsers, builds the candidate certificate chains, 
and conducts semantic validation as required. Finally, it returns the feedback along with some parsed information 
(\ie, \field{Key Usage} purposes, \field{TBSCertificate} bytes, \field{SignatureValue} bytes, \field{SignatueAlgorithm}) 
to the \python side. Subsequently, the \python side takes over to perform signature verification and check the consistency 
of the specified purpose in the end-user certificate. The final result of the chain validation process is determined and 
provided by the \python implementation. 
% This dual-implementation approach leverages the strengths of both \python and \agda to ensure efficient and secure certificate validation.

\noindent\textbf{Chain Building and String Canonicalization.} 
We use the chain builder module to build candidate chains that can potentially
be validated after parsing. For ease of formal verification, we first create 
all candidate chains and then check each of their legitimacy, terminating when 
we have identified one such chain. Our chain builder module uses name matching, 
instead of using \field{AKI} (Authority Key Identifier) and \field{SKI} (Subject Key Identifier) 
extensions as these may not be present in an input certificate. Before name matching as part 
of the chain building, we normalize the names using LDAP StringPrep profile described in RFC 
4518~\cite{zeilenga2006lightweight}. Our chain building module's total correctness ensures that 
we consider all potential chains, the chains all start with a CA certificate in the root store, 
and the chain building process terminates.  

% Our Chain builder module locates the issuer CA certificate of the current certificate by matching the subject name of other given certificates. The algorithm to match two names are defined in Section
% 7.1 of RFC 5280, which requires all the Strings to be normalized with LDAP StringPrep profile described in RFC 4518~\cite{zeilenga2006lightweight}. Our chain building algorithm ensures if it successfully returns any candidate chain, the chain must start from a trust anchor, given by the validator.

\noindent\textbf{Semantic Validation.} For semantic validation, 
we consider a total of $27$ rules. The complete list is provided in Table~\ref{rules} of the Appendix. 
The first 18 rules (R1 - R18) are applicable to individual certificates in a chain, whereas 
the last 9 rules (R19 - R27) are for a chain of certificates. Note that the rules from R1 to R25 are 
implemented in \agda while R26 (signature verification) and R27 (certificate purpose check) are enforced 
by the \python side of driver module. Also, R24 (subject and issuer name chaining) and 
R25 (trust anchor check) are not explicitly enforced by the semantic validator since these checks are 
already enforced when candidate chains are built.

\noindent\textbf{Signature Verification.}
We currently support only RSA signature verification, primarily because over
$96\%$ of certificates employ RSA public keys, corroborated by our measurement
studies on the $1.5$ billion \censys~\cite{censys} certificates.
However, the RSA signature verification process necessitates the application 
of specific cryptographic operations, calculating modular exponentiation over the 
\field{SignatureValue} field, computing hash of \field{TBSCertificate}, and 
the execution of the actual verification process. Given that we do not model and 
verify cryptography in the \agda code, we use \python's cryptography library 
for doing \emph{modular exponentiation}. However, for high-assurance, we also 
utilize \haclstar~\cite{zinzindohoue2017hacl} and \morpheus~\cite{yahyazadeh2021morpheus}. 
\haclstar is a formally-verified cryptographic library developed in $F^*$ and compiled 
down to C. 
% 
% can be compiled into $C$ programs while retaining all its verified properties (\eg, memory safety, resistance to timing side-channel attacks, and functional correctness). 
In \armor, we specifically utilize \haclstar's \emph{hash function} implementations. 
In contrast, \morpheus is a formally verified implementation of 
% oracle of 
the RSA $\mathit{PKCS\#1-v1.5}$~\cite{moriarty2016pkcs} signature verification.
\morpheus checks the correctness of the signature format after performing the modular exponentiation of the 
\field{SignatureValue} using the public exponent of the certificate issuer's RSA public key, avoiding 
signature forgery attacks \cite{finney2006bleichenbacher}. 
% , 
% the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. 
% This oracle accepts several parameters as input, such as a hexadecimal list of bytes 
% representing the structure obtained after performing the modular exponentiation of the 
% \field{SignatureValue} using the public exponent of the certificate issuer's RSA public key, 
% the length of the public modulus of the RSA public key, the hash value of \field{TBSCertificate} in bytes, 
% and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, 
% returning true if the signature verification passes and false if it does not.


\noindent\textbf{Supported Extensions.}
In our current configuration of \armor, we support $14$ certificate extensions for parsing -- 
Basic Constraints, Key Usage, Extended Key Usage, Authority Key Identifier, Subject Key Identifier, 
Subject Alternative Name, Issuer Alternative Name, Certificate Policy, Policy Mapping, Policy Constraints, 
Inhibit anyPolicy, CRL Distribution Points, Name Constraints, and Authority Information Access. 
These extensions are selected based on their frequency of occurrence in practice, providing a comprehensive 
coverage for the most common scenarios encountered in certificate parsing~\cite{debnath2021re}. When any 
other extension is present, we only consume the corresponding bytes of the extension to continue 
parsing rest of the certificate fields. Our supported semantic validation rules are spread across the following 
$5$ extensions -- Basic Constraints, Key Usage, Extended Key Usage, Subject Alternative Name, and CRL Distribution Points.
\armor returns a rejection for any unrecognized critical extensions. 

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


\noindent\textbf{From \agda to Executable Binary.} 
\agda is primarily a proof assistant, not commonly used to produce executable binaries directly. 
However, we can indirectly produce executable binary by compiling the \agda code to \haskell 
and then using the \haskell compiler \ghc~\cite{ghc} to generate an executable. 
% This process 
% begins with enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} 
% command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an 
% executable binary using the \ghc compiler. However, in terms of runtime performance, the generated 
% executable may not be as efficient as the code written directly in \haskell.