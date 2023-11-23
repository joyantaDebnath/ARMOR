\section{Design and Implementation of ARMOR} 
In this section, we introduce the \agda theorem prover~\cite{bove2009brief, No07_Agda}, central to our formal verification efforts, and then discuss the architecture of ARMOR, along with its implementation challenges and details.



\subsection{Preliminaries on \agda Theorem Prover}
\agda~\cite{bove2009brief, No07_Agda} is a powerful and expressive programming language
that combines functional programming and formal verification.
At its core, \agda is a \textit{dependently-typed} functional programming
language, which allows types to refer to terms.
This capability helps express rich properties in types, with typechecking
enforcing that programs satisfy those properties.
In other words, if a program compiles, it is also proven to meet the
specifications described by its type.
Under the \emph{Curry-Howard}
correspondence~\cite{SU06_Lectures-on-the-Curry-Howard-Isomorphism}, we can view
\agda's types as \emph{propositions} and its terms as \emph{proofs} of the
propositions expressed by their types.
This makes \agda a powerful tool for both expressing programs and their
correctness, as the language of programs and proofs is unified.

\textbf{An Example of \agda's Syntax.} Consider the example shown in
Figure~\ref{fig:agda-ex} of length-indexed lists, provided as part of the \agda
standard library as |Vec|. 
\begin{figure}
  \centering
  \begin{code}
data Vec (A : Set) : Nat -> Set where
  vnil : Vec A 0
  vcons : forall {n} -> A -> Vec A n -> Vec A (1 + n)

head : forall {A n} -> Vec A (1 + n) -> A
head (vcons hd tl) = hd
  \end{code}
  \caption{Length-indexed lists in Agda}
  \label{fig:agda-ex}
\end{figure}
By length-indexed, we mean that the length of the list is itself part of the
type.
We now briefly explain the code listing in the figure.
\begin{itemize}
\item |Set| is the type of (small) types. Note that, we skip the details of \agda's
  universe hierarchy since it is beyond the scope of this paper.
  
\item The |data| keyword indicates that we are declaring |Vec| as an \emph{inductive
    family} indexed by a type |A| and a natural number. By \emph{inductive
    family}, we mean that for each type |A| and natural number |n|, |Vec A n| is
  a unique type -- the type for lists with exactly |n| elements of type |A|).
  
\item |Vec| has two \emph{constructors}, |vnil| for the empty list and |vcons|
  for a list with at least one element.
  The constructors encode the connection between the number of elements and the
  natural number index: |vnil| has type |Vec A 0| and |vcons| produces a list
  with one more element than the tail of the list.
 
\item Curly braces indicate function arguments that need not be passed
  explicitly, leaving \agda to infer their values from the types of other
  arguments to the function.
  For example, we can write |vcons 0 vnil|, and \agda will know this has type
  |Vec Nat 1|, as the only correct instantiation of parameter |n| of |vcons| 
  is |0|.
\end{itemize}

Tracking the length of lists statically allows us to express correctness
properties in the types of functions producing or consuming them.
As a simple example, the second definition of Figure~\ref{fig:agda-ex}, |head|,
expresses in its type that the list it consumes must have at least one element
(denoted by |Vec A (1 + n)|).
Because of this, in the definition of |head| we do not need to consider the case
that the argument is an empty list. Through a process called \emph{dependent
  pattern matching}~\cite{Co92_Pattern-Dependent-Types}, \agda determines that
the equation \(0 = 1 + n\) is impossible to solve for the natural numbers, and
thus the empty list can never be a well-typed argument to |head|.

% Note that we can generate an executable binary of the implementation by first compiling the \agda source code into \haskell and then using a \haskell compiler to compile the generated \haskell code into a binary. 

% As an example of \agda's syntax, consider representing the \agda boolean values
% in their \xsno \der counterparts.
% As per the Basic Encoding Rules (\ber)~\cite{rec2002x}, boolean values must
% comprise a singular octet, with $False$ denoted by setting all bits to $0$ and
% $True$ denoted by setting at least one bit to $1$.
% The \der further mandates that the value $True$ is signified by setting all bits
% to $1$.
% We capture these requirements of \der boolean in \agda by defining a type that
% holds not only the boolean value and its $8$-bit numerical representation but
% also a proof that this representation is correct.
% To further illustrate, let us look at the \agda code below.  

% \begin{figure}[h]
%   \centering
%   \begin{code}
% data BoolRep : Bool -> UInt8 -> Set where
%   falser : BoolRep false (UInt8.fromN 0)
%   truer  : BoolRep true (UInt8.fromN 255)


% record BoolValue (@0 bs : List UInt8) : Set where
%   constructor mkBoolValue
%   field
%     v     : Bool
%     @0 b  : UInt8
%     @0 vr : BoolRep v b
%     @0 bseq : bs == [ b ]
%   \end{code}
%   \caption{\agda example for representing \der boolean type}
%   \label{fig:code1}
% \end{figure}

% Here, |BoolRep| is a dependent type representing a binary relationship between
% \agda |Bool| values (\ie, true, false) and |UInt8| (\ie, 8-bit unsigned
% integers or octet values stipulated by the \xsno \der), where the |falser|
% constructor associates the false boolean value with $0$, and the |truer|
% constructor associates true with $255$. The function |UInt8.fromN| transforms
% a non-negative unbounded integer into its equivalent |UInt8| representation.
% It is important to note that this transformation is contingent upon \agda's
% ability to automatically verify that the provided number is less than $256$.
% Also, the keyword |Set| (referred to as the type of types) defines the type of
% |BoolRep|, indicating that |BoolRep| maps specific pairs of |Bool| and |UInt8|
% values to unique types. Subsequently, we can construct a dependent and
% parameterized record type, |BoolValue|, to represent the boolean value defined
% by \xsno. This record type, essentially a predicate over byte-strings,
% includes the boolean value |v|, its byte-string representation |b|, a proof
% |vr| that |b| is the correct representation of |v|, and a proof |bseq| that
% the byte-string representation |bs| of this grammatical terminal is a
% singleton list containing |b|. The |@0| annotations applied to types and
% fields specify that these values are erased at runtime to minimize execution
% overhead and to mark parts of the formalization used solely for verification
% purposes. In short, |BoolRep| verifies the correct mapping between boolean
% values and their numerical representations, while |BoolValue| holds the
% boolean value, its numerical representation, and the proof of the correctness
% of this representation, returned by the |BoolRep|.

% \subsubsection{The Oracle of Morpheus}
% \label{mor}
% \morpheus~\cite{yahyazadeh2021morpheus} provides a rigorously validated oracle of the RSA $PKCS\#1-v1.5$~\cite{moriarty2016pkcs} signature verification, the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. The system accepts several parameters as input, such as a hexadecimal list of bytes representing the structure obtained after performing the modular exponentiation of the \texttt{SignatureValue} using the public exponent of the certificate issuer's RSA public key, the length of the public modulus of the RSA public key, the hash value of \texttt{TbsCertificate} in bytes, and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, returning true if the signature verification passes and false if it does not.



\subsection{Architecture of ARMOR}

\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.7]{img/armor.drawio.pdf} \\
  \caption{Architecture of \armor}
  \label{armor}
  \end{figure}

Figure~\ref{armor} shows the high-level architecture of \armor, which consists
of four core modules: \driver, \parser, \stringtransformer, and \semantic.
As discussed in Section~\ref{sem}, the \driver module, written in \python, takes
the input certificates in a single \pem file.
We assume the input \pem file contains all the certificates in order.
That means we rely on the sender to provide the end-entity and CA certificates
with a valid certification path.
Therefore, we do not include the \chain module in our implementation to ease our
verification steps.
However, we formally verified the most challenging steps, such as parsing,
string transformation\todo{CJ: We have not!}, and semantic validation using the \agda theorem prover.
Note that we execute signature verification and trust anchor check outside our verified \semantic module. Finally, our \driver module manages the I/O operations and directs the external calls needed to execute signature verification (based on the oracle of \morpheus) and trust anchor check. As mentioned in Section~\ref{mor}, some inputs to the \morpheus's oracle require pre-processing with cryptographic operations, such as \textit{modular exponentiation} and \textit{hashing}, for which we leverage \python's \cryptography library~\cite{crypto}. 



\subsection{Implementation Details}
\label{imp}
Now we provide details on our implementation, including the reasons behind specific design choices.


\subsubsection{Parser Module} The \parser module includes both a \basesf decoder and a \der certificate parser. In our current configuration, we support $10$ certificate extensions. These extensions are selected based on their high frequency of occurrence in practice, providing a comprehensive coverage for the most common scenarios encountered in certificate parsing and semantic checking. When any other extension is present, we only consume the corresponding bytes of the extension to continue parsing rest of the certificate fields.
Table~\ref{extfreq} shows our analysis on the frequency of different extensions based on $1.5$ billion real certificates collected from the \censys~\cite{censys} certificate repository in January $2022$. Based on this measurement study, we support the following extensions-- Basic Constraints, Key Usage, Extended Key Usage, Authority Key Identifier, Subject Key Identifier, Subject Alternative Name, Issuer Alternative Name, Certificate Policy, CRL Distribution Points, and Authority Information Access.


\begin{table}[h]
  \captionsetup{font=footnotesize}
  \centering
       \setlength\extrarowheight{1.5pt}
       \setlength{\tabcolsep}{1.5pt}
       \sffamily\scriptsize
  \caption{Frequencies of extensions in \censys certificates}
  \sffamily\scriptsize
  Freq = Frequency \quad  Perc = Percentage \enskip
        \vspace{0.5em}
        \label{extfreq}
        \sffamily\tiny
    \centering
  \begin{tabular}{||l||c||c||l||c||c||}
  \hline
  \textbf{Extension}                                  & \textbf{Freq} & $\approx$ \textbf{Perc} & \textbf{Extension}                              & \multicolumn{1}{||c||}{\textbf{Freq}} & \multicolumn{1}{||c||}{$\approx$ \textbf{Perc}} \\ \hline
  {\color[HTML]{00009B} Basic Constraints}            & 1,381,870,876           & 92\%             & {\color[HTML]{00009B} Issuer Alternative Names} & 2,36,050                                   & 0\%                                   \\ \hline
  {\color[HTML]{00009B} Authority Key Identifier}     & 1,292,396,530           & 86\%             & Subject Directory Attributes                    & 5,090                                     & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Subject Alternative Name}     & 1,415,148,751           & 94\%             & Name Constraints                                & 33,821                                      & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Subject Key Identifier}       & 1,305,739,909           & 87\%             & Freshest CRL                                    & 1,171                                      & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Key Usage}                    & 1,335,398,382           & 89\%             & Policy Constraints                              & 34                                       & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Extended Key Usage}           & 1,357,755,474           & 91\%             & Policy Mapping                                  & 9                                       & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Authority Information Access} & 1,257,051,609           & 84\%             & Subject Information Access                      & 19                                       & 0\%                                      \\ \hline
  {\color[HTML]{00009B} Certificate Policy}           & 1,272,318,842           & 85\%             & Inhibit Policy                                  & 7                                       & 0\%                                      \\ \hline
  {\color[HTML]{00009B} CRL Distribution Points}      & 1,45,932,655            & 9\%             & \multicolumn{3}{c||}{\textbf{Total Certificates} = 1,500,000,000}     \\ \hline                                                                                                          
  \end{tabular}
  \end{table}

\subsubsection{String-transformer Module} To verify the semantic check related to name chaining, our approach involves matching the issuer name from a certificate with the subject name present in its issuer CA certificate. This matching algorithm is defined in Section 7.1 of RFC-5280 and necessitates all the strings to undergo a preprocessing phase using the LDAP \stringprep profile, as described in RFC-4518~\cite{zeilenga2006lightweight}. However, the wide variety of languages and character sets present many cases to cover, leading to considerable complexity. Our initial implementation, which encapsulated all the transformations in a single \agda module, overwhelmed the compiler due to the sheer volume of cases. As a solution, we have divided the transformations across $16$ sub-modules, allowing for their sequential compilation, thereby enhancing the system's efficiency and manageability without compromising the comprehensiveness of the transformations.

\subsubsection{Semantic-checker Module}
\label{sec:semantic-checker}
We currently support $23$ semantic properties; see Table~\ref{rules} in Appendix. Of these, $18$ properties (R1-R18) are applicable for verifying compliance within a single certificate, while the remaining $5$ (R19-R23) are related to checking properties across different certificates in a chain. Note that we conduct the signature verification (R26) and trust anchor check (R25) outside the verified \agda code due to the computational complexity of these tasks and the requirements of external cryptographic libraries. \\
\textbf{Signature Verification:} We currently support only RSA signature verification, primarily because over $96\%$ of certificates employ RSA public keys, corroborated by our measurement studies on the $1.5$ billion \censys~\cite{censys} certificates. However, the RSA Signature verification process necessitates the application of specific cryptographic operations on the \texttt{SignatureValue} field, parsing the signed data's hash digest, and the execution of the actual verification process. Given that we do not model and verify cryptography in the \agda code, we utilize \python's \cryptography library and \morpheus's formally verified code to perform the signature verification externally. This approach allows us to focus on leveraging \agda's strengths in formal verification of the parsing and validation logic while outsourcing the computationally-intensive cryptographic operations to established, trusted libraries in \python and \morpheus. \\
\textbf{Trust Anchor Check:} The trust anchor check generally involves verifying if the root CA certificate is present in the trusted CA store of the verifier's system. However, in practice, this root store can also include intermediate CA certificates or even the end-entity certificate itself. This allows the validation process to proceed in reverse order, starting from the end-entity certificate and moving toward the root CA certificate until a match is found in the trusted CA store. Given that this process can be accomplished by directly mapping the \der bytestring of the input certificates to those in the trusted store, we delegate this task to our driver module as the final step in the validation process. This division of labor allows us to leave the straightforward task of bytestring comparison to the \driver module.


\subsubsection{Verified Agda Code to Executable Binary} \agda is primarily a proof assistant, not commonly used to produce executable binaries directly. However, we can indirectly produce executable binaries by compiling \agda code to \haskell and then using \ghc~\cite{ghc} to generate an executable. This process begins with creating an \agda program, enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an executable binary using the \ghc \haskell compiler. However, the generated executable may not be as efficient as code written directly in \haskell.



\subsubsection{Driver Module}
The \driver module, written in \python, is a crucial intermediary that links the call to the executable \agda binary with the input certificate chain. It also manages the calls to the external processes responsible for signature verification and trust anchor check. After all these semantic checks, the driver module collates the result of certificate chain validation to present to the verifier.



\subsubsection{Trusted Computing Base (TCB)} Our TCB comprises the \agda toolchain, which includes its native type-checker, compiler, and standard library. In addition, we trust the correctness of the \ghc \haskell compiler to generate the executable binary. Furthermore, we assume the cryptographic operations provided by \python's \cryptography library are correct. Lastly, we assume that the verifier's trust anchor (\ie, the trusted root CA store) is up-to-date and does not contain any malicious certificates.
