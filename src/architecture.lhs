\section{Design and Implementation of \armor} 
The development of \armor entails four critical steps: (1) Consulting the X.509
specifications to extract the requirements for certificate chain validation and
then formally represent them; (2) Developing the actual implementation for X.509
certificate chain validation; (3) Employing an interactive theorem prover to
prove that the implementation meets the specified criteria;\todo{\tiny The
  separation between (2) and (3) is misleading, impls are correct by construction} and (4) Extracting
an executable binary from the validated implementation, serving as a reference
for future non-compliance checking and validation purposes. As the interactive
theorem prover, we choose \agda~\cite{bove2009brief, No07_agda} for \armor. In
this section, we first present a brief introduction to \agda, and then present
the architecture and the implementation details of \armor. 

\subsection{Background on \agda}
\agda is a \textit{dependently-typed} functional programming
language, meaning that types may involve term expressions\todo{\tiny Explain:
  program and data}.
This capability helps express rich properties in types, and enforcing that
programs satisfy those properties is reduced to typechecking.
In other words, if a program compiles, it is also proven to meet the
specifications described by its type.
Under the \emph{Curry-Howard}
correspondence~\cite{SU06_Lectures-on-the-Curry-Howard-Isomorphism}, we can view
\agda's types as \emph{propositions} and its terms as \emph{proofs} of the
propositions expressed by their types.
This makes \agda a powerful tool for both expressing programs and their
correctness, as it unifies the language of programs and proofs.

\textbf{Example.} Consider the example shown in
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
  \caption{Length-indexed lists in \agda}
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
  a unique type --- the type for lists with exactly |n| elements of type |A|).
  
\item |Vec| has two \emph{constructors}, |vnil| for the empty list and |vcons|
  for a list with at least one element.
  The constructors encode the connection between the number of elements and the
  natural number index: |vnil| has type |Vec A 0| and |vcons| produces a list
  with one more element than the tail of the list.
 
\item Curly braces indicate function arguments that need not be passed
  explicitly, leaving \agda to infer their values from the types of other
  arguments to the function.
  For example, we can write |vcons 5 vnil|, and \agda will know this has type
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

% % Note that we can generate an executable binary of the implementation by first compiling the \agda source code into \haskell and then using a \haskell compiler to compile the generated \haskell code into a binary. 

% % As an example of \agda's syntax, consider representing the \agda boolean values
% % in their \xsno \der counterparts.
% % As per the Basic Encoding Rules (\ber)~\cite{rec2002x}, boolean values must
% % comprise a singular octet, with $False$ denoted by setting all bits to $0$ and
% % $True$ denoted by setting at least one bit to $1$.
% % The \der further mandates that the value $True$ is signified by setting all bits
% % to $1$.
% % We capture these requirements of \der boolean in \agda by defining a type that
% % holds not only the boolean value and its $8$-bit numerical representation but
% % also a proof that this representation is correct.
% % To further illustrate, let us look at the \agda code below.  

% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% % data BoolRep : Bool -> UInt8 -> Set where
% %   falser : BoolRep false (UInt8.fromN 0)
% %   truer  : BoolRep true (UInt8.fromN 255)


% % record BoolValue (@0 bs : List UInt8) : Set where
% %   constructor mkBoolValue
% %   field
% %     v     : Bool
% %     @0 b  : UInt8
% %     @0 vr : BoolRep v b
% %     @0 bseq : bs == [ b ]
% %   \end{code}
% %   \caption{\agda example for representing \der boolean type}
% %   \label{fig:code1}
% % \end{figure}

% % Here, |BoolRep| is a dependent type representing a binary relationship between
% % \agda |Bool| values (\ie, true, false) and |UInt8| (\ie, 8-bit unsigned
% % integers or octet values stipulated by the \xsno \der), where the |falser|
% % constructor associates the false boolean value with $0$, and the |truer|
% % constructor associates true with $255$. The function |UInt8.fromN| transforms
% % a non-negative unbounded integer into its equivalent |UInt8| representation.
% % It is important to note that this transformation is contingent upon \agda's
% % ability to automatically verify that the provided number is less than $256$.
% % Also, the keyword |Set| (referred to as the type of types) defines the type of
% % |BoolRep|, indicating that |BoolRep| maps specific pairs of |Bool| and |UInt8|
% % values to unique types. Subsequently, we can construct a dependent and
% % parameterized record type, |BoolValue|, to represent the boolean value defined
% % by \xsno. This record type, essentially a predicate over byte-strings,
% % includes the boolean value |v|, its byte-string representation |b|, a proof
% % |vr| that |b| is the correct representation of |v|, and a proof |bseq| that
% % the byte-string representation |bs| of this grammatical terminal is a
% % singleton list containing |b|. The |@0| annotations applied to types and
% % fields specify that these values are erased at runtime to minimize execution
% % overhead and to mark parts of the formalization used solely for verification
% % purposes. In short, |BoolRep| verifies the correct mapping between boolean
% % values and their numerical representations, while |BoolValue| holds the
% % boolean value, its numerical representation, and the proof of the correctness
% % of this representation, returned by the |BoolRep|.



% \subsubsection{HACL*} \haclstar~\cite{zinzindohoue2017hacl} is a formally-verified cryptographic library developed in $F^*$ and can be compiled into $C$ programs while retaining all its verified properties (\eg, memory safety, resistance to timing side-channel attacks, and functional correctness). In \armor, we specifically utilize \haclstar's \emph{hash function} implementations during RSA signature $PKCS\#1-v1.5$~\cite{moriarty2016pkcs} verification.


% \subsubsection{Morpheus}
% \morpheus~\cite{yahyazadeh2021morpheus} is an oracle of the RSA $PKCS\#1-v1.5$~\cite{moriarty2016pkcs} signature verification, the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. This oracle accepts several parameters as input, such as a hexadecimal list of bytes representing the structure obtained after performing the modular exponentiation of the \texttt{SignatureValue} using the public exponent of the certificate issuer's RSA public key, the length of the public modulus of the RSA public key, the hash value of \texttt{TbsCertificate} in bytes, and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, returning true if the signature verification passes and false if it does not.

\subsection{Our Approach}

\subsubsection{Architecture Overview}
\begin{figure}[h]
  \centering
  \scriptsize
  \includegraphics[scale=0.65]{img/armor.drawio.pdf} \\
  Sub-modules marked with green color in Agda module are formally-verified \\
  \vspace{0.2cm}
  \caption{Architecture of \armor}
  \label{armor}
\end{figure}


\armor is designed and developed with modularity in mind. Inspired by prior work~\cite{debnath2021re, nqsb-tls}, 
we modularly decompose the whole \xfon certificate chain validation 
process into several stages. Such modularity facilitates both ease of implementation, 
manageability of the implementation, and also formal verification
efforts.\todo{\tiny Need map key, also explain in prose.}\todo{\tiny Table
  summary of formal guarantees?}
Figure~\ref{armor} depicts the architecture of \armor, which is divided into two main modules: the \emph{Python} module (implemented in \python) and the \emph{Agda} module (implemented in the \agda). Each module includes several sub-modules. \circled{A} The \emph{Driver} sub-module of the \emph{Python} module receives the inputs and \circled{B} forwards those inputs to the \emph{Main} sub-module of the \emph{Agda} module. The \emph{Main} sub-module then sequentially utilizes the \emph{PEM parser} (\circled{C} -- \circled{D}), \emph{Base64 decoder} (\circled{E} -- \circled{F}), and \emph{DER parser} (\circled{G} -- \circled{H}) to parse the input certificate files and represent all input certificates (end-user certificate, associated CA certificates, and trusted CA certificates) into their internal data structures. Then, (\circled{I} -- \circled{L}) it invokes the \emph{Chain builder} to generate all possible certificate chains from the parsed data, ensuring each chain originates from a trusted CA certificate. Note that, our chain building process depends on matching the \texttt{Subject} and \texttt{Issuer} names of subsequent certificates in a chain. This matching algorithm is defined in Section 7.1 of RFC 5280 and necessitates all the strings to undergo a preprocessing phase using the LDAP \stringprep profile, as described in RFC-4518~\cite{zeilenga2006lightweight}. Thus, during chain building, (\circled{G} -- \circled{H}) the \emph{String canonicalizer} is called to normalize the \texttt{Subject} and \texttt{Issuer} names.
  
  Next, (\circled{M} -- \circled{N}) the \emph{Main} sub-module tests each candidate chain for semantic validation. If any of the candidate chains passes the semantic validation, \circled{O} the \emph{Main} sub-module informs the \emph{Driver} in the \emph{Python} module. Notably, the \emph{Semantic validator} in the \emph{Agda} module does not perform any signature verification on the candidate chains since we do not implement and formally verify cryptographic operations in \armor. Hence, (\circled{P} -- \circled{U}) the \emph{Driver} in the \emph{Python} module calls upon the external \emph{Signature Verifier} for this task. The \emph{Signature verifier}, in turn, employs two formally-verified libraries -- (\circled{Q} -- \circled{R}) \haclstar~\cite{zinzindohoue2017hacl} and (\circled{S} -- \circled{T}) \morpheus~\cite{yahyazadeh2021morpheus} for the required cryptographic operations (details on \armor's signature verification is discussed later). Once the signature verification is successful, \circled{U} the \emph{Driver} is notified, and \circled{V} it then outputs the final chain validation result and the public-key of the end-user certificate.

\subsubsection{Our Insights on Technical Challenges} We now discuss our design choices to tackle the challenges discussed on Section 2. 

\textit{a. Choosing the boundary for parsing.}
In Section 2, we discussed the RFC 5280 specification, which comprises two main
rule sets: \emph{producer rules} and \emph{consumer rules}. Our formalization
specifically concentrates on the \emph{consumer rules}, which are intended for
certificate chain validation implementations.
Additionally, RFC 5280 can be categorized into \emph{syntactic} and \emph{semantic}
rules. A clear separation between these syntactic and semantic rules is pivotal in
formally specifying requirements.
However, having a balance is essential --- too many semantic checks incorporated into the parsing process can lead to an overly complex parser, while excluding all semantic checks during parsing can result in an overly lenient parser. Our strategy lies somewhere in the middle, taking inspiration from the re-engineering effort by Debnath \etal~\cite{debnath2021re}. Similar to that prior work, we categorize \der restrictions as part of the parsing rules, and the rest are left for semantic validation. We enforce the semantic check on \der's $<T, L, V>$ length bound into the parsing side, contributing to a manageable parser that maintains necessary rigor without becoming overly complex. 

\textit{b. Choosing the level of specificity.}
While the \xsno \der and RFC 5280 are comprehensive and detail numerous restrictions and possibilities, in reality, not all aspects of the specifications are uniformly or widely used. For example, not all the extensions specified in the standard are used in real-world certificates. In addition, RFC 5280 puts additional restrictions on certain \der rules to be used for the Internet. Therefore, we aim to create a formally verified implementation that focuses primarily on the most commonly used subset of the standard specifications. For example, in our current configuration of \armor, we support $10$ certificate extensions. These extensions are selected based on their high frequency of occurrence in practice, providing a comprehensive coverage for the most common scenarios encountered in certificate parsing and semantic checking. When any other extension is present, we only consume the corresponding bytes of the extension to continue parsing rest of the certificate fields. Table~\ref{extfreq} shows our analysis on the frequency of different extensions based on $1.5$ billion real certificates collected from the \censys~\cite{censys} certificate repository in January $2022$. Based on this measurement study, we support the following extensions: Basic Constraints, Key Usage, Extended Key Usage, Authority Key Identifier, Subject Key Identifier, Subject Alternative Name, Issuer Alternative Name, Certificate Policy, CRL Distribution Points, and Authority Information Access.

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


% \textbf{Challenge 3: Speeding up the string canonicalization} Our initial implementation, which encapsulated all the transformations in a single \agda module, overwhelmed the compiler due to the sheer volume of cases. As a solution, we have divided the transformations across $16$ sub-modules, allowing for their sequential compilation, thereby enhancing the system's efficiency and manageability without compromising the comprehensiveness of the transformations.



\textit{c. Tackling cryptographic operations.} Verification of cryptographic
operations is out of scope for this work.
Therefore, we rely on formally-verified external libraries for the task of signature verification. 
We currently support only RSA signature verification, primarily because over
$96\%$ of certificates employ RSA public keys, corroborated by our measurement
studies on the $1.5$ billion \censys~\cite{censys} certificates.
However, the RSA signature verification process necessitates the application of specific cryptographic operations on the \texttt{SignatureValue} field, parsing the signed data's hash digest, and the execution of the actual verification process. Given that we do not model and verify cryptography in the \agda code, we utilize \haclstar~\cite{zinzindohoue2017hacl} and \morpheus~\cite{yahyazadeh2021morpheus}. \haclstar is a formally-verified cryptographic library developed in $F^*$ and can be compiled into $C$ programs while retaining all its verified properties (\eg, memory safety, resistance to timing side-channel attacks, and functional correctness). In \armor, we specifically utilize \haclstar's \emph{hash function} implementations. In contrast, \morpheus is an oracle of the RSA $\mathit{PKCS\#1-v1.5}$~\cite{moriarty2016pkcs} signature verification, the formal correctness of which has been established using the \coq proof assistant~\cite{huet1997coq}. This oracle accepts several parameters as input, such as a hexadecimal list of bytes representing the structure obtained after performing the modular exponentiation of the \texttt{SignatureValue} using the public exponent of the certificate issuer's RSA public key, the length of the public modulus of the RSA public key, the hash value of \texttt{TBSCertificate} in bytes, and the name of the signature hash algorithm. Upon execution, the oracle provides a boolean outcome, returning true if the signature verification passes and false if it does not. This design choice allows us to focus on leveraging \agda's strengths in formal verification of the parsing and validation logic while outsourcing the computationally-intensive cryptographic operations to already verified implementations such as \haclstar and \morpheus.


\subsubsection{Verification Overview} 
Our verification effort on the \emph{Agda} module can be decomposed to the
verification of \emph{parsers (\ie, PEM parser, Base64 decoder, X.690 DER and
  X.509 parser)} and the verification of \emph{semantic validation}.
In this work, we only provide implementations of the \emph{String canonicalizer} and \emph{Chain builder}, however, we do not provide any formal specification and correctness guarantees for them. We now present a high-level overview on our verification efforts, while details on the verification and correctness proofs with their specific-challenges are discussed in Section 4. 

\noindent\textbf{Verification of Parsers:}  
We conceptually separate each parser verification task into \emph{language
  specification}, \emph{language security verification}, and \emph{parser
  correctness verification}. Since \agda enforces termination
for all definitions, we automatically get the \emph{termination} guarantee for each parser.

\textit{a. Language specification.} We provide parser-independent formalizations of the PEM, Base64, X.690
  DER, and \xfon formats, greatly reducing the complexity of the specification
  and increasing trust that they faithfully capture the natural language description. Much current research~\cite{ni2023asn1, ramananandro2019everparse}
for applying formal methods to parsing uses serializers to specify the
correctnes properties of parsers.
Formal proofs of correctness (in any context) are only ever as good as the
formal specification of those correctness properties, and by using serializers
as part of the specification, this earlier research swells the trusted computing
base by introducing implementation details. To avoid this issue, for our approach we use \emph{relational}
specifications of languages.
In addition to reducing the trusted computing base, this relational approach has
two other advantages: (1) it allows for a clear distinction between correctness
properties of the \emph{language} and \emph{parser}; and (2)
it brings the formal language specification into closer correspondence with the
natural language description.
This second point in particular means the formal specification can serve as a
machine-checked, rigorous alternative to the latter for developers seeking to
understand the relevant specifications X.509 and X.690 DER. 

% More concretely, the relational specifications we propose to give are of the
% following form.
% For a given language \(G\) with alphabet \(\Sigma\), a family of types
% \(\mathit{GSpec}\ \mathit{xs}\) where the family \(\mathit{GSpec}\) is indexed
% by strings \(\mathit{xs} \in \Sigma^*\) over the alphabet (for PEM the alphabet
% is characters, for X.690 it is unsigned 8-bit integers).
% Such a family of types can serve the dual role as the internal representation of
% the value encoded by \(\mathit{xs}\), i.e., a value of type \(\mathit{GSpec}\
% \mathit{xs}\) is not only a proof that \(\mathit{xs}\) is in the language \(G\),
% but also the internal representation of the value decoded from \(\mathit{xs}\).

% \emph{Example:}
% As a short example, the X.690 DER specification requires that signed integer
% values be encoded in the minimal number of bytes needed to express that value in
% binary two's complement.
% This can be concisely expressed as a type family that maps the empty bytestring
% to the empty type \texttt{False} (the encoding must consist of one byte), the
% bytestring consisting of single byte to the unital type \texttt{True} (a single
% byte is always minimal), and a bytestring with two or more elements to the
% proposition (encoded as a type) that: if the first byte has all bits 0, the
% second byte has its first bit set to 1; and if the first byte has all bits set
% to 1, the second byte's first bit is set to 0.
% As a type-level, relational encoding, we can use this property as an assumption
% to proofs that the grammar for integer values is \emph{non-malleable} without
% referencing the particular checks executed by our parsers to ensure conformance
% to it.

% \emph{Proof Term Erasure:}
% While convenient for proving, naively mixing data and specification can
% have undesirable effects on runtime performance.
% This is because in languages like Agda, proofs \emph{are} programs, and so they
% carry computational content.
% To prevent issue, we will leverage Agda's support for \emph{run-time
%   irrelevance} through erasure annotations, ensuring that computations existing
% only for specificational purposes are
% removed from compiled Haskell code by Agda's GHC backend, and therefore have no
% effect on performance.
% As a nice corollary to this, this improves the usability of our library as an
% machine-checked alternative to the relevant RFCs by clearly marking which
% components are purely for specificational purposes.

\textit{b. Language security verification.} We verify properties of the language specifications that give
  confidence they meet their desired design goals. X.509 certificates are required to use the X.690 DER, a set of encoding rules for ASN.1 types that is meant to ensure (1)
\emph{unambiguousness} (a bytestring cannot be a valid encoding of two distinct values)
and (2) \emph{non-malleability} (two distinct bytestrings cannot be valid encodings of
the same value). \emph{Unambiguousness} and \emph{non-malleability} are properties of a
given language, and proofs of these properties for \xfon and X.690 DER 
provide high-assurance for these formats \emph{themselves}, rather than for
parser and serializer implementations.
Our approach of giving parser-independent, relational specifications of
languages enables us to prove \emph{directly} that they hold for the supported
languages, without reference to implementation details of parsing or
serializing. Proofs of language properties also serve as useful lemmas for verifying
parser correctness.

% Proofs of language properties can also serve as useful lemmas for verifying
% parser correctness.
% As a relatively simple example, if during parsing one of the elements of a
% sequence of ASN.1 components fails to parse, then to guarantee parser
% completeness without resorting to back-tracking it is useful to establish that
% the sequence formed from the earlier, successfuly parsed components satisfy a
% \emph{unique prefix} property (at most one prefix of a given bytestring can be
% in the language).
% A more complicated example involves the handling of \emph{optional and default}
% fields within an ASN.1 sequence, meaning that encodings for those fields may be
% omitted.
% In such cases, it is essential that each component in a ``block'' of optional
% fields satisfy a \emph{no confusion} relation (if a prefix of a bytestring is in
% language \(G_1\), then no prefix of that bytestring is in language \(G_2\)) with
% respect to each other such component.
% This is not only critical for ensuring unambiguousness of the language (as is
% guarantees that the presences of one optional field is not mistaken for the
% presence of another), but also helps in proving parser completeness without
% resorting to back-tracking.

\textit{c. Parser correctness verification.}
We write parsers that are \emph{sound} and \emph{complete} by construction.
With a parser-independent characterization of a language established, these
properties of parsing can be expressed directly in terms of that
characterization.
Note that parser acceptance means that some prefix of the input was successfully
processed, with the parser returning not only the internal representation of the
parsed value but the remaining suffix of the input to be processed by parsers
for the languages denoted by the subsequent production rules.
With this in mind, \emph{soundness} of parsing with respect to language \(G\) means that,
if the parser accepts some prefix of an input string \(\mathit{xs}\), then that
prefix is in the language \(G\), and \emph{completeness} means that if \(\mathit{xs}\)
is \(G\), then the parser will accept some prefix of \(\mathit{xs}\) (possibly
all of \(\mathit{xs}\) itself).
In our approach, this is guaranteed by the types of the parsers themselves: if
the parser accepts a prefix of \(\mathit{xs}\), it returns a proof that
prefix is in \(G\), and if it rejects \(\mathit{xs}\), it returns a proof that
\emph{no prefix} of \(\mathit{xs}\) is in \(G\). 
That is to say, parsers are really proofs that membership (in \(G\)) of an
input’s prefix is decidable.


% Of course, this formulation of parser soundness and completeness is insufficient
% to address all concerns of security, even with proofs that the language being
% parsed is unambiguous and non-malleable.
% In particular, parsing completeness cannot guarantee that the only prefix of
% \(\mathit{xs}\) consumed by the parser is \(\mathit{xs}\) itself.
% This is, however, can be established by the \emph{language} property
% of \emph{unique prefixes}, discussed above.

% \mypara{Certificate Chain Building}
% \emph{We propose to develop a verified implementation of string preparation and
%   chain building}. 
% Recall that a certificate chain is a sequence of X.509 certificates that begins
% with the certificate of the entity being authenticated, ends with a trusted CA
% certificate, and has the property that for every adjacent pair of certificates,
% the first is signed by the owner of the second.
% A client seeking to authenticate a server must build these chains itself, and
% faces several challenges in doing so: certificates may be received out of order
% with respect to a chain, and multiple chains may include a single certificate as
% it may be cross-signed by multiple CAs.
% In addition, before chain building can begin certain certificate string
% attributes must be canonicalized using LDAP string preparation, a process
% complicated by the sheer size of the combined international character sets.

% Beginning with string preparation, our verification goal is establishing that
% the algorithm is fit for purpose by proving \emph{it induces an effective quotient,} as
% the goal of the algorithm is to provide a canonical representation for an
% equivalence class of strings across a wide range of character sets.
% For certificate chain building, we will first provide a specification of a valid
% chain as a list of certificates with the property that for every adjacent pair,
% the issuer of the first matches the subject of the second; this comprises the
% specification of \emph{chain building soundness.}
% Next, we will give a relational specification of what it means for a sound chain
% to be present in a list of certificates as a partial permutation of that list
% with the adjacent pair property; this comprises part of the specification of
% \emph{completeness}.
% Finally, we will implement chain building that, like our parsers, is \emph{sound
% and complete by construction}, where the full specification of completeness is
% that if a chain is present in the certificate list, the implementation generates
% that chain.

\noindent\textbf{Verification of semantic validator:} 
We provide formal specifications of semantic validation, and give a correct-by-construction implementation of the \emph{Semantic validator}.
The \xfon standard requires enforcement of certain properties (over both single
certificates and certificate chains) that fall outside the scope of parsing.
For example, within a single certificate certain fields (\eg, unique
identifiers, extensions) cannot appear unless permitted by the version of the
standard that the certificate indicates it is using; within a certificate chain,
if a CA certificate specifies a path length constraint, then the length of the
remainder of the chain following it must not exceed the given limit. Similar to \cite{debnath2021re}, we enumerated $X$ such single certificate and
certificate chain properties in total (see Table ? in Appendix). We translate each of these into type-level predicates so that they bear close correspondence to their natural language descriptions, then implement
semantic checking as proofs that these properties are \emph{decidable}. That means our implementation will not only return ``yes/no'' answers, but also \emph{proofs} that either affirm or refute that the predicate holds for the given certificate or the chain.



\noindent\textbf{Verified \agda Code to Executable Binary:} \agda is primarily a proof assistant, not commonly used to produce executable binaries directly. However, we can indirectly produce executable binaries by compiling the \agda code to \haskell and then using the \haskell compiler \ghc~\cite{ghc} to generate an executable. This process begins with enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an executable binary using the \ghc. However, in terms of runtime performance, the generated executable may not be as efficient as the code written directly in \haskell.

\noindent\textbf{Trusted Computing Base (TCB):} Our TCB comprises the \agda toolchain, which includes its native type-checker, compiler, and standard library. In addition, we trust the correctness of the \ghc \haskell compiler to generate the executable binary. Lastly, we assume that the verifier's trust anchor (\ie, the trusted root CA store) is up-to-date and does not contain any malicious certificates.