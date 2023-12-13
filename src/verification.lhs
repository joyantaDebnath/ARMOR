\section{Verification Goals and Correctness Proofs}
We now discuss \armor{}'s correctness proofs. 
% Recall that, as shown in Figure~\ref{armor}, 
We provide formal correctness guarantees for the
following modules of \armor: \emph{parsers (\ie, PEM, X.690 DER, and
  X.509 parsers)}, \emph{Base64 decoder}, \emph{Semantic validator}, and \emph{Chain builder} (see
Table~\ref{table:summary-of-guarantees} for a summary of guarantees organized by
module).
% A summary of these guarantees is in Table \ref{table:summary-of-guarantees}. 
%   , and
% \emph{String canonicalizer}.
For these verification tasks, 
which took 12 person months to complete, we use the \agda interactive theorem
prover~\cite{bove2009brief, No07_agda}. 
% Due to space constraints, we only discuss the correctness guarantees of the X.690 DER and X.509 parsers, 
% and relegate the discussion of the other components in the full version of the
% paper \cite{armor-full-version};
See Table~\ref{tab:app-formal-guarantees} for a
listing and brief description of all formal guarantees proven.

% In this section, we briefly introduce Agda and then detail the
% design and verified guarantees of \armor's \agda modules.

\begin{table}[t]
  % \captionsetup{font=footnotesize}
\centering
\sffamily\scriptsize
  \setlength\extrarowheight{1.5pt}
  \setlength{\tabcolsep}{1.5pt}
  \caption{Correctness guarantees for each module in \armor}
  \label{table:summary-of-guarantees}
  \sffamily\scriptsize
\centering
\resizebox{.48\textwidth}{!}{%
\begin{tabular}{c||c||c||c||c||c||}
\cline{2-6}
\textbf{}                                                                                                        & \textbf{\begin{tabular}[c]{@@{}c@@{}}PEM \\ Parser\end{tabular}}                              & \textbf{\begin{tabular}[c]{@@{}c@@{}}Base64 \\ Decoder\end{tabular}}             & \textbf{\begin{tabular}[c]{@@{}c@@{}}DER\\ Parser\end{tabular}}             & \textbf{\begin{tabular}[c]{@@{}c@@{}}Chain \\ Builder\end{tabular}}              & \textbf{\begin{tabular}[c]{@@{}c@@{}}Semantic\\ Validator\end{tabular}}          \\ \hline
\multicolumn{1}{||c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Correctness\\ Properties\end{tabular}}} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Maximal\\ Terminating\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminating\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminating\end{tabular}             & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminating\end{tabular}                                                                    & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminating\end{tabular} \\ \hline
\multicolumn{1}{||c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Language\\ Security\\ Properties\end{tabular}}}          & Unambiguous                                                                             & N/A                                                                            & \begin{tabular}[c]{@@{}c@@{}}Unambiguous\\ Non-malleable\\ Unique prefixes\end{tabular} & N/A                                                                                                                                              & N/A                                                                            \\ \hline
\end{tabular}
}%
\end{table}


\noindent\textbf{Trusted Computing Base (TCB).}
Our TCB comprises the \agda toolchain (v2.6.2.2), which includes its native
type-checker, compiler, and standard library (v1.7.1).
% In particular, 
Our use of \agda's standard library includes the module
\texttt{\small Data.Trie} (for the \emph{String canonicalizer}), which requires the
\texttt{\small -{}-sized-types} language feature, and the module \texttt{\small IO}, which
requires the \texttt{\small -{}-guardedness} language feature.
The use of these two features together \emph{in the declaration of a coinductive
  type} causes logical inconsistency~\cite{AgdaIssue-1209}.
In our code base,  the only module which enables both features is the
\emph{Driver}. It, 
%(because it needs to invoke the \emph{String canonicalizer} and perform IO), 
% which, 
however, does not define any coinductive types.
Finally, \armor uses Agda's FFI for two Haskell packages: \texttt{time} and
\texttt{bytestring}.

\textbf{Termination.}
By default, \agda employs a syntactic termination checker that ensures 
recursive functions respect a certain well-founded ordering~\cite{AgdaDocs}.
This syntactic termination checker can be disabled through the explicit use of
certain pragmas, or replaced with a \emph{type-based} termination checker
through the use of sized types.
\armor does not use any pragmas that disable termination checking, so its
termination is guaranteed by \agda's syntactic checker everywhere except the
\emph{String canonicalizer} and its co-dependencies, whose termination guarantee
additionally rests on the correctness of \agda's type-based checker.

\textbf{Other Assumptions.}
We also make the following assumptions: (1) the \ghc \haskell compiler correctly generates
the executable; (2) the verifier's %trust anchor (\ie, the
trusted root CA store is up-to-date and does not contain any malicious
certificates; (3) the current system time is accurate.

\subsection{Preliminaries on Agda}
\label{sec:s4-preliminaries-agda}
\agda is a \textit{dependently-typed} functional programming
language, meaning that types may involve terms (that is, program-level
expressions).
This capability helps express rich properties of programs \emph{in the types of
  those programs}, and checking that programs satisfy those properties is
reduced to typechecking.
This paradigm, known as the \emph{Curry-Howard}
correspondence~\cite{SU06_Lectures-on-the-Curry-Howard-Isomorphism}, means we
can view \agda's types as \emph{propositions} and its programs as \emph{proofs}
of the propositions expressed by their types.
% This makes \agda a powerful tool for both expressing programs and their
% correctness, as it unifies the language of programs and proofs. 

Consider the example shown in Figure~\ref{fig:agda-ex} of nonnegative integers
strictly less than some upper bound, provided as part of the \agda standard
library as |Fin|.
\begin{figure}[h]
  \begin{code}
data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (1 + n)
  fsuc  : {n : Nat} -> (i : Fin n) -> Fin (1 + n)

toNat : forall {n} -> Fin n -> Nat
toNat fzero = 0
toNat (fsuc i) = 1 + (toNat i)  
  \end{code}
  \caption{Length-indexed lists in \agda}
  \label{fig:agda-ex}
\end{figure}
|Fin| defines an \emph{inductive family} of types, where the family is indexed
by a non-negative integer.
In other words, for every nonnegative integer |n : Nat|, |Fin n| is a unique
type whose inhabitants correspond to the nonnegative integers strictly less than |n|.

We now explain the declaration of |Fin|.
\begin{itemize}
\item The |data| keyword introduces a new inductive type or
  type family, in this case |Fin|.
\item |Set| is the type of (small) types (we omit the details of \agda's
  universe hierarchy). 
  
\item |Fin| has two constructors, both of which have dual readings as ``mere
  data'' and as axiomatizations of the \emph{``is strictly less than''}
  relation.
  As mere data, |fzero| corresponds to the integer 0; as an axiom, it states
  that 0 is strictly less than the successor |1 + n| of any nonnegative |n|.
  Similarly, as mere data |fsuc| is a primitive successor operation
  (like the Peano numbers), and as an inference rule, it states that if |i| is
  strictly less than |n|, then its successor is strictly less than |1 + n|.
 
\item Curly braces indicate function arguments that need not be passed
  explicitly.
  For example, if |i| has type |Fin 5|, then  Agda can
  determine |fsuc i| has type |Fin 6|.
\end{itemize}

Since |Fin| is inductive, we can define functions over it by \emph{pattern
  matching} and \emph{recursion}.
This is shown with function |toNat|, which we can think of as extracting the ``mere data''
contained in an expression of type |Fin n|.
\begin{itemize}
\item In the type signature, we use the syntactic sugar |forall| to
  omit the type of the parameter |n|, as Agda can infer this from the occurrence
  of |n| in the rest of the type.
  
\item The definition of |toNat| is given with two equations, one each for the
  two constructors of |Fin|.
  \begin{itemize}
  \item In the first equation, we set |fzero| to 0.
    
  \item In the second equation, our argument is of the form |fsuc i|.
    We make a recursive call |toNat i| and increment the result by |1|.
    \agda's termination checker accepts this, as |i| is structurally smaller
    than |fsuc i|.
  \end{itemize}
\end{itemize}

\subsection{Input Strings and Base64 Decoding}
|Fin| plays a central role as the type of the language alphabet for our
\xsno DER and \xfon parsers, as well as the input and output types for Base64
decoding.
In general, parser inputs have types of the form |List A|, where |A| is the type
of language alphabet; %
%for our PEM parser this is |Char|, Agda's character type,
%and
for our \xsno DER and \xfon parsers, this is |UInt8|, an alias for |Fin 256|.
The ultimate result of our PEM parser is a string of sextets, \ie, a value of
type |List UInt6|, where |UInt6| is an alias for |Fin 64|.

The hand-off between the result of PEM parsing and the input to \xfon parsing
(Figure~\ref{armor}, \circled{C} -- \circled{D}) is managed by the 
Base64 decoder, whose formal correctness properties are established with respect
to a specificational encoder. %
%(used only for specificational purposes).
Specifically, we prove: (1) that the encoder always produces a result accepted by
the decoder; and (2) the encoder and decoder pair forms an
isomorphism between octet strings and valid sextet strings for encoding them.
%For a more detailed summary, see the full version of the paper~\cite{armor-full-version}.
This is summarized below in Figure~\ref{fig:s4-base64} (definitions omitted), which
we now explain.

\begin{figure}[h]
  \begin{code}
Valid64Encoding : List UInt6 -> Set

encode : List UInt8 -> List UInt6
decode : (bs : List UInt6) -> Valid64Encoding bs -> List UInt8

encodeValid : forall bs -> Valid64Encoding (encode bs)

encodeDecode :  forall bs -> decode (encode bs) (encodeValid bs) == bs
decodeEncode :  forall bs -> (v : Valid64Encoding bs)
                -> encode (decode bs v) == bs
  \end{code}
  \caption{Base64 encoding and decoding (types only)}
  \label{fig:s4-base64}
\end{figure}

\begin{itemize}
\item |Valid64Encoding| is a predicate for sextet strings that expresses what it
  means for them to be valid encodings of an octet string.
  Recall that Base64 decoding proceeds by mapping each group of four sextets to
  three octets (24 bits in total).
  \begin{itemize}
  \item If a single sextet remains after this grouping, then the sextet string
    is invalid (6 bits is not enough to encode an 8 bit value).
    
  \item If two sextets remain, then they encode a single octet iff the last 4
    bits of the second sextet are set to 0.
    
  \item If three sextets remains, then they encode two octets iff the last 2 bits
    of the third sextet are set to 0.
  \end{itemize}
  
\item Next in the figure are the encoder, |encode|, and decoder, |decode|.
  While the domain of the encoder is all octet strings, for the decoder the
  domain is restricted to only those sextet strings for which the predicate
  |Valid64Encoding| holds.

  
\item Lemma |encodeValid| is a proof that the specificational Base64encoder
  always produces a valid Base64 encoding.

  
\item Finally, our main correctness result for the Base64 module is given by the
  proofs |encodeDecode| and |decodeEncode|, which together state that the
  encoder and decoder form an isomorphism (|==| is the symbol for propositional
  equality).
  In the first direction (|encodeDecode|), we pass to the decoder the result of
  encoding octet string |bs| together with a proof that this encoding is valid,
  and the result we get is the very same octet string |bs|.
  In the second direction, we assume that the given sextet string |bs| is
  already a valid encoding, and we obtain that the result of first decoding and
  then re-encoding |bs| is |bs| itself.
\end{itemize}

\subsection{Verification of Parsers} We conceptually separate each parser verification task into \emph{language
specification}, \emph{language security verification}, and \emph{parser correctness verification}.

\subsubsection{Language specification} \label{sec:s4-lang-spec}
We provide parser-independent formalizations of the PEM, Base64, X.690
DER, and \xfon formats, greatly reducing the complexity of the specification
and increasing trust that they faithfully capture the natural language
description.
Much current research~\cite{ni2023asn1, ramananandro2019everparse}
on applying formal methods to parsing uses serializers to specify their
correctness properties.
Formal proofs of correctness (in any context) are only ever as good as the
specification of those correctness properties, and this earlier research swells
the trusted computing base by introducing implementation details for serialization.
To avoid this issue, we use \emph{relational} specifications of
languages. 
This has two other advantages: (1) it allows for a clear distinction between correctness
properties of the \emph{language} and \emph{parser}; and (2)
it brings the formal language specification into closer correspondence with the
natural language description.
This second point also means the formal specification can serve as a
machine-checked, rigorous alternative for the developers seeking to
understand the relevant specifications. 

The relational specifications we give are of the following form.
For a given language \(G\) with alphabet \(A\), we define a family of types
|G : List A -> Set|, where the family |G| is indexed by strings |xs : List A|
over the alphabet.
Such a family serves dual roles: a value of type |G xs| is both
proof that \(\mathit{xs}\) is in the language \(G\), and the internal
representation of the value decoded from \(\mathit{xs}\).

\begin{figure}[h]
  \begin{code}
MinRep : UInt8 -> List UInt8 -> Set
MinRep hd [] = Top
MinRep hd (b2 :: tl) =
  (hd > 0 Lor (hd == 0 Land b2 >= 128))
  Land (hd < 255 Lor (hd == 255 Land b2 <=127))
    
record IntegerValue (@0 bs : List UInt8) : Set where
  constructor mkIntVal
  field
    @0 hd : UInt8
    @0 tl : List UInt8
    @0 minRep : MinRep hd tl
    val : IntZ
    @0 valeq : val == Base256.twosComp bs
    @0 bseq : bs == hd :: tl
  \end{code}
  \caption{Specification of integer values}
  \label{fig:s4-integervalue}
\end{figure}

We illustrate our approach with a concrete example: our specification of X.690
DER integer values, shown in Figure~\ref{fig:s4-integervalue}.
This specification takes the form of an Agda record that is parameterized by a
bytestring |bs|.
\begin{itemize}
\item \textbf{Erasure annotations.} The annotation |@0| marks the accompanying
  identifier as \emph{erased at runtime}.
  In |IntegerValue|, only |val|, which is the integer encoded by |bs|, is
  present at runtime; the remaining fields and parameter |bs| are erased by
  Agda's GHC backend.
  Runtime erasure annotations not only improve performance,
  but also document the components that serve only specificational purposes for
  programmers using \armor as a reference.

\item \textbf{Minimum representation.} \xsno DER requires the two's
  complement encoding of an integer value consists of the minimum number of
  octets.
  We \emph{express} this property with |MinRep|, which defines a relation between the
  first byte of the encoding and the remaining bytes.
  We \emph{enforce} the property with field |minRep| of |IntegerValue|: in order
  to construct an expression of type |IntegerValue bs|, one must prove that
  |MinRep| holds for the head and tail of |bs|.
  
  The definition of |MinRep| is by pattern matching on |tl|.
  \begin{enumerate}
  \item If |tl| is empty, we return the trivially true proposition |Top|,
    because a single byte is always minimal.
    
  \item Otherwise, if the first byte is |0|, the second byte must be no less than
    |128|; and if the first byte is |255|, then the second byte must be no
    greater than |127|.
  \end{enumerate}
  
\item \textbf{Nonempty encoding.} Fields |hd|, |tl|, and |bseq| together ensure
  the encoding of an integer value ``consists of one or more octets.''~\cite{rec2002x}
  Specifically, |bseq| ensures that |bs| is of the form |hd :: tl|, where |hd|
  is the first content octet and |tl| contains the remaining octets (if any).
  

\item \textbf{Linking the value and its encoding.}
  Field |valeq| enforces that |val| be populated with a value equal to the
  result of decoding |bs| as a two's complement binary value (|Base256.twosComp|
  is the decoding operation).
\end{itemize}


\subsubsection{Language security verification}
\label{sec:s4-lang-security}

A major advantage of our approach to specifying X.509 is that it facilitates
proving properties \emph{about the grammar} without having to reason about
parser implementation details.
We have proven: \emph{unambiguousness} for the supported subsets of formats PEM, \xsno \der, and
\xfon; \emph{non-malleability} for the supported subsets of formats \xsno \der
and \xfon; and \emph{unique prefixes} for all \tlv structures.

\textbf{Unambiguous.}
We formally define unambiguousness of a language |G| in Agda as follows.
\begin{code}
Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
\end{code}
Read this as saying for every string |xs|, any two inhabitants
of the internal representation of the value encoded by |xs| in |G| are equal.
In the context of \xfon, format ambiguity could result in interoperability
issues between standards-compliant producers and consumers (\eg, rejection
because the decoded certificate does not match the encoded certificate).

\textit{Challenges.}
One challenging aspect in proving unambiguousness for X.690 DER its support for
sequences with \emph{optional} and \emph{default} fields, that is, fields that
might not be present in the sequence.
We are threatened with ambiguity if it is possible to mistake an optional field
whose encoding is present for another optional field whose encoding is absent.
To avoid this scenario, the \xsno format stipulates that every field of any
``block'' of optional or default fields must be given a tag distinct from every
other such field.
Our proof of unambiguousness for \xfon relies heavily on lemmas proving the
\xfon format obeys this stipulation.

\textbf{Non-malleable.}
Informally, in the context of \xfon non-malleability means that two distinct
bytestrings cannot be encodings for the same certificate.
Compared to unambiguousness, non-malleability requires more machinery to
express, so we begin by discussing the challenges motivating this machinery.
Since the bytestring encodings are part of \emph{the very types of internal
representations}, e.g., |IntegerValue xs|, it is impossible to express equality
between internal representations |a1 : G xs1| and |a2 : G xs2| without
\emph{already assuming |xs1| is equal to |xs2|}.
Thus, to make non-malleability non-trivial, we must express what is the
``raw'' internal datatype corresponding to |G|, discarding the specificational
components.
We express this with |Raw|, given below.
\begin{code}
record Raw (G : List A -> Set) : Set where
  field
    D : Set
    to : {@0 xs : List A} -> G xs -> D
\end{code}

An inhabitant of |Raw G| consists of a type |D| (the ``mere data'' of |G|)
together with a function |to| that extracts this data from any inhabitant of |G xs|.
Consider the case for |IntegerValue| below.
\begin{code}
  RawIntegerValue : Raw IntegerValue
  Raw.D RawIntegerValue = IntZ
  Raw.to RawIntegerValue = IntegerValue.val
\end{code}
\noindent This says that the raw representation for \xsno DER integer values is
|IntZ|, and the extraction function is just the field accessor |IntegerValue.val|.

Once we have defined an instance of |Raw G|, we express non-malleability of |G|
with respect to that raw representation with the following property: give two
``proof-carrying'' internal representations |g1 : G xs1| and |g2 : G xs2|, if
the mere data of |g1| and |g2| are equal, then not only are strings
|xs1| and |xs2| equal, but also |g1| and |g2|.
In Agda, we write:
\begin{code}
NonMalleable : {G : List A -> Set} -> Raw G -> Set
NonMalleable{G} R =
  forall {@0 xs1 xs2} -> (g1 : G xs1) (g2 : G xs2)
  -> Raw.to R g1 == Raw.to R g2 -> (xs1 , g1) ==  (xs2 , g2)  
\end{code}
Proving |NonMalleable RawIntegerValue| requires proving |Base256.twosComp| is
injective. 

\textbf{Unique prefixes}
The final language property we discuss, dubbed \emph{``unique prefixes,''}
expresses that a language permits parsers no degrees of freedom over which
prefix of the input it consumes.
Striving for \emph{parser independence}, we formulate
this property as follows: for any two prefixes of an input string, if both
prefixes are in the language |G|, then they are equal.
In Agda, we express this as |UniquePrefixes| below.
\begin{code}
UniquePrefixes G = forall {xs1 ys1 xs2 ys2}
   -> xs1 ++ ys1 == xs2 ++ ys2 -> G xs1 -> G xs2 -> xs1 == xs2
\end{code}
Given that \xfon uses \tlv encoding, it is
unsurprising that we are able to prove |UniquePrefixes| holds.
However, we call explicit attention to this property for two
reasons: (1) it is an essential lemma in our proof of \emph{strong completeness} of
our \xfon parser (see Section~\ref{sec:s4-parser-sound-complete-strong}); and (2)
this property \emph{does not hold} for the PEM format due to leniency in
end-of-line encoding, so to show strong completeness for PEM parsers we need an
additional property, \emph{maximality}.

\subsubsection{Parser correctness}
We now describe our approach to verifying parser soundness and completeness.
For a language \(G\), parser \emph{soundness} means every
prefix it consumes is in the language, and \emph{completeness} means if a
string is in the language, it consumes a prefix of it (we later show a
strengthening of this notion of completeness).
Our approach to verifying these is to make our parsers
\emph{correct-by-construction}, meaning that parsers do not merely indicate
success or failure with \eg an integer code, but return \emph{proofs}.
Precisely, our parsers are correct-by-construction by being proofs that
membership of an input's prefix in \(G\) is decidable: parsers return either a
proof that some prefix of its input is in the language, or a proof that
\emph{no} prefix is.

\noindent\textbf{Correct-by-construction parsers:}
\label{sec:s4-parsers-cbc}
Our first step is to formally define success.
In first-order logic, we would express the condition for the parser's success on a prefix of
|xs| as \(\exists \mathit{ys}\, \mathit{zs}, \mathit{xs} = \mathit{ys} +\!\!\!+
\mathit{zs} \land |G ys|\).
That is to say, on success the parser consumes some prefix of the input string
that is in the language |G|.
In Agda, we express this as the record |Success|, shown below.
\begin{figure}[h]
  \centering
  \begin{code}
    record Success 
      (G : List UInt8 -> Set) (@0 xs : List UInt8) : Set where
      field
        @0 prefix : List UInt8
        suffix : List UInt8
        @0 pseq : prefix ++ suffix == xs
        value : G prefix
  \end{code}
  \caption{Success conditions for parsing}
  \label{fig:parser-success}
\end{figure}
In the definition, parameters |G| and |xs| are the language denoted by
a production rule and an input string, respectively.
The fields of the record are: |prefix|, the consumed prefix of the input (erased
at runtime); |suffix|, the remaining suffix of the input from which we parse
subsequent productions; |pseq|, which relates |prefix| and |suffix| to the input
string |xs| (also runtime erased); and |value|, which serves dual roles as both
the internal data representation of the value encoded by |prefix| \textbf{and}
a proof that |prefix| is in the language |G|.  
As a consequence, \emph{soundness will be immediate}.

Failure is the negation of the success condition, |not Success G xs|, meaning
\emph{no} prefix of the input |xs| is in the language of |G|.
To have the parser return |Success G xs| on success and |not Success G xs| on
failure, we use the \agda standard library datatype |Dec|, shown below.
\begin{code}
data Dec (Q : Set) : Set where
  yes : Q -> Dec Q
  no  : not Q -> Dec Q
\end{code}
Reading |Dec| as programmers, |Dec Q| is a tagged union type which can be
populated using either values of type |Q| or type |not Q|; as mathematicians, we
read it as the type of proofs that |Q| is \emph{decidable}.
Expressed as a formula of FOL, |Dec Q| is simply \(Q \lor \neg Q\); however,
note that constructive logic (upon which \agda is based) does not admit LEM, so
this disjunction must be proven on a case-by-case basis for each |Q| (there
are some undecidable propositions). 

We are now able to complete the definition of the type of parsers, shown in
Figure~\ref{fig:parser-def}.
\begin{figure}[h]
  \begin{code}
Parser : (List A -> Set) -> Set
Parser G = forall xs -> Dec (Success G xs)

MaximalSuccess :  forall (G : List A -> Set) xs
                  -> Dec (Success G xs) -> Set
MaximalSuccess G xs (no _) = Top
MaximalSuccess G xs (yes s) = forall pre suf -> pre ++ suf == xs
  -> G pre -> length pre <= length (Success.prefix s)

record MaximalParser (G : List A -> Set) : Set where
  field
    p : Parser G
    max : forall xs -> MaximalSuccess (p xs)
  \end{code}
  \caption{Definition of |Parser| and |MaximalParser|}
  \label{fig:parser-def}
\end{figure}%
|Parser| is a family of types, where for each language |G|, the type
|Parser G| is the proposition that, for all bytestrings |xs|, it is decidable
whether some prefix of |xs| is in |G|.

\textit{Challenges.}
The guarantee that, on failure, the parser returns |not Success G xs| is very
strong, as it asserts a property concerning \emph{all possible prefixes} of the
input.
This strength is double-edged: while having this guarantee makes proving
completeness straightforward, \emph{proving} it means ruling out all possible
ways in which the input could be parsed.
In some cases, we implemented parsers to facilitate
the proofs concerning the failure case, at a cost to performance.
The clearest example of such a trade-off is in our parsers for \xsno
\texttt{Choice} values, implemented using back-tracking.

\textbf{Maximal parsers:} The PEM format does not enjoy the
\emph{unique prefixes} property.
To facilitate our implementation of correct-by-construction PEM parsers and
prove a stronger completeness result, we have augmented the specifications of these parsers
to guarantee they consume \emph{the largest prefix of the input compliant with
  the format.}
The formalization of this in Agda is shown in
Figure~\ref{fig:parser-def}.
Definition |MaximalSuccess| expresses that if parsing |xs| was successful (|yes
s|), then any other prefix |pre| of |xs| in |G| is no greater than
that consumed by the parser.
In the record |MaximalParser|, we couple together a parser |p| together with a
proof |max| that, for \emph{every} input string |xs|, if |p| is successful
parsing |xs| then that success is maximal.

\noindent\textbf{Correctness properties:}
\label{sec:s4-parser-sound-complete-strong}
We now show our formal definitions and proofs of soundness and completeness for
parsing, beginning with soundness.
\begin{figure}
  \begin{code}
Sound : (G : List A -> Set) -> Parser G -> Set
Sound G p =
  forall xs -> (w : IsYes (p xs)) -> G (Success.prefix (toWitness w))    

Complete : (G : List A -> Set) -> Parser G -> Set
Complete G p = forall xs -> G xs -> IsYes (p xs)

soundness : forall {G} -> (p : Parser G) -> Sound G p
soundness p xs w = Success.value (toWitness w)

trivSuccess : forall {G} {xs} -> G xs -> Success G xs

completeness : forall {G} -> (p : Parser G) -> Complete G p
completeness p xs inG = fromWitness (p xs) (trivSuccess inG)
  \end{code}
  \caption{Parser soundness and completeness}
  \label{fig:s4-parser-soundness-completeness}
\end{figure}%

\textbf{Soundness.}
The \agda definition and proof of soundness for all of our parsers is
shown in Figure~\ref{fig:s4-parser-soundness-completeness}.
Beginning with |Sound|, the predicate expressing that parser |p| is sound with
respect to language |G|, the predicate |IsYes| (definition omitted) expresses
the property that a given decision (in this case, one of type |Dec (Success G
xs)|) is affirmative (i.e., constructed using |yes|).
The function |toWitness : forall {Q} {d : Dec Q} -> IsYes d -> Q| takes a
decision |d| for proposition |Q| and proof that it is affirmative, and produces
the underlying proof of |Q|.
Thus, we read the definition of |Sound G p| as: ``for all input strings |xs|, if
parser |p| accepts |xs|, the prefix it consumes is in |G|.''

The proof |soundness| states that \emph{all parsers are sound}.
As our parsers are correct-by-construction, the definition is straightforward:
we use |toWitness| to extract the proof of parser success, i.e., an expression of type
|Success G xs|, then the field accessor |Success.value| obtains the
desired proof that the consumed prefix is in |G|.

\textbf{Completeness.}
% Recall that the definition of parser completeness with respect to a language |G|
% means that if an input string |xs| is in |G|, the parser accepts \emph{some
%   prefix of |xs|}.
% Of course, this property in isolation does not rule out certain bad behavior
% that threatens security; specifically, it does not constrain the parser's
% freedom over (1) which prefix of the input is consumed, and (2) how the internal
% datastructure is constructed.
% However, and as we have discussed in Section~\ref{sec:s4-lang-spec}, these
% should be thought of as properties of the \emph{language}, and \emph{not} its
% parsers.
% To emphasize this, after discussing the completeness proof we will show how,
% using language properties, it can be strengthed to address the aforementioned
% security concerns.
%
Figure~\ref{fig:s4-parser-soundness-completeness} also shows our definition and
proof of \emph{completeness} in \agda.
The definition of |Complete| directly translates our notion of completeness: for
every input string |xs|, if |xs| is in |G|, then parser |p| accepts some prefix
of |xs|.
For the proof, a straightforward lemma |trivSuccess| (definition
omitted) states any proof that |xs| is in |G| can be turned into a proof
that some prefix of |xs| (namely, |xs| itself) is in |G|.
With this lemma, the proof of |completeness| uses the function |fromWitness : {Q :
  Set} -> (d : Dec Q) -> Q -> IsYes d|, which intuitively states that if a
proposition |Q| is true, then any decision for |Q| must be in the affirmative.


\textbf{Strong completeness.}
In isolation, completeness does not rule out all bad behavior that threatens
security.
Specifically, it does not constrain the parser's freedom over (1) which prefix
it consumes and (2) how the internal datastructure is constructed.
As discussed in Section~\ref{sec:s4-lang-spec}, these should be thought of as
\emph{language} properties.
To rule out both bad behaviors, it suffices that |G| satisfies the
properties |Unambiguousness| and |UniquePrefixes|.

\begin{figure}
  \begin{code}
StronglyComplete : (G : @0 List A -> Set) -> Parser G -> Set
StronglyComplete G p = forall xs -> (inG : G xs)
  -> exists  (w : IsYes (p xs)) (let s = toWitness w in
               (xs , inG) == (Success.prefix x , Success.value s))

strongCompleteness
  : forall {G} -> Unambiguous G -> UniquePrefixes G
    -> (p : Parser G) -> StronglyComplete G p

strongCompletenessMax : forall {G} -> Unambiguous G
  -> (m : MaximalParser G)
  -> StronglyComplete G (MaximalParser.p m)
  \end{code}
  \caption{Strong completeness (types only)}
  \label{fig:s4-parser-stcompleteness}
\end{figure}

Figure~\ref{fig:s4-parser-stcompleteness} shows the types used in our proof of
our strong completeness (see the full paper for more).
|StronglyComplete G p| says that, if we have a proof |inG| that
|xs| is in |G|, then not only does there exist a witness |w| that the parser
accepts some prefix of |xs|, but this prefix is |xs| and the proof it returns is
|inG|.
Recall that the assumption |inG| and the |value| field of the |Success| record
serve dual roles: they are not only proofs that a string is in a language, but
also the internal data representation of the value encoded by |xs|.
So, saying they are equal means the internal representations are equal.

% The proof, |strongCompleteness|, shows that to prove |StronglyComplete|, it
% suffices that the language |G| satisfies |Unambiguous| and |UniquePrefixes|.
% In the definition, we exhibit witness |w| using the previous proof
% |completeness|, and in the helper proof |strong| we use the assumptions |ns :
% UniquePrefixes G| and |ua : Unambiguous G| to prove that |xs| and |inG| are equal
% to the |prefix| consumed and |value| returned by |p xs|.
% Note that in the type signature of |strong|, |dashcomma| is a \emph{function}
% (with precedence lower than ordinary function application) that builds a tuple,
% used when the type of the second component of the tuple uniquely determines the
% value of the first component.

\emph{Strong completeness from maximality.}
For PEM, even though the format lacks the \emph{unique prefixes} property we can
still prove strong completeness by leveraging the fact that our parsers are
guaranteed to be \emph{maximal.}
Intuitively, this is because if |xs| is in |G|, then the largest possible prefix
of |xs| in |G| is |xs| itself.
We show the formal statement of the theorem in
Figure~\ref{fig:s4-parser-soundness-completeness} (proof omitted).

% 
% 
% 

\subsection{Verification of Chain Builder}
The section presents the \emph{Chain builder}, for which we have proven
soundness and completeness with respect to a partial specification.
Adhering to our discipline of providing high-level, relational specifications,
we dedicate the bulk of this section to describing the specification used,
presenting at the end the type of our sound-by-construction chain builder and
its proof of completeness.

\subsubsection{|Chain| Specification}
Our operative definition of correctness for the |Chain Builder| module is as
follows (cf.\, RFC 5820, Section 6.1).
Given a list of certificates \(c_1 \ldots c_n\) where \(n \geq 2\), this list forms a chain when:
\begin{itemize}
\item \(c_1\) is the certificate to be validated;
  
\item \(c_n\) is a certificate in the trusted root store;
  
\item for all \(i \in \{1 \ldots n-1\}\), the issuer field of \(c_i\) matches
  the subject field of \(c_{i+1}\); and
  
\item if \(c_1\) is not a self-signed certificate that is present in the trusted root
  store, then for all \(i,j \in {1 \ldots n}\), if \(c_i = c_j\) then \(i = j\).
\end{itemize}
\noindent Note that it is the \emph{Semantic validator} that checks whether the
certificate validity period contains the current time, that
cryptographic signature verification is outsourced to external libraries (see
Section~\ref{sec:s6-empirical-eval}), and that we currently perform no policy
mapping.
Thus, our specification is \emph{partial} in the sense that we do not claim it
captures the full set of desired correctness properties of chain building.

\begin{figure}
  \begin{code}
_IsIssuerFor_ : forall {@0 xs1 xs2} -> Cert xs1 -> Cert xs2 -> Set
issuer IsIssuerFor issuee =
  NameMatch (Cert.getIssuer issuee) (Cert.getSubject issuer)    

_IsIssuerFor_In_ :  forall {@0 xs1 xs2} -> Cert xs1 -> Cert xs2
                    -> (certs : List (exists Cert)) -> Set
issuer IsIssuerFor issuee In certs =
  issuer IsIssuerFor issue Land (dashcomma issuer) `elem` certs

removeCertFromCerts :  forall {@0 xs} -> Cert xs 
                       -> List (exists Cert) -> List (exists Cert)
removeCertFromCerts cert certs = filter (\ c -> c /=? (dashcomma cert)) certs
  
data Chain (trust candidates : List (exists Cert))
  : forall {@0 xs} -> Cert xs -> Set where
  root :  forall {@0 xs1 xs2} {c1 : Cert xs1} (c2 : Cert xs2)
          -> c2 IsIssuerFor c1 In trust
          -> Chain trustedRoot candidates c1
  link :  forall {@0 xs1 xs2} (issuer : Cert xs1) {c : Cert xs2}
          -> issuer IsIssuerFor c In candidates
          -> Chain  (removeCertFromCerts issuer trust)
                    (removeCertFromCerts issuer candidates)
                    issuer
          -> Chain trust candidates c
  \end{code}
  \caption{Definition of a sound |Chain|}
  \label{fig:s4-chain}
\end{figure}

Figure~\ref{fig:s4-chain} lists our formalization of the specification for a
sound chain, defined as |Chain|, which we now describe.
\begin{itemize}
\item |_IsIssuerFor_| is a binary relation on certificates expressing that the
  subject field of the first certificate matches the subject of the second.
  In \agda, one can define mixfix operators and relations by using underscores
  in the identifier to mark the locations of arguments.
  This allows us to write |issuer IsIssuerFor issuee| as syntactic sugar for
  |_IsIssuerFor_ issuee issuer|.
  
\item The three-place relation |_IsIssuerFor_In_| augments the previous relation
  by allowing us to track \emph{where} the issuer came from using the membership
  relation \(\_\in\_\).
  \begin{itemize}
  \item In the signature of |_IsIssuerFor_In_|, the type of the third argument,
    |List (exists Cert)|, is the type of \emph{lists of tuples} of byte strings
    |xs : List UInt8| together with proofs |Cert xs| that the byte string
    encodes a certificate.
    
  \item In the definition of |_IsIssuerFor_In_|, since |certs| is a list of
    tuples, to express that |issuer| is present in certs we must tuple it
    together with its octet string encoding.
    This is neatly achieved with |(dashcomma issuer)|, which forms a tuple where only
    the second component need by passed explicitly, leaving \agda to infer the
    value of the first component.
  \end{itemize}
    
\item Function |removeCertFromCerts| takes a certificate |cert| and list of
  tupled certificates |certs| and uses the \agda standard library function
  |filter| to remove all certificates from |certs| that are equal to |cert|.
  
\item Finally, we come to the definition of |Chain|, an inductive family of
  types indexed by: |trust : List (exists Cert)|, the certificates in the
  trusted root store; |candidates : List (exists Cert)|, the intermediate
  CA certificates provided by the end entity to facilitate chain building; and
  the certificate we are attempting to authenticate.
  |Chain| has two constructors, axiomatizing the two ways we can extend trust to
  the end entity.
  \begin{itemize}
  \item Constructor |root| expresses that we can trust certificate |c1| when we
    can find a certificate |c2| in the trusted root store representing an issuer
    for |c1|.
    
  \item Constructor |link| expresses that we can trust certificate |c| if we can
    find an issuer's certificate |issuer| in |candidates|, and furthermore that
    we (inductively) trust |issuer| through the construction of a |Chain|.
    To avoid duplicate certificates in the chain (and ensure termination by
    ruling out cycles), the chain of trust extended to |issuer| must use a
    trusted root store and candidate certificate list from which |issuer| has
    been removed; we express this using function |removeCertFromCerts|.
  \end{itemize}
\end{itemize}

\subsubsection{Chain Uniqueness}

As we did with our language formalizations, by having an implementation-independent,
relational specification |Chain| we can prove that certain properties hold of
\emph{all} chains constructed by our chain builder, \emph{without} reasoning
about its implementation details.
Given the limited scope of our specification of correctness for chains, we are
primarily interested in verifying the \emph{uniqueness} property: ``A
certificate MUST NOT appear more than once in a propsective certification
path.''
We are able to verify this property under the assumption that the end entity
certificate is neither in the candidate list (ensured by a preprocessing step
before the \emph{Chain Builder} is invoked) nor in the trusted root store.
\begin{figure}
\begin{code}
toList :  forall {trust candidates} {@0 xs} (c : Cert xs)
          -> Chain trust candidates c -> List (exists Cert)
toList c (root issuer _) = (dashcomma c) :: [ issuer ]
toList c (link issuer isIn chain) = (dashcomma c) ::toList issuer chain

ChainUnique : forall {trust candidates} {@0 xs} {c : Cert xs}
              -> Chain trust candidates c -> Set
ChainUnique c = List.Unique (toList c)

chainUnique
  :  forall trust candidates {@0 xs} {issuee : Cert xs}
     -> (dashcomma issuee) `notElem` candidates -> (dashcomma issuee) `notElem` trust
     -> (c : Chain trust candidates issuee) -> ChainUnique c
\end{code}
  \caption{Chain Uniqueness}
  \label{fig:s4-chain-unique}
\end{figure}

The specification and proof of chain uniqueness are listed in
Figure~\ref{fig:s4-chain-unique}, which we now describe.
\begin{itemize}
\item Function |toList| extracts the list of certificates from the chain,
  including the issuer found in the trusted root.
  
\item Predicate |ChainUnique| expresses the uniqueness of each certificate in a
  chain by first using |toList| to extract the underlying list of certificates,
  then uses the predicate |List.Unique| from \agda{}'s standard library.

  
\item Finally, the proof |chainUnique| (definition omitted) establishes that the
  predicate |ChainUnique| holds for every chain |c : Chain trust candidates
  issuee|, provided that |issuee| is not present in either the candidate
  certificate list or the trusted root.
\end{itemize}

\subsubsection{Sound and Complete Chain Building}
\label{sec:s4-sound-complete-chain-building}
\begin{figure}
\begin{code}
buildChains
  :  forall trust candidates {@0 bs} (issuee : Cert bs)
     -> List (Chain trust candidates issuee)

ChainEq :  forall {trust candidates} {@0 bs} {issuee : Cert bs}
           -> (c1 c2 : Chain trust candidates issuee) -> Set
ChainEq c1 c2 = toList c1 == toList c2

buildChainsComplete
  :  forall trust candidates {@0 bs} (issuee : Cert bs)
     -> (c : Chain trust candidates issuee)
     -> Any (ChainEq c) (buildChains trust candidates issuee)
\end{code}
  \caption{Verified chain builder}
  \label{fig:s4-chain-builder}
\end{figure}

We now present our chain builder, verified sound and complete with
respect to the specification |Chain|, in Figure~\ref{fig:s4-chain-builder}.
First, observe that by its type |buildChains| (definition omitted) is
\emph{sound by construction}: every chain that it returns has type |Chain trust
candidates issuee|.
Of course, the \emph{trivial} chain builder (one that always returns the empty
list) is also sound by construction, and so the other property we are interested
in is \emph{completeness:} if there \emph{exists} a chain of trust extending to
the |issuee| from the |trust| store using intermediate certificates pulled from
|candidates|, then our chain builder enumerates it.
This is formalized in the remainder of the figure, which we now describe.

\begin{itemize}
\item Relation |ChainEq| expresses that the underlying certificate lists of two
  chains |c1 c2 : Chain trust candidates issuee| are equal.
  Observe that were we to define |ChainEq c1 c2| as |c1 == c2|, this would be
  much stronger than is required: a value of type |Chain trust candidates
  issuee| carries with it not only the underlying certificate list, but also
  proofs relating each certificate with the next and with |trust| and
  |candidates|.
  It is not necessary that these proof terms are also equal, so |ChainEq|
  discards these using |toList|.
  
\item In the type signature of |buildChainsComplete|, we use |Any| from the \agda standard
  library |Any|.
  Given any type |T|, a predicate |Q : T -> Set| and a list |xs : List T|, |Any
  Q xs| is the proposition that there exists \emph{some} element of xs for which
  |Q| holds.
  
\item Putting these together, we can read the type signature of
  |buildChainsComplete| as follows: for every chain |c : Chain trust candidates
  issuee|, there exists a chain in the result of |buildChains trust candidates
  issuee| which is equal to |c| modulo some proof terms (i.e., the proofs that
  issuers are present in either |candidates| or |trust| and the proofs that for
  each adjacent pair of certificates, the issuer of the first matches the
  subject of the second).
\end{itemize}

\subsection{Verification of Semantic Validator}
We now describe our verification approach to the task of \emph{semantic
  validation}.
The checks performed by the \emph{Semantic validator} are separated into two
categories: those that apply to a single certificate, and those that apply to a
candidate certificate chain.
For each property to validate, we formulate in \agda a predicate expressing
satisfaction of the property by a given certificate or chain, then prove that
these predicates are decidable (|Dec|, Section~\ref{sec:s4-parsers-cbc}).
In what follows, we illustrate with two relatively simple concrete examples: one
predicate for a single certificate and one for a certificate chain.

Before we illustrate with examples, we stress that the purpose of this setup is
\emph{not} merely to give decidability results for the semantic checks of the \xfon
specification, as this fact is intuitively obvious.
Instead, and just like with our approach to verified parsing, formulating these
semantic checks as decidability proofs (1) \emph{forces} us formalize the natural
language property we wish to check \emph{independently of the code that performs
the checking,} and (2) \emph{enables} us to write the checking code that is
\emph{correct-by-construction}, as these decidability proofs are themselves
the very functions called after parsing to check whether the certificate or chain
satisfies the property in question.

\textbf{Single certificate property.}
For a given certificate, it must be the case that its \texttt{SignatureAlgorithm} field
contains the same algorithm identifier as the \texttt{Signature} field of
its \texttt{TBSCertificate} (R1 in Table~\ref{rules} of the Appendix).
As a formula of FOL, we could express this property with respect to
certificate \(c\) as
\[
  \forall s_1\, s_2, \mathit{SignAlg}(s_1,c) \land \mathit{TBSCertSignAlg}(s_2,c)
  \implies s_1 = s_2
\]
where \(\mathit{SignAlg}(s_1,c)\) and \(\mathit{TBSCertSignAlg}(s_2,c)\) express
respectively the properties that \(s_1\) is the signature algorithm identifier
of \(c\) and that \(s_2\) is the signature algorithm identifier of the
\texttt{TBSCertificate} of \(c\).
In \agda, we express this property, and the type of its corresponding
decidability proof, as follows (we omit the proof for space considerations).

\begin{code}
R1 : forall {@0 bs} -> Cert bs -> Set
R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c

r1 : forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
r1 c = ...  
\end{code}
The predicate |R1| expresses that the two signature algorithm
fields are equal using the binary relation |==|, which is defined in \agda{}'s
standard library.
Compared to the proof |r1|, |R1| is relatively simple: |==| is
\emph{parametric} in the type of the values it relates (meaning it uses no
specifics about the |SignAlg| type family), and is defined as the smallest
reflexive relation.
In contrast, the checking code |r1| \emph{must} concern itself with the
specifics of |SignAlg|.
In \xfon, signature algorithm fields are defined as a pair where the first
component is an object identifier (OID) and the second is an optional field for
parameters whose type \emph{depends upon that OID.}
So, to implement |r1| we must prove equality is decidable for OIDs
\emph{and} for all the signature algorithm parameter types we support.

\textbf{Certificate chain property.}
\begin{figure}
\begin{code}
IsConfirmedCA : forall {@0 bs} -> Cert bs -> Set

isConfirmedCA? : forall {@0 bs} (c : Cert bs) -> Dec (IsConfirmedCA c)

R23 :  forall {trust candidates} {@0 bs} (issuee : Cert bs) 
       -> Chain trust candidates issuee -> Set
R23 issuee c = All (IsConfirmedCA . proj2) (tail (toList c))

r23 :  forall {trust candidates} {@0 bs} (issuee : Cert bs)
       -> (c : Chain trust candidates issuee) -> Dec (R23 c)
r23 c = All.all? (isConfirmedCA? . proj2) (tail (toList c))
\end{code}  
  \caption{Semantic check for R23}
  \label{fig:s4-semantic-chain-check}
\end{figure}

For a certificate chain, it must be the case that every issuer certificate is a
CA certificate.
Specifically, RFC 5280 (Section 6.1.4) makes the following requirement for
issuer certificates:
\quoteRFC{%
  If certificate i is a version 3 certificate, verify that the
  basicConstraints extension is present and that cA is set to
  TRUE.  (If certificate i is a version 1 or version 2
  certificate, then the application MUST either verify that
  certificate i is a CA certificate through out-of-band means
  or reject the certificate.  Conforming implementations may
  choose to reject all version 1 and version 2 intermediate
  certificates.)
}
In \armor, we take the approach suggested in the last line of the quote (see
entry R19 of Table~\ref{rules} in the Appendix), so our task reduces to checking
that for each issuer certificate, the \texttt{basicConstraints} extension is
present and its \texttt{cA} field is set to true.

We formalize this semantic condition, listed as R23 in Table~\ref{rules} in
Figure~\ref{fig:s4-semantic-chain-check}. 
Predicate |IsConfirmedCA| (definition omitted) expresses the condition that the
\texttt{basicConstraints} extension is present in a certificate with field
\texttt{cA} set to |true|, and function |isConfirmedCA?| (definition omitted) is
the correct-by-construction implementation of that check.
Predicate |R23| is extends this property to all issuer certificates of a chain.
\begin{itemize}
\item The \agda standard library definition |All| is to |Any| (see
  Section~\ref{sec:s4-sound-complete-chain-building}) what |forall| is to
  |exists|.
  Given a predicate |Q : A -> Set| and a list |xs : List A|, |All Q xs| is the
  proposition that every element of |xs| satisfies |Q|.
  
\item The list we are concerned with in predicate |R23| is every certificate in the
  chain except the first (i.e., the end entity).
  This is expressed by |tail (toList c) : List (exists Cert)|.
  
\item Since the elements of this list are \emph{tuples} of type |exists Cert|
  (where the first component is an octet string and the second is a proof that
  string encodes a certificate), we form the predicate supplied to |All| by
  precomposing |IsConfirmedCA| with |proj2 : (c : exists Cert) -> Cert (proj1 c)|.
\end{itemize}
\noindent Finally, the sound-by-construction checker for this semantic condition
is |r23|, which is defined using |All.all?|, defined in the \agda standard
library.
|All.all?| takes a decision procedure that applies to a single element (in this
case, |isConfirmedCA? . proj2|) and returns a decision procedure that decides
whether the predicate holds for \emph{all} elements of the given list.



% LocalWords:  serializers cryptographic
