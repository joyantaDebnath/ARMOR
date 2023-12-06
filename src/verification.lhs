\section{Verification Goals and Correctness Proofs}
We now briefly discuss \armor{}'s verification 
goals and their correctness proofs. 
% Recall that, as shown in Figure~\ref{armor}, 
We provide formal correctness guarantee for the
following modules of \armor: \emph{parsers (\ie, PEM parser, Base64 decoder, X.690 DER and
  X.509 parsers)}, \emph{Semantic validator}, and \emph{Chain builder} (see Table \ref{table:summary-of-guarantees} for a summary of guarantees).
% A summary of these guarantees is in Table \ref{table:summary-of-guarantees}. 
%   , and
% \emph{String canonicalizer}.
For these verification tasks, 
which took 12 person months to complete, we use the \agda interactive theorem
prover~\cite{bove2009brief, No07_agda}. 
Due to space constraints, we only discuss the correctness guarantees of the X.690 DER and X.509 parsers, 
and relegate the discussion of the other components in the full version of the paper \cite{armor-full-version}. 

% In this section, we briefly introduce Agda and then detail the
% design and verified guarantees of \armor's \agda modules.

\begin{table}[t]
  % \captionsetup{font=footnotesize}
\centering
\sffamily\scriptsize
  \setlength\extrarowheight{1.5pt}
  \setlength{\tabcolsep}{1.5pt}
  \caption{Correctness guarantees for each module in \armor}
  \sffamily\scriptsize
  \label{table:summary-of-guarantees}
\centering
\begin{tabular}{c||c||c||c||c||c||}
\cline{2-6}
\textbf{}                                                                                                        & \textbf{\begin{tabular}[c]{@@{}c@@{}}PEM \\ Parser\end{tabular}}                              & \textbf{\begin{tabular}[c]{@@{}c@@{}}Base64 \\ Decoder\end{tabular}}             & \textbf{\begin{tabular}[c]{@@{}c@@{}}DER\\ Parser\end{tabular}}             & \textbf{\begin{tabular}[c]{@@{}c@@{}}Chain \\ Builder\end{tabular}}              & \textbf{\begin{tabular}[c]{@@{}c@@{}}Semantic\\ Validator\end{tabular}}          \\ \hline
\multicolumn{1}{||c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Correctness\\ Properties\end{tabular}}} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Maximality\\ Terminate\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminate\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminate\end{tabular}             & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminate\end{tabular}                                                                    & \begin{tabular}[c]{@@{}c@@{}}Sound\\ Complete\\ Terminate\end{tabular} \\ \hline
\multicolumn{1}{||c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Language\\ Security\\ Properties\end{tabular}}}          & Unambiguous                                                                             & N/A                                                                            & \begin{tabular}[c]{@@{}c@@{}}Unambiguous\\ Non-malleable\\ No substrings\end{tabular} & N/A                                                                                                                                              & N/A                                                                            \\ \hline
\end{tabular}
\end{table}


\noindent\textbf{Trusted Computing Base (TCB).}
Our TCB comprises of the \agda toolchain (v2.6.2.2), which includes its native
type-checker, compiler, and standard library (v1.7.1).
% In particular, 
Particularly, 
our use of \agda's standard library includes the module
\texttt{\small Data.Trie} (for the \emph{String canonicalizer}), which requires the
\texttt{\small --sized-types} language feature, and the module \texttt{\small IO}, which
requires the \texttt{\small --guardedness} language feature.
The use of these two features together \emph{in the declaration of a coinductive
  type} causes logical inconsistency~\cite{AgdaIssue-1209}.
In our code base,  the only module which enables both features is the
\emph{Driver Interface}. It, 
%(because it needs to invoke the \emph{String canonicalizer} and perform IO), 
% which, 
however, does not define any coinductive types.

\textbf{Termination.}
By default, \agda employs a syntactic termination checking that ensures that
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
In other words, if a program compiles, it is also proven to meet the
specifications described by its type.
Under the \emph{Curry-Howard}
correspondence~\cite{SU06_Lectures-on-the-Curry-Howard-Isomorphism}, we can view
\agda's types as \emph{propositions} and its terms as \emph{proofs} of the
propositions expressed by their types.
This makes \agda a powerful tool for both expressing programs and their
correctness, as it unifies the language of programs and proofs. 

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

We now explain the code listing in the figure, starting with the declaration of |Fin|.
\begin{itemize}
\item The |data| keyword allows us to introduce a new inductive type or
  inductive type family, in this case the type family |Fin|.
  ``Inductive'' here means that \agda allows us to define functions over |Fin n|
  by \emph{pattern matching} and \emph{structural recursion}, which we shall see shortly.
  
\item |Set| is the type of (small) types (we will omit the details of \agda's
  universe hierarchy).
  
\item |Fin| has two constructors, both of which have dual readings as ``mere
  data'' and as axiomatizations of the \emph{``is strictly less than''}
  predicate.
  As mere data, |fzero| corresponds to the integer 0; as an axiom, it states
  that 0 is strictly less than the successor |1 + n| of any nonnegative integer
  |n|.
  Similarly, as mere data |fsuc| corresponds to a primitive successor operation
  (like the Peano numbers), and as an axiom it corresponds to the following
  inference rule: if a number |i| is strictly less than |n|, then its successor
  is strictly less than |1 + n|.
 
\item Curly braces indicate function arguments that need not be passed
  explicitly, leaving \agda to infer their values from the types of other
  arguments to the function.
  For example, if |i| has type |Fin 5|, then we can write |fsuc i| and Agda can
  determine this has type |Fin 6|; if we wanted to make explicit the argument that
  instantiates parameter |n|, we would write |fsuc {5} i|.
\end{itemize}

The next definition of the figure is the function |toNat|, which is defined by
\emph{pattern matching} and \emph{recursion} over |Fin|.
We can think of |toNat| as extracting the ``mere data'' contained in an
expression of type |Fin n|.
\begin{itemize}
\item In the type signature of |toNat|, we use the syntactic sugar |forall| to
  omit the type of the parameter |n|, as Agda can infer this from the occurrence
  of |n| in the rest of the type, |Fin n -> Nat|.
  Note, we could have also use |forall| our presentation of the type signatures
  of constructors |fzero| and |fsucc|.
  
\item The definition of |toNat| is given with two equations, one each for the
  two constructors of |Fin|.
  \begin{itemize}
  \item In the first equation, we send |fzero| to 0.
    
  \item In the second equation, our |Fin| argument is of the form |fsuc i|.
    We make a recursive call |toNat i| and increment the result by |1|.
    Here, \agda can determine that the recursion is terminating, as |i| is
    structurally smaller than |fsuc i|.
  \end{itemize}
\end{itemize}





\subsection{Input Strings and Base64 Decoding}
We used |Fin| as our example throughout Section~\ref{sec:s4-preliminaries-agda}
because it plays a central role as the type of the language alphabet for our
\xsno DER and \xfon parsers, as well as the input and output types for Base64
decoding.
In general, parser inputs have types of the form |List A|, where |A| is the type
of language alphabet; for our PEM parser this is |Char|, Agda's primitive type
for character literals, and for our \xsno DER and \xfon parsers, this is
|UInt8|, an alias for |Fin 256|.
The ultimate result of our PEM parser is a string of sextets, \ie, a value of
type |List UInt6|, where |UInt6| is an alias for |Fin 64|.

The hand-off between the result of PEM parsing and the input to \xsno DER /
\xfon parsing (Figure~\ref{armor}, \circled{C} -- \circled{D}) is managed by the
Base64 decoder, whose formal correctness properties are established with respect
to a Base64 encoder (used only for specificational purposes).
Specifically, we prove: 1) that the encoder always produces a valid sextet
string; and 2) the encoder and decoder pair forms an
isomorphism between octet strings and valid sextet strings for encoding them.
This is summarized below in Figure~\ref{fig:s4-base64} (for space
considerations, all definitions have been omitted).

\begin{figure}[h]
  \begin{code}
ValidEncoding : List UInt6 -> Set
encode : List UInt8 -> List UInt6
decode : (bs : List UInt6) -> Valid64Encoding bs -> List UInt8

encodeValid : (bs : List UInt8) -> ValidEncoding (encode bs)

encodeDecode :  forall bs -> decode (encode bs) (encodeValid bs) == bs
decodeEncode :  forall bs -> (v : ValidEncoding bs)
                -> encode (decode bs v) == bs
  \end{code}
  \caption{Base64 encoding and decoding (types only)}
  \label{fig:s4-base64}
\end{figure}


\subsection{Verification of Parsers} We conceptually separate each parser verification task into \emph{language
specification}, \emph{language security verification}, and \emph{parser correctness verification}.

\subsubsection{Language specification} \label{sec:s4-lang-spec}
We provide parser-independent formalizations of the PEM, Base64, X.690
DER, and \xfon formats, greatly reducing the complexity of the specification
and increasing trust that they faithfully capture the natural language
description.
Much current research~\cite{ni2023asn1, ramananandro2019everparse}
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
machine-checked, rigorous alternative for the developers seeking to
understand the relevant specifications. 

More concretely, the relational specifications we give are of the
following form.
For a given language \(G\) with alphabet \(A\), we define a family of types
|G : List A -> Set|, where the family |G| is indexed by strings |xs : List A|
over the alphabet (for PEM the alphabet is characters, for X.690 and X.509 DER
it is unsigned 8-bit integers).
Such a family of types can serve the dual role as the internal representation of
the value encoded by \(\mathit{xs}\), i.e., a value of type |G xs| is not only a
proof that \(\mathit{xs}\) is in the language \(G\), 
but also the internal representation of the value decoded from \(\mathit{xs}\).

\begin{figure}[h]
  \begin{code}
MinRep : UInt8 -> List UInt8 -> Set
MinRep b1 [] = Top
MinRep b1 (b2 :: bs) =
  (b1 > 0 Lor (b1 == 0 Land b2 >= 128))
  Land (b1 < 255 Lor (b1 == 255 Land b2 <=127))
    
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
This specification takes the form of an Agda record (roughly analogous to a
C-style \texttt{struct}) that is parameterized by a bytestring |bs|.
\begin{itemize}
\item \textbf{Minimum representation.} \xsno DER requires that the two's
  complement encoding of an integer value consists of the minimum number of
  octets needed for this purpose.
  We \emph{express} this property with |MinRep|, which defines a relation between the
  first byte of the encoding and the remaining bytes; we \emph{enforce} that the
  property holds with field |minRep| of |IntegerValue| (in order to construct an
  expression of type |IntegerValue bs|, we must prove that |MinRep| holds for
  the head and tail of |bs|).
  
  The definition of |MinRep| proceeds by cases on whether or not the remaining
  byte string is empty.
  \begin{enumerate}
  \item If it is, we return the trivially true proposition |Top|, because a
    single byte is always minimal.
    
  \item Otherwise, if the bits of the first byte are all 0, the first bit of the
    second byte must be 1 (i.e., |b2 >= 128|); and if the bits of the first byte
    are all 1 (i.e., |b1 == 255|), then the first bit of the second byte must be
    0 (i.e., |b2 <= 127|).
  \end{enumerate}
  
\item \textbf{Erasure annotations.} The string |@0| is an annotation that marks
  the accompanying identifier as \emph{erased at runtime}.
  In the figure, only the field |val| (the integer encoded by |bs|) is present
  at runtime, with the remaining fields (and the parameter |bs|) erased by
  Agda's GHC backend.
  The annotations for runtime erasure not only improves the performance of ARMOR,
  but also serve to document, for programmers using ARMOR as a reference
  implementation, which components of the internal representation serve only
  specificational purposes.

\item \textbf{Nonempty encoding.} Fields |hd|, |tl|, and |bseq| together ensure
  that the encoding of an integer value ``consists of one or more
  octets.''~\cite{rec2002x}
  Specifically, |bseq| ensures that |bs| is of the form |hd :: tl|, where |hd|
  is the first content octet and |tl| contains the remaining content octets (if any).
  

\item \textbf{Linking the value and its encoding.}
  Field |valeq| forecloses any possibility that an expression of type |IntegerValue
  bs| populates the field |val| with an arbitrary integer by requiring that this
  field \emph{must} be equal to the result of decoding |bs| as a two's complement
  binary value, where |Base256.twosComp| is the decoding operation.
\end{itemize}


A major advantage of our approach to specifying X.509 is that it facilitates
proving properties \emph{about the grammar} without having to reason about
parser implementation details.
By verifying properties of grammar itself, we can be more confident that we have
accurately captured the meaning of the natural language descriptions. 

\subsubsection{Language security verification}
\label{sec:s4-lang-security}

We have proven \emph{unambiguousness} (a given input can encode \emph{at most one value} of a
particular type) for the supported subsets of formats
PEM,
\xsno \der, and \xfon, \emph{non-malleability} (distinct
inputs cannot encode identical values) for the supported
subsets of formats \xsno \der and \xfon, and \emph{no-substrings} (a language permits parsers no degrees
of freedom over which prefix of an input string it consumes) for all
\tlv structures.

\textbf{Unambiguous.}
We formally define unambiguousness of a language |G| in Agda as follows.
\begin{code}
Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
\end{code}
Read this definition as saying that for every string |xs|, any two inhabitants
of the internal representation of the value encoded by |xs| in |G| are equal.
In the context of \xfon, format ambiguity could result in interoperability
issues between standards-compliant producers and consumers (\eg, rejection
because the decoded certificate does not match the encoded certificate).

\textit{Challenges.} |Unambiguous| expresses a property much stronger
than might be first apparent.
To illustrate, showing |Unambiguous IntegerValue| requires showing that the
corresponding fields are equal --- \emph{even the purely specificaional fields.}
Once established, the additional strength afforded by |Unambiguous| significantly aids
development of our verified parsers; however, this means that specifications must
be carefuly crafted so as to admit unique proof terms.
In the case of |IntegerValue|, this means showing that any two proofs of |MinRep
hd tl| are equal.

Another challenging aspect in proving unambiguousness for X.690 DER in
particular is the format's support for sequences that have \emph{optional} and
\emph{default} fields, that is, fields that might not be present in the
sequence.
We are threatened with ambiguity if it is possible to mistake an optional field
whose encoding is present for another optional field whose encoding is absent.
To avoid this scenario, the X.690 format stipulates that every field of any
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
We express generally in Agda by |Raw|, given below.
\begin{code}
record Raw (G : List A -> Set) : Set where
  field
    D : Set
    to : {@0 xs : List A} -> G xs -> D
\end{code}

An inhabitant of |Raw G| consists of a type |D|, intended to be the
``raw data'' of |G|, together with a function |to| that should extract this data
from any inhabitant of |G xs|.
To illustrate, consider the case for |IntegerValue| below.
\begin{code}
  RawIntegerValue : Raw IntegerValue
  Raw.D RawIntegerValue = IntZ
  Raw.to RawIntegerValue = IntegerValue.val
\end{code}
\noindent This says that the raw representation for \xsno DER integer values is |IntZ| (a
type for integers defined in Agda's standard library), and the extraction
function is just the field accessor |IntegerValue.val|.

Once we have defined an instance of |Raw G| for a language specification |G|,
we express non-malleability of |G| with respect to that raw representation
with the following property: give two input strings |xs1| and |xs2|, with witnesses
|g1 : G xs1| and |g2 : G xs2|, if the raw representations of |g1| and |g2| are
equal, then not only are strings |xs1| and |xs2| equal, but also |g1| and |g2|.
In Agda, this is written as:
\begin{code}
NonMalleable : {G : @0 List A -> Set} -> Raw G -> Set
NonMalleable{G} R =
  forall {@0 xs1 xs2} -> (g1 : G xs1) (g2 : G xs2)
  -> Raw.to R g1 == Raw.to R g2 -> (xs1 , g1) ==  (xs2 , g2)  
\end{code}
For |IntegerValue| in particular, proving |NonMalleable RawIntegerValue|
requires showing |Base256.twosComp| is itself injective.

\textbf{No-Substrings.}
The final language property we discuss, which we dub \emph{``no-substrings,''}
expresses formally the intuitive idea that a language permits parsers no degrees
of freedom over which prefix of an input string it consumes.
As we are striving for \emph{parser independence} in our language
specifications, we formulate this property as follows: for any two prefixes of
an input string, if both prefixes are in the language |G|, then they are equal.
In Agda, we express this as |NoSubstrings| below.
\begin{code}
NoSubstrings G =
  forall {xs1 ys1 xs2 ys2} -> xs1 ++ ys1 == xs2 ++ ys2
  -> G xs1 -> G xs2 -> xs1 == xs2
\end{code}
Given that \xfon uses \tlv encoding, it is
unsurprising that we are able to prove |NoSubstrings| holds for our
specification.
However, we call explicit attention to this property here because for two
reasons: 1) it an essential lemma in our proof of \emph{strong completeness} of
our \xfon parser (see Section~\ref{sec:s4-parser-sound-complete-strong}); and 2)
this property \emph{does not hold} for the PEM format due to leniency in
end-of-line encoding, and so to show strong completeness we need an additional
property for PEM parsers, \emph{maximality}.

\subsubsection{Parser correctness verification}
We now describe our approach to verified parsing. We write parsers that are \emph{sound} and \emph{complete}.
For a language \(G\), \emph{soundness} of a parser means that every
bytestring it accepts is in the language, and \emph{completeness} means that it
accepts every bytestring in the language.
Our approach to verifying these properties for all our parsers is to make them
\emph{correct-by-construction}, meaning that parsers do not merely indicate
success or failure with e.g.\ an integer code, but return \emph{proofs}. 
If the parser is successful, this is a proof that some prefix of its input is in
the language, and if the parser fails, it returns a proof that \emph{no} prefix
of its input is. That is to say, our parsers are really proofs that membership
(in \(G\)) of an input's prefix is decidable.

\noindent\textbf{The type of correct-by-construction parsers:}
\label{sec:s4-parsers-cbc}
Our first step is to formally define what success in means.
In first-order logic, we would express the condition for the parser's success on a prefix of
|xs| as \(\exists \mathit{ys}\, \mathit{zs}, \mathit{xs} = \mathit{ys} +\!\!\!+
\mathit{zs} \land |G ys|\).
That is to say, on success the parser consumes some prefix of the input string
that is in the language |G|.
In Agda, we express the result of successful parsing as the parameterized record
|Success|, shown below.
\begin{figure}[h]
  \centering
  \begin{code}
    record Success 
      (G : List UInt8 -> Set) (xs : List UInt8) : Set where
      constructor success
      field
        @0 prefix : List UInt8
        suffix : List UInt8
        @0 pseq : prefix ++ suffix == xs
        value : G prefix
  \end{code}
  \caption{Success conditions for parsing}
  \label{fig:parser-success}
\end{figure}
In the definition, understand parameters |G| and |xs| as the language denoted by
a production rule and an input string, respectively.
The fields of the record are: |prefix|, the consumed prefix of the input (erased
at runtime); |suffix|, the remaining suffix of the input from which we parse
subsequent productions; |pseq|, which relates |prefix| and |suffix| to the input
string |xs| (also runtime erased); and |value|, which serves dual roles as both
the internal data representation of the value encoded by |prefix| \textbf{and}
a proof that |prefix| is in the language |G|.  
As a consequence, \emph{soundness will be immediate}.

Our next step is to define what parser failure means.
We define this to be the condition that \emph{no} prefix of the input |xs| is in
the language of |G|, which is to say the failure condition is the
\emph{negation} of the success condition: |not Success G xs|.

To have the parser return |Success G xs| on success and |not Success G xs| on
failure, we use datatype |Dec| in the Agda standard library, shown below.
\begin{code}
data Dec (Q : Set) : Set where
  yes : Q -> Dec Q
  no  : not Q -> Dec Q
\end{code}
Reading |Dec| as programmers, |Dec Q| is a tagged union type which can be
populated using either values of type |Q| or type |not Q|; as mathematicians, we
read it as the type of proofs that |Q| is \emph{decidable}.
Expressed as a formula of FOL, |Dec Q| is simply \(Q \lor \neg Q\); however,
note that constructive logic (upon which Agda is based) does not admit LEM, so
this disjunction must be proven on a case-by-case basis for each |A| in
question, as there are some propositions which can neither be proven nor refuted.

We are now able to complete the definition of the type of parsers, shown below.
\begin{figure}[h]
  \begin{code}
Parser : (List UInt8 -> Set) -> Set
Parser G = forall xs -> Dec (Success G xs)    
  \end{code}
  \caption{Definition of |Parser|}
  \label{fig:parser-def}
\end{figure}%
|Parser| is a family of types, where for each language |G|, the type
|Parser G| is the proposition that, for all bytestrings |xs|, it is decidable
whether some prefix of |xs| is in |G|; alternatively, we can (as programmers)
read it as the type of functions which take a bytestring and possibly return a
parsed data structure and remaining bytestring to continue parsing.

\textit{Challenges.}
The guarantee that, on failure, the parser returns |not Success G xs| is very
strong, as it asserts a property concerning \emph{all possible prefixes} of the
input.
This strength is double-edged: while having this guarantee makes proving
completeness straightforward, \emph{proving} it means ruling out all possible
ways in which the input could be parsed.
In some cases, we have made choices about parser implementations to facilitate
the proofs concerning the failure case, at a cost to performance.
The clearest example of such a trade-off is in our parsers for X.690
\texttt{Choice} values, which are implemented using back-tracking.

\textbf{Maximal parsers:} As we mentioned at the end of
Section~\ref{sec:s4-lang-spec}, the PEM format does not enjoy the
\emph{no-substrings} property.
To facilitate our implementation of correct-by-construction PEM parsers, and
(ultimately) prove strong completeness, we have augmented the specifications of
these parsers to guarantee they consume \emph{the largest prefix of the input
  compliant with the format.}

\begin{figure}
\begin{code}
MaximalSuccess : forall G xs -> Dec (Success A xs) -> Set
MaximalSuccess G xs (no _) = Top
MaximalSuccess G xs (yes s) = forall pre suf -> pre ++ suf == xs
  -> G pre -> length pre <= length (Success.prefix s)

record MaximalParser (G : List A -> Set) : Set where
  field
    p : Parser G
    max : forall xs -> MaximalSuccess (p xs)
\end{code}
  \caption{Definition of |MaximalParser|}
  \label{fig:s4-parser-maximal}
\end{figure}

The formalization of this in Agda is shown in
Figure~\ref{fig:s4-parser-maximal}.
Definition |MaximalSuccess| expresses what it means for a parser's successful
result to be maximal: if parsing |xs| was successful (|yes s|), then any other
prefix |pre| of |xs| in the language |G| is no greater than that consumed by the
parser.
In the record |MaximalParser|, we couple together a parser |p| together with a
proof |max| that, for \emph{every} input string |xs|, if |p| is successful
parsing |xs| then that success is maximal.

\noindent\textbf{Correctness properties:}
\label{sec:s4-parser-sound-complete-strong}
We now show our formal definitions and proofs of soundness and completeness for
parsing, beginning with soundness.
\begin{figure}[h]
  \begin{code}
Sound : (G : List A -> Set) -> Parser G -> Set
Sound G p =
  forall xs -> (w : IsYes (p xs)) -> G (Success.prefix (toWitness w))    

soundness : forall {G} -> (p : Parser G) -> Sound G p
soundness p xs w = Success.value (toWitness w)
  \end{code}
  \caption{Parser soundness (definition and proof)}
  \label{fig:s4-parser-soundness}
\end{figure}%

\textbf{Soundness.}
Recall that parser soundness means that, if a parser for \(G\) accepts a prefix of the
input string, then that prefix is in \(G\).
The Agda definition and proof of soundness for all of our parsers is
shown in Figure~\ref{fig:s4-parser-soundness}, which we now detail.
Beginning with |Sound|, the predicate expressing that parser |p| is sound with
respect to language |G|, the predicate |IsYes| (definition omitted) expresses
the property that a given decision (in this case, one of type |Dec (Success G
xs)|) is affirmative (i.e., constructed using |yes|).
The function |toWitness : forall {Q} {d : Dec Q} -> IsYes d -> Q| takes a
decision |d| for proposition |Q| and proof that it is affirmative, and produces
the underlying proof of |Q|.
Thus, we read the definition of |Sound G p| as: ``for all input strings |xs|, if
parser |p| accepts |xs|, the the prefix it consumes is in |G|.''

The proof |soundness| states that \emph{all parsers are sound}.
As our parsers are correct-by-construction, the definition is straightforward:
we use |toWitness| to extract the proof of parser success, i.e., a term of type
|Success G xs|, then use the field accessor |Success.value| to obtain the
desired proof that the consumed prefix is in |G|.

\textbf{Completeness.}
Recall that the definition of parser completeness with respect to a language |G|
means that if an input string |xs| is in |G|, the parser accepts \emph{some
  prefix of |xs|}.
Of course, this property in isolation does not rule out certain bad behavior
that threatens security; specifically, it does not constrain the parser's
freedom over (1) which prefix of the input is consumed, and (2) how the internal
datastructure is constructed.
However, and as we have discussed in Section~\ref{sec:s4-lang-spec}, these
should be thought of as properties of the \emph{language}, and \emph{not} its
parsers.
To emphasize this, after discussing the completeness proof we will show how,
using language properties, it can be strengthed to address the aforementioned
security concerns.

\begin{figure}[h]
\begin{code}
Complete : (G : @0 List A -> Set) -> Parser G -> Set
Complete G p = forall xs -> G xs -> IsYes (p xs)

trivSuccess : forall {G} {xs} -> G xs -> Success G xs

completeness : forall {G} -> (p : Parser G) -> Complete G p
completeness p xs inG = fromWitness (p xs) (trivSuccess inG)
\end{code}
  \caption{Parser completeness (definition and proof)}
  \label{fig:s4-parser-wkcompleteness}
\end{figure}

Figure~\ref{fig:s4-parser-wkcompleteness} shows our definition and proof of
\emph{completeness} in \agda, which we now detail.
The definition of |Complete| directly translates our notion of completeness: for
every input string |xs|, if |xs| is in |G|, then parser |p| accepts some prefix
of |xs|.
For the proof, we first prove a straightforward lemma |trivSuccess| (definition
omitted) that states any proof that |xs| is in |G| can be turned into a proof
that some prefix of |xs| (namely, |xs| itself) is in |G|.
With this, the proof of |completeness| uses the function |fromWitness : {Q :
  Set} -> (d : Dec Q) -> Q -> IsYes d|, which intuitively states that if a
proposition |Q| is true, then any decision for |Q| must be in the affirmative.


\textbf{Strong completeness.}
We will now see how, using language properties, our parser completeness result
can be strengthened to rule out bad behavior that could compromises security.
To be precise, when a string |xs| is in the language |G|, we desire that the
parser consumes \emph{exactly} |xs|, and furthermore that there is only one way
for it to construct the internal data representation of |G| from |xs|.
To show both of these guarantees, it suffices that |G| satisfies the properties
|Unambiguousness| and |NoSubstrings| (see Section~\ref{sec:s4-lang-spec}).

\begin{figure}[h]
  \begin{code}
StronglyComplete : (G : @0 List A -> Set) -> Parser G -> Set
StronglyComplete G p = forall xs -> (inG : G xs)
  -> exists  (w : IsYes (p xs))
             (  let s = toWitness w in
                (xs , inG) == (Success.prefix x , Success.value s))

strongCompleteness
  : forall {G} -> Unambiguous G -> NoSubstrings G
    -> (p : Parser G) -> StronglyComplete G p
strongCompleteness ua ns p xs inG = (w , strong xs inG s)
  where
  w = completeness p inG
  s = toWitness w
  strong : forall xs inG s -> (dashcomma inG) == (dashcomma Success.value s)
  strong xs inG s with ns _ inG (Success.prefix s)
  ... | refl with ua inG (Success.value s)
  ... | refl = refl
  \end{code}
  \caption{Strong completeness (definition and proof)}
  \label{fig:s4-parser-stcompleteness}
\end{figure}

Figure~\ref{fig:s4-parser-stcompleteness} shows the definition and proof of our
strengthened completeness result.
For the definition, |StronglyComplete G p| says that, if we have a proof |inG| that
|xs| is in |G|, then not only does there exist a witness |w| that the parser
accepts some prefix of |xs|, but prefix it consumes is |xs| and the
proof it returns is |inG|.
Recall that the assumption |inG| and the |value| field of the |Success| record
serve dual roles: they are not only proofs that a string is in a language, but
also the internal data representation of the value encoded by |xs|.
So, saying they are equal means the internal representations are equal.

The proof, |strongCompleteness|, shows that to prove |StronglyComplete|, it
suffices that the language |G| satisfies |Unambiguous| and |NoSubstrings|.
In the definition, we exhibit witness |w| using the previous proof
|completeness|, and in the helper proof |strong| we use the assumptions |ns :
NoSubstrings G| and |ua : Unambiguous G| to prove that |xs| and |inG| are equal
to the |prefix| consumed and |value| returned by |p xs|.
Note that in the type signature of |strong|, |dashcomma| is a \emph{function}
(with precedence lower than ordinary function application) that builds a tuple,
used when the type of the second component of the tuple uniquely determines the
value of the first component.

\emph{Strong completeness from maximality.}
For PEM, even though the format lacks the \emph{no-substrings} property we can
still prove strong completeness by leveraging the fact that our parsers are
guaranteed to be \emph{maximal.}
Intuitively, this is because if |xs| is in |G|, then the largest possible prefix
of |xs| in |G| is |xs| itself.
We show the formal statement of the theorem below, omitting the proof for space
considerations.
\begin{figure}[h]
  \begin{code}
strongCompletenessMax : forall {G} -> Unambiguous G
  -> (m : MaximalParser G)
  -> StronglyComplete G (MaximalParser.p m)
  \end{code}
  \caption{Strong completeness from parser maximality}
  \label{fig:s4-parser-stcompleteness-max}
\end{figure}

% 
% 
% 

% \subsection{Verification of Chain Builder}
% The section presents the \emph{Chain builder}, for which we have proven
% soundness.
% Adhering to our discipline of providing high-level, relational specifications,
% we dedicate the bulk of this section to explaining how soundness is formalized,
% presenting at the end the type of our correct-by-construction chain builder.

% \subsubsection{Relating a Certificate to a Certificate of its Issuer}

% \begin{figure}
%   \begin{code}
% _IsIssuerFor_ : forall {@0 xs1 xs2} -> Cert xs1 -> Cert xs2 -> Set
% issuer IsIssuerFor issuee =
%   NameMatch (Cert.getIssuer issuee) (Cert.getSubject issuer)    

% _IsIssuerFor_In_ :  forall {@0 xs1 xs2} -> Cert xs1 -> Cert xs2
%                     -> (certs : List (exists Cert)) -> Set
% issuer IsIssuerFor issuee In certs =
%   issuer IsIssuerFor issue Land (dashcomma issuer) `elem` certs
%   \end{code}
%   \caption{|_IsIssuerFor_In_| relation}
%   \label{fig:isissuer}
% \end{figure}

% In Figure~\ref{fig:isissuer}, |c1 IsIssuerFor c2| expresses the property that |c1|
% is a certificate for the issuer of certificate |c2|.
% \agda provides great flexibility in defining infix and mixfix operations through
% the use of underscores in identifiers, so by writing |_IsIssuerFor_|, we can use
% |IsIssuerFor| as a infix binary relation.
% |IsIssuerFor| is defined using |NameMatch| (definition not shown), which
% expresses that two distinguished names are equal after string canonicalization.

% Of course, for chain building we are not just interested in \emph{whether} one
% certificate represents an issuer for another, but \emph{where} that issuer came
% from, \ie, whether it came from the trusted CA certificates or as part of the
% message sent by the entity we are trying to authenticate.
% It is therefore useful to define the 3-place (mixfix) relation |c1 IsIssuerFor
% c2 In certs|, which expresses the additional property that |issuer| is an
% element of |certs|.
% We briefly explain the unfamiliar parts of this definition.
% First, the type |exists
% Cert| is a convenience notation for the type of pairs whose first component is a
% bytestring |xs| and whose second component is a proof of type |Cert xs|;
% therefore, the type of the argument |certs : List (exists Cert)| tells us
% |certs| is a list of such tuples.
% Second, the binary relation |_`elem`_| (appearing in the definition as
% |(dashcomma issuer) `elem` certs|) is defined in \agda's standard library and
% expresses that the left expression is an element of the list on the right.

% \subsubsection{Definition of |Chain| and the Sound-By-Construction Chain Builder}

% \begin{figure}
%   \begin{code}
% data Chain (trust certs : List (exists Cert))
%   : forall {@0 xs} -> Cert xs -> Set where
%   root :  forall {@0 xs1 xs2} {c : Cert xs1} {r : Cert xs2}
%           -> r IsIssuerFor c In trust -> Chain trust certs c
%   link :  forall {@0 xs1 xs2} {c1 : Cert xs1} {c2 : Cert xs2}
%           -> (isIn : c1 IsIssuerFor c2 In certs)
%           -> Chain trust (certs emdash (proj2 isIn)) c2
%           -> Chain trust certs c1
%   \end{code}
%   \caption{|Chain|}
%   \label{fig:s4-chain}
% \end{figure}

% We now have everything need to specify a correct chain, shown in
% Figure~\ref{fig:s4-chain}.
% |Chain trust certs c| is the type of proofs that there exists a path beginning
% with the entity whose certificate is |c|, ending with a certificate in |trust|,
% and whose intermediate steps are pulled uniquely from |certs|.
% The base case for |Chain| is given by constructor |root|, which says the chain
% is complete if we find a certificate for the issuer of |c| in |trust|.
% In the inductive case, we have that if |c1| is the certificate for an issuer of
% |c2| in the input certificate list |certs|, then to build a valid chain of trust
% to |c1| we need a valid chain of trust to |c2|.

% Moreover, to prohibit |c2| from appearing than once, the list of valid
% intermediate certs between |c2| and the trust anchor must be reduced.
% This is captured by the expression |certs emdash (proj2 isIn)|, where |emdash|
% takes a list and a proof some element is a member of it and returns a list where
% that member has been remove.
% Not only does this capture a crucial correctness guarantee, but it is essential
% for convincing \agda's termination checker that chain building is terminating:
% since the element we are trying to remove has been proven to be in the list, the
% length of the resulting list is strictly smaller than the list we started with.

% \begin{figure}
%   \begin{code}
% buildChains
%   :  forall (trust certs : List (exists Cert))
%      -> forall {@0 bs} (c : Cert bs) -> List (Chain trust certs c)
% buildChains = ...
%   \end{code}
%   \caption{Chain building function (type only)}
%   \label{fig:s4-chain-builder}
% \end{figure}
% We can at last present the type of our sound-by-construction chain builder,
% shown in Figure~\ref{fig:s4-chain-builder}.
% We read it as follows: for all certificate lists |trust| and |certs|, and for
% every certificate |c|, we can produce a list of chains which authenticates |c|
% using intermediate certificates for |certs| and ending with an issuing
% certificate from |trust|.


% \subsection{Verification of String Canonicalizer}


% \subsection{Verification of Semantic Validator}
% Our approach to semantic validation, as outlined in
% Section~\ref{sec:s3-insights-on-tech-challenges}, is separating those properties that should
% be verified for a single certificate and those that concern the entire chain.
% For each property to validate, we formulate in Agda a predicate expressing
% satisfaction of the property by a given certificate or chain, then prove that
% these predicates are decidable (|Dec|, Section~\ref{sec:s4-parsers-cbc}).
% In what follows, we illustrate with two relatively simple concrete examples: one
% predicate for a single certificate and one for a certificate chain.

% Before we illustrate with examples, we stress that the purpose of this setup is
% \emph{not} to give decidability results for the semantic checks of the \xfon
% specification, as the mere fact that they are decidable is intuitively obvious.
% Instead, and just like with our approach to verified parsing, formulating these
% semantic checks as decidability proofs (1) \emph{forces} us formalize the natural
% language property we wish to check \emph{independently of the code that performs
% the checking,} and (2) \emph{enables} us to write the checking code that is
% \emph{correct-by-construction}, as these decidability proofs are themselves
% the functions called after parsing to check whether the certificate or chain
% satisfies the property.

% \textbf{Single certificate property.}
% For a given certificate, it must be the case that its \texttt{SignatureAlgorithm} field
% contains the same algorithm identifier as the \texttt{Signature} field of
% its \texttt{TBSCertificate} (R1 in Table~\ref{rules} of the Appendix).
% As a formula of FOL, we could express this property with respect to
% certificate \(c\) as
% \[
%   \forall s_1\, s_2, \mathit{SignAlg}(s_1,c) \land \mathit{TBSCertSignAlg}(s_2,c)
%   \implies s_1 = s_2
% \]
% where \(\mathit{SignAlg}(s_1,c)\) and \(\mathit{TBSCertSignAlg}(s_2,c)\) express
% respectively the properties that \(s_1\) is the signature algorithm identifier
% of \(c\) and that \(s_2\) is the signature algorithm identifier of the
% \texttt{TBSCertificate} of \(c\).
% In Agda, we express this property, and the type of its corresponding
% decidability proof, as follows (we omit the proof for space considerations).

% \begin{code}
% R1 : forall {@0 bs} -> Cert bs -> Set
% R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c

% r1 : forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
% r1 c = ...  
% \end{code}
% The predicate |R1| expresses that the two signature algorithm
% fields are equal using the binary relation |==| defined in Agda's standard library.
% Compared to the proof |r1|, |R1| is relatively simple: |==| is
% \emph{parametric} in the type of the values it relates (meaning it uses no
% specifics about the |SignAlg| type family), and is defined as the smallest
% reflexive relation.
% In contrast, the checking code |r1| \emph{must} concern itself with the
% specifics of |SignAlg|.
% In \xfon, signature algorithm fields are defined as a pair where the first
% component is an object identifier (OID) and the second is an optional parameters
% field whose type \emph{depends upon that OID.}
% So, to implement |r1| we must prove equality is decidable for OIDs
% \emph{and} for all of the signature algorithm parameter types we support.

% \textbf{Certificate chain property.}
% For a certificate chain, it must be the case that a certificate does not appear
% more than once in a prospective certificate path (R20 in Table~\ref{rules} of the Appendix).
% As a formula of FOL, we could express this property with respect to a
% certificate chain \(\mathit{cc}\) as
% \[
%   \begin{array}{l}
%     \forall c_1\, c_2\, i_1\, i_2. \mathit{InChain}(c_1,i_1,\mathit{cc}) \land
%     \mathit{InChain}(c_2,i_2,\mathit{cc})
%     \\ \quad \land\ i_1 \neq i_2 \implies c_1 \neq c_2
%   \end{array}
% \]
% where \(\mathit{InChain}(c_1,i_1,\mathit{cc})\) is the property that certificate
% \(c_1\) is at index \(i_1\) in chain \(\mathit{cc}\).
% The Agda standard library provides a definition of the property that all entries
% of a list are distinct from each other, written below as |List.Unique|, as well
% as a proof that this property is decidable, written |List.unique?|, provided
% that the type of the list's elements support decidable equality.
% We express this predicate and its corresponding decidability proof in Agda as
% % We have proven equality is decidable for certificates, so we can express this
% % property and corresponding decidability proof in Agda as
% \begin{code}
% R20 : forall {@0 bs} -> Chain bs -> Set
% R20 c = List.Unique (chainToList c)

% r20 : forall {@0 bs} (c : Chain bs) -> Dec (R20 c)
% r20 c = List.unique? decCertEq (chainToList c)
% \end{code}
% where function |chainToList| converts a certificate chain to a
% list of certificates and |decCertEq| is the proof that equality is decidable for
% certificates.
% Again, there is an asymmetry in the complexities of the specification and proof:
% while |List.Unique| is defined in 3 lines of code as an inductive type, the proof
% of |decCertEq| is substantially longer as it requires plumbing through the
% details of our formalization of |Cert|.
% By writing our checking function |r20| as a decision procedure, however, we do
% not have to worry that there is a mistake hidden somewhere in this complexity:
% by its very type, |r20| is \emph{correct-by-construction} with respect to the
% specification given by |R20|.






% % This section details the design and verified guarantees of our parser and
% % semantic checker modules.
% % \begin{itemize}
% % \item We start with an overview of our specifications of the supported subsets
% %   of the PEM, X.690 DER, and X.509 formats, emphasizing how their being
% %   \emph{parser independent} facilitates verifying language properties without
% %   mentioning implementation details.
  
% % \item Next, we describe our parsers, which are designed to be \emph{correct by
% %     construction} with respect to the language specifications.
% %   We achieve this by having parsers return \emph{proofs} either affirming or
% %   refuting language membership.
  
% % \item Finally, we describe approach to \emph{correct-by-construction} semantic
% %   validation.
% %   We express the desired properties of semantic checking as predicates over the
% %   internal data representations, with the code executing these checks
% %   implemented as proofs that these properties are decidable.
% % \end{itemize}

% % % \subsubsection*{Input Strings}
% % % Inputs to our parser have types of the form |List A|, where |A| is the type of
% % % the language alphabet.
% % % For our PEM parser, this is |Char|, Agda's primitive type for character
% % % literals.
% % % For our X.690 and X.509 parsers, this is the type |UInt8|, which is an alias for
% % % the Agda standard library type |Fin 256| (the type for nonnegative integers
% % % strictly less than 256).
% % % \subsubsection*{Base64 Decoding}
% % % We hand off the result of the PEM parser, which extracts the Base64 encoding of the
% % % certificates, to the X.509 parser, which expects an octet string, through a
% % % Base64 decoder that is verified with respect to an encoder.
% % % Specifically, we prove: 1) that the encoder always produces a valid sextet
% % % string (Base64 binary string); and 2) the encoder and decoder pair forms an
% % % isomorphism between octet strings and valid sextet strings for encoding them.
% % % This is summarized below in Figure~\ref{fig:s4-base64} (for space
% % % considerations, all definitions have been omitted).

% % % \begin{figure}[h]
% % %   \begin{code}
% % % ValidEncoding : List UInt6 -> Set
% % % encode : List UInt8 -> List UInt6
% % % decode : (bs : List UInt6) -> Valid64Encoding bs -> List UInt8

% % % encodeValid : (bs : List UInt8) -> ValidEncoding (encode bs)

% % % encodeDecode :  forall bs -> decode (encode bs) (encodeValid bs) == bs
% % % decodeEncode :  forall bs -> (v : ValidEncoding bs)
% % %                 -> encode (decode bs v) == bs
% % %   \end{code}
% % %   \caption{Base64 encoding and decoding (types only)}
% % %   \label{fig:s4-base64}
% % % \end{figure}


% % \subsection{Independent Specification}
% % \label{sec:s4-lang-spec}
% % Our first challenge concerns how the specification is represented, that is,
% % answering the question ``parser soundness and completeness \emph{with respect to
% %   what?}''
% % Our answer is that for each production rule |G| of the supported subset of the
% % PEM, X.690, and X.509 grammars, we define a predicate |G : List A -> Set| over
% % the input strings.
% % Membership of an input string |xs| in the language denoted by |G| corresponds to
% % the inhabitation of the type |G xs|.

% % \begin{figure}[h]
% %   \begin{code}
% % MinRep : UInt8 -> List UInt8 -> Set
% % MinRep b1 [] = Top
% % MinRep b1 (b2 :: bs) =
% %   (b1 > 0 Lor (b1 == 0 Land b2 >= 128))
% %   Land (b1 < 255 Lor (b1 == 255 Land b2 <=127))
    
% % record IntegerValue (@0 bs : List UInt8) : Set where
% %   constructor mkIntVal
% %   field
% %     @0 hd : UInt8
% %     @0 tl : List UInt8
% %     @0 minRep : MinRep hd tl
% %     val : IntZ
% %     @0 valeq : val == Base256.twosComp bs
% %     @0 bseq : bs == hd :: tl
% %   \end{code}
% %   \caption{Specification of integer values}
% %   \label{fig:s4-integervalue}
% % \end{figure}

% % We illustrate our approach with a concrete example: our specification of X.690
% % DER integer values, shown in Figure~\ref{fig:s4-integervalue}.
% % This specification takes the form of an Agda record (roughly analogous to a
% % C-style \texttt{struct}) that is parameterized by a bytestring |bs|.
% % \begin{itemize}
% % \item \textbf{Minimum representation.} \xsno BER requires that the two's
% %   complement encoding of an integer value consists of the minimum number of
% %   octets needed for this purpose.
% %   We \emph{express} this property with |MinRep|, which defines a relation between the
% %   first byte of the encoding and the remaining bytes; we \emph{enforce} that the
% %   property holds with field |minRep| of |IntegerValue| (in order to construct an
% %   expression of type |IntegerValue bs|, we must prove that |MinRep| holds for
% %   the head and tail of |bs|).
  
% %   The definition of |MinRep| proceeds by cases on whether or not the remaining
% %   byte string is empty.
% %   \begin{enumerate}
% %   \item If it is, we return the trivially true proposition |Top|, because a
% %     single byte is always minimal.
    
% %   \item Otherwise, if the bits of the first byte are all 0, the first bit of the
% %     second byte must be 1 (i.e., |b2 >= 128|); and if the bits of the first byte
% %     are all 1 (i.e., |b1 == 255|), then the first bit of the second byte must be
% %     0 (i.e., |b2 <= 127|).
% %   \end{enumerate}
  
% % \item \textbf{Erasure annotations.} The string |@0| is an annotation that marks
% %   the accompanying identifier as \emph{erased at runtime}.
% %   In the figure, only the field |val| (the integer encoded by |bs|) is present
% %   at runtime, with the remaining fields (and the parameter |bs|) erased by
% %   Agda's GHC backend.
% %   The annotations for runtime erasure not only improves the performance of ARMOR,
% %   but also serve to document, for programmers using ARMOR as a reference
% %   implementation, which components of the internal representation serve only
% %   specificational purposes.

% % \item \textbf{Nonempty encoding.} Fields |hd|, |tl|, and |bseq| together ensure
% %   that the encoding of an integer value ``consists of one or more
% %   octets.''~\cite{rec2002x}
% %   Specifically, |bseq| ensures that |bs| is of the form |hd :: tl|, where |hd|
% %   is the first content octet and |tl| contains the remaining bytes (if any).
  

% % \item \textbf{Linking the value and its encoding.}
% %   Field |valeq| forecloses any possibility that an expression of type |IntegerValue
% %   bs| populates the field |val| with an arbitrary integer by requiring that this
% %   field \emph{must} be equal to the result of decoding |bs| as a two's complement
% %   binary value, where |Base256.twosComp| is the decoding operation.
% % \end{itemize}

% % A major advantage of our approach to specifying X.509 is that it facilitates
% % proving properties \emph{about the grammar} without having to reason about
% % parser implementation details.
% % By verifying properties of grammar itself, we can be more confident that we have
% % accurately captured the meaning of the natural language descriptions. 
% % Two properties in particular that we have proven hold of our specification
% % capture the major design goal of X.690 DER formats: they are \emph{unambiguous},
% % meaning that a given bytestring can encode \emph{at most one value} of a
% % particular type; and they are \emph{non-malleable}, meaning that distinct
% % bytestrings cannot encode identical values.

% % \subsubsection{Unambiguous}
% % We formally define unambiguousness of a language |G| in Agda as follows.
% % \begin{code}
% % Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
% % \end{code}
% % Read this definition as saying that for every string |xs|, any two inhabitants
% % of the internal representation of the value encoded by |xs| in |G| are equal.

% % \textbf{Challenges.} |Unambiguous| expresses a property much stronger
% % than might be first apparent.
% % To illustrate, showing |Unambiguous IntegerValue| requires showing that the
% % corresponding fields are equal --- \emph{even the purely specificaional fields.}
% % Once established, the additional strength that |Unambiguous| significantly aids
% % development of the verified parser; however, this means that specifications must
% % be carefuly crafted so as to admit unique proof terms.
% % In the case of |IntegerValue|, this means showing that any two proofs of |MinRep
% % hd tl| are equal.

% % Another challenging aspect in proving unambiguousness for X.690 DER in
% % particular is the format's support for sequences that have \emph{optional} and
% % \emph{default} fields, that is, fields that might not be present in the
% % sequence.
% % We are threatened with ambiguity if it is possible to mistake an optional field
% % whose encoding is present for another optional field that is absent.
% % To avoid this scenario, the X.690 format stipulates that every field of any
% % ``block'' of optional or default fields must be given a tag distinct from every
% % other such field.
% % Our proof of unambiguousness for \xfon relies heavily on lemmas proving the
% % \xfon format obeys this stipulation.

% % \subsubsection{Non-malleable}
% % Compared to unambiguousness, non-malleability requires more machinery to
% % express, so we begin by discussing the challenges motivating this machinery.
% % Since the bytestring encodings are part of \emph{the very types of internal
% % representations}, e.g., |IntegerValue xs|, it is impossible to express equality
% % between internal representations |a1 : G xs1| and |a2 : G xs2| without
% % \emph{already assuming |xs1| is equal to |xs2|}.
% % Thus, to make non-malleability non-trivial, we must express what is the
% % ``raw'' internal datatype corresponding to |G|, discarding the specificational
% % components.
% % We express this general notion in Agda by |Raw|, given below.
% % \begin{code}
% % record Raw (G : List A -> Set) : Set where
% %   field
% %     D : Set
% %     to : {@0 xs : List A} -> G xs -> D
% % \end{code}

% % An inhabitant of |Raw G| consists of a type |D|, intended to be the
% % ``raw data'' of |G|, together with a function |to| that should extract this data
% % from any inhabitant of |G xs|.
% % To illustrate, consider the case for |IntegerValue| below.
% % \begin{code}
% %   RawIntegerValue : Raw IntegerValue
% %   Raw.D RawIntegerValue = IntZ
% %   Raw.to RawIntegerValue = IntegerValue.val
% % \end{code}
% % \noindent This says that the raw representation for integer values is |IntZ| (a
% % type for integers defined in Agda's standard library), and the extraction
% % function is just the field accessor |IntegerValue.val|.

% % Once we have defined an instance of |Raw G| for a language specification |G|,
% % we express non-malleability of |G| with respect to that raw representation
% % with the following property: give two input strings |xs1| and |xs2|, with witnesses
% % |g1 : G xs1| and |g2 : G xs2|, if the raw representations of |g1| and |g2| are
% % equal, then not only are strings |xs1| and |xs2| equal, but also |g1| and |g2|.
% % In Agda, this is written as:
% % \begin{code}
% % NonMalleable : {G : @0 List A -> Set} -> Raw G -> Set
% % NonMalleable{G} R =
% %   forall {@0 xs1 xs2} -> (g1 : G xs1) (g2 : G xs2)
% %   -> Raw.to R g1 == Raw.to R g2 -> (xs1 , g1) ==  (xs2 , g2)  
% % \end{code}
% % For |IntegerValue| in particular, proving |NonMalleable RawIntegerValue|
% % requires showing |Base256.twosComp| is itself injective.

% % \subsubsection{No Substrings}
% % The final language property we discuss, which we dub \emph{``no substrings,''}
% % expresses formally the intuitive idea that a language permits parsers no degrees
% % of freedom over which prefix of an input string it consumes.
% % As we are striving for \emph{parser independence} in our language
% % specifications, we formulate this property as follows: for any two prefixes of
% % an input string, if both prefixes are in the language |G|, then they are equal.
% % In Agda, we express this as |NoSubstrings| below.
% % \begin{code}
% % NoSubstrings G =
% %   forall {xs1 ys1 xs2 ys2} -> xs1 ++ ys1 == xs2 ++ ys2
% %   -> G xs1 -> G xs2 -> xs1 == xs2
% % \end{code}
% % Given that \xfon uses \(<T,L,V>\) encoding, it is
% % unsurprising that that we are able to prove |NoSubstrings| holds for our
% % specification.
% % However, this property is essential to understanding our \emph{strong
% %   completeness} result (see Section~\ref{sec:s4-parser-sound-complete-strong})
% % for parsing.

% % \subsubsection{Summary of Language Guarantees}
% % We have proven \emph{unambiguousness} for the supported subsets of formats
% % PEM,\todo{\tiny Remove if we haven't}
% % \xsno \der, and \xfon; we have proven \emph{non-malleability} for the supported
% % subsets of formats \xsno \der and \xfon, and proven \emph{no substrings} for all
% % TLV-encoded values.

% % % In addition, two properties in particular are essential to our proof of parser
% % % completeness.
% % % \begin{itemize}
% % % \item \textbf{Unambiguous:} at most one prefix of a bytestring can belong to
% % %   |G|.
% % %   That means, \(\forall \mathit{ws}\, \mathit{xs}\, \mathit{ys}\, \mathit{zs},
% % %   \mathit{ws} +\!\!\!+ \mathit{xs} = \mathit{ys} +\!\!\!+ \mathit{zs} \land
% % %   |G ws| \land |G ys| \implies \mathit{ws} = \mathit{ys}\).
  
% % % \item \textbf{Uniqueness:} the internal representation of |G xs| is uniquely
% % %   determined by |xs|.
% % %   That means (using \(\mathit{Rep}_{|G|}(x,\mathit{xs})\) to express ``\(x\) is the
% % %   internal representation of |G xs|''),
% % %   \(\forall x\, y\, \mathit{xs}, \mathit{Rep}_{|G|}(x,\mathit{xs}) \land
% % %   \mathit{Rep}_{|G|}(y,\mathit{xs}) \implies x = y\).
% % % \end{itemize}
% % % \noindent Both of these properties have been proven for our specification of
% % % X.509 certificates.
% % % In Agda, predicates |Unambiguous| and |Unique| are defined as follow.
% % % \begin{figure}[h]
% % %   \centering
% % %   \begin{code}
% % %     Unambiguous : (List UInt8 -> Set) -> Set
% % %     Unambiguous G =  forall {ws xs ys zs} -> ws ++ xs == ys ++ zs
% % %                      -> G ws -> G ys -> ws == ys
% % %     Unique : (List UInt8 -> Set) -> Set
% % %     Unique G = forall {xs} -> (g h : G xs) -> g == h
% % %   \end{code}
% % %   \caption{Definition of unambiguousness and uniqueness}
% % %   \label{fig:unambig-uniq}
% % % \end{figure}

% % \subsection{Sound and Complete Parsing}
% % We now describe our approach to verified parsing.
% % Recall that, for a language \(G\), \emph{soundness} of a parser means that every
% % bytestring it accepts is in the language, and \emph{completeness} means that it
% % accepts every bytestring in the language.
% % Our approach to verifying these properties for all our parsers is to make them
% % \emph{correct-by-construction}, meaning that parsers do not merely indicate
% % success or failure with e.g.\ an integer code, but return \emph{proofs}. 
% % If the parser is successful, this is a proof that some prefix of its input is in
% % the language, and if the parser fails, it returns a proof that \emph{no} prefix
% % of its input is.

% % \subsubsection{The Type of Correct-by-Construction Parsers}
% % \label{sec:s4-parsers-cbc}
% % Our first step is to formally define what success in means.
% % In FOL, we would express the condition for the parser's success on a prefix of
% % |xs| as \(\exists \mathit{ys}\, \mathit{zs}, \mathit{xs} = \mathit{ys} +\!\!\!+
% % \mathit{zs} \land |G ys|\).
% % That is to say, on success the parser consumes some prefix of the input string
% % that is in the language |G|.
% % In Agda, we express the result of successful parsing as the parameterized record
% % |Success|, shown below.
% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %     record Success 
% %       (G : List UInt8 -> Set) (xs : List UInt8) : Set where
% %       constructor success
% %       field
% %         @0 prefix : List UInt8
% %         suffix : List UInt8
% %         @0 pseq : prefix ++ suffix == xs
% %         value : G prefix
% %   \end{code}
% %   \caption{Success conditions for parsing}
% %   \label{fig:parser-success}
% % \end{figure}
% % In the definition, understand parameters |G| and |xs| as the language denoted by
% % a production rule and an input string, respectively.
% % The fields of the record are: |prefix|, the consumed prefix of the input (erased
% % at runtime); |suffix|, the remaining suffix of the input from which we parse
% % subsequent productions; |pseq|, which relates |prefix| and |suffix| to the input
% % string |xs| (also runtime erased); and |value|, which serves dual roles as both
% % the internal data representation of the value encoded by |prefix| \textbf{and}
% % a proof that |prefix| is in the language |G|.  
% % As a consequence, \emph{soundness will be immediate}.

% % Our next step is to define what parser failure means.
% % We define this to be the condition that \emph{no} prefix of the input |xs| is in
% % the language of |G|, which is to say the failure condition is the
% % \emph{negation} of the success condition: |not Success G xs|.

% % To have the parser return |Success G xs| on success and |not Success G xs| on
% % failure, we use datatype |Dec| in the Agda standard library, shown below.
% % \begin{code}
% % data Dec (A : Set) : Set where
% %   yes : A -> Dec A
% %   no  : not A -> Dec A
% % \end{code}
% % Reading |Dec| as programmers, |Dec A| is a tagged union type which can be
% % populated using either values of type |A| or type |not A|; as mathematicians, we
% % read it as the type of proofs that |A| is \emph{decidable}.
% % Expressed as a formula of FOL, |Dec A| is simply \(A \lor \neg A\); however,
% % note that constructive logic (upon which Agda is based) does not admit LEM, so
% % this disjunction must be proven on a case-by-case basis for each |A| in
% % question, as there are some propositions which can neither be proven nor refuted.

% % We are now able to complete the definition of the type of parsers, shown below.
% % \begin{figure}[h]
% %   \begin{code}
% % Parser : (List UInt8 -> Set) -> Set
% % Parser G = forall xs -> Dec (Success G xs)    
% %   \end{code}
% %   \caption{Definition of |Parser|}
% %   \label{fig:parser-def}
% % \end{figure}%
% % |Parser| is a family of types, where for each language |G|, the type
% % |Parser G| is the proposition that, for all bytestrings |xs|, it is decidable
% % whether some prefix of |xs| is in |G|; alternatively, we can (as programmers)
% % read it as the type of functions which take a bytestring and possibly return a
% % parsed data structure and remaining bytestring to continue parsing.

% % \textbf{Challenges.}
% % The guarantee that, on failure, the parser returns |not Success G xs| is very
% % strong, as it asserts a property concerning \emph{all possible prefixes} of the
% % input.
% % This strength is double-edged: while having this guarantee makes proving
% % completeness straightforward, \emph{proving} it means ruling out all possible
% % ways in which the input could be parsed.
% % In some cases, we have made choices about parser implementations to facilitate
% % the proofs concerning the failure case, at a cost to performance.
% % The clearest example of such a trade-off is in our parsers for X.690
% % \texttt{Choice} values, which are implemented using back-tracking.

% % \subsubsection{Parser Soundness, Completeness, and Strong Completeness}
% % \label{sec:s4-parser-sound-complete-strong}
% % We now show our formal definitions and proofs of soundness and completeness for
% % parsing, beginning with soundness.
% % \begin{figure}[h]
% %   \begin{code}
% % Sound : (G : @0 List A -> Set) -> Parser G -> Set
% % Sound G p =
% %   forall xs -> (w : IsYes (p xs)) -> G (Success.prefix (toWitness w))    

% % @0 soundness : forall {G} -> (p : Parser G) -> Sound G p
% % soundness p xs w = Success.value (toWitness w)
% %   \end{code}
% %   \caption{Parser soundness (definition and proof)}
% %   \label{fig:s4-parser-soundness}
% % \end{figure}%

% % \textbf{Soundness.}
% % Recall that parser soundness means that, if a parser for \(G\) accepts a prefix of the
% % input string, then that prefix is in \(G\).
% % The Agda definition and proof of soundness for all of our parsers is
% % shown in Figure~\ref{fig:s4-parser-soundness}, which we now detail.
% % Beginning with |Sound|, the predicate expressing that parser |p| is sound with
% % respect to language |G|, the predicate |IsYes| (definition omitted) expresses
% % the property that a given decision (in this case, one of type |Dec (Success G
% % xs)|) is affirmative (i.e., constructed using |yes|).
% % The function |toWitness : forall {Q} {d : Dec Q} -> IsYes d -> Q| takes a
% % decision |d| for proposition |Q| and proof that it is affirmative, and produces
% % the underlying proof of |Q|.
% % Thus, we read the definition of |Sound G p| as: ``for all input strings |xs|, if
% % parser |p| accepts |xs|, the the prefix it consumes is in |G|.''

% % The proof |soundness| states that \emph{all parsers are sound}.
% % As our parsers are correct-by-construction, the definition is straightforward:
% % we use |toWitness| to extract the proof of parser success, i.e., a term of type
% % |Success G xs|, then use the field accessor |Success.value| to obtain the
% % desired proof that the consumed prefix is in |G|.

% % \textbf{Completeness.}
% % Recall that the definition of parser completeness with respect to a language |G|
% % means that if an input string |xs| is in |G|, the parser accepts \emph{some
% %   prefix of |xs|}.
% % Of course, this property in isolation does not rule out certain bad behavior
% % that threatens security; specifically, it does not constrain the parser's
% % freedom over (1) which prefix of the input is consumed, and (2) how the internal
% % datastructure is constructed.
% % However, and as we have discussed in Section~\ref{sec:s4-lang-spec}, these
% % should be thought of as properties of the \emph{language}, and \emph{not} its
% % parsers.
% % To emphasize this, after discussing the completeness proof we will show how,
% % using language properties, it can be strengthed to address the aforementioned
% % security concerns.

% % \begin{figure}[h]
% % \begin{code}
% % Complete : (G : @0 List A -> Set) -> Parser G -> Set
% % Complete G p = forall xs -> G xs -> IsYes (p xs)

% % trivSuccess : forall {G} {xs} -> G xs -> Success G xs

% % completeness : forall {G} -> (p : Parser G) -> Complete G p
% % completeness p xs inG = fromWitness (p xs) (trivSuccess inG)
% % \end{code}
% %   \caption{Parser completeness (definition and proof)}
% %   \label{fig:s4-parser-wkcompleteness}
% % \end{figure}

% % Figure~\ref{fig:s4-parser-wkcompleteness} shows our definition and proof of
% % \emph{completeness} in \agda, which we now detail.
% % The definition of |Complete| directly translates our notion of completeness: for
% % every input string |xs|, if |xs| is in |G|, then parser |p| accepts some prefix
% % of |xs|.
% % For the proof, we first prove a straightforward lemma |trivSuccess| (definition
% % omitted) that states any proof that |xs| is in |G| can be turned into a proof
% % that some prefix of |xs| (namely, |xs| itself) is in |G|.
% % With this, the proof of |completeness| uses the function |fromWitness : {Q :
% %   Set} -> (d : Dec Q) -> Q -> IsYes d|, which intuitively states that if a
% % proposition |Q| is true, then any decision for |Q| must be in the affirmative.


% % \textbf{Strong completeness.}
% % We will now see how, using language properties, our parser completeness result
% % can be strengthened to rule out bad behavior that could compromises security.
% % To be precise, when a string |xs| is in the language |G|, we desire that the
% % parser consumes \emph{exactly} |xs|, and furthermore that there is only one way
% % for it to construct the internal data representation of |G| from |xs|.
% % To show both of these guarantees, it suffices that |G| satisfies the properties
% % |Unambiguousness| and |NoSubstrings| (see Section~\ref{sec:s4-lang-spec}).

% % \begin{figure}[h]
% %   \begin{code}
% % StronglyComplete : (G : @0 List A -> Set) -> Parser G -> Set
% % StronglyComplete G p = forall xs -> (inG : G xs)
% %   -> exists  (w : IsYes (p xs))
% %              (  let s = toWitness w in
% %                 (xs , inG) == (Success.prefix x , Success.value s))

% % strongCompleteness
% %   : forall {G} -> Unambiguous G -> NoSubstrings G
% %     -> (p : Parser G) -> StronglyComplete G p
% % strongCompleteness ua ns p xs inG = (w , strong xs inG s)
% %   where
% %   w = completeness p inG
% %   s = toWitness w
% %   strong : forall xs inG s -> (_ , inG) == (_ , Success.value s)
% %   strong xs inG s with ns _ inG (Success.prefix s)
% %   ... | refl with ua inG (Success.value s)
% %   ... | refl = refl
% %   \end{code}
% %   \caption{Strong completeness (definition and proof)}
% %   \label{fig:s4-parser-stcompleteness}
% % \end{figure}

% % Figure~\ref{fig:s4-parser-stcompleteness} shows the definition and proof of our
% % strengthened completeness result.
% % For the definition, |StronglyComplete G p| says that, if we have a proof |inG| that
% % |xs| is in |G|, then not only does there exist a witness |w| that the parser
% % accepts some prefix of |xs|, but prefix it consumes is |xs| and the
% % proof it returns is |inG|.
% % Recall that the assumption |inG| and the |value| field of the |Success| record
% % serve dual roles: they are not only proofs that a string is in a language, but
% % also the internal data representation of the value encoded by |xs|.
% % So, saying they are equal means the internal representations are equal.

% % The proof, |strongCompleteness|, shows that to prove |StronglyComplete|, it
% % suffices that the language |G| satisfies |Unambiguous| and |NoSubstrings|.
% % In the definition, we exhibit witness |w| using the previous proof
% % |completeness|, and in the helper proof |strong| we use the assumptions |ns :
% % NoSubstrings G| and |ua : Unambiguous G| to prove that |xs| and |inG| are equal
% % to the |prefix| consumed and |value| returned by |p xs|.

% % \subsection{Semantic Validation}

% % Our approach to semantic validation, as outlined in
% % Section~\ref{sec:s3-insights-on-tech-challenges}, is separating those properties that should
% % be verified for a single certificate and those that concern the entire chain.
% % For each property to validate, we formulate in Agda a predicate expressing
% % satisfaction of the property by a given certificate or chain, then prove that
% % these predicates are decidable (|Dec|, Section~\ref{sec:s4-parsers-cbc}).
% % In what follows, we illustrate with two relatively simple concrete examples: one
% % predicate for a single certificate and one for a certificate chain.

% % Before we illustrate with examples, we stress that the purpose of this setup is
% % \emph{not} to give decidability results for the semantic checks of the \xfon
% % specification, as the mere fact that they are decidable is intuitively obvious.
% % Instead, and just like with our approach to verified parsing, formulating these
% % semantic checks as decidability proofs (1) \emph{forces} us formalize the natural
% % language property we wish to check \emph{independently of the code that performs
% % the checking,} and (2) \emph{enables} us to write the checking code that is
% % \emph{correct-by-construction,} as these decidability proofs are the themselves
% % the functions called after parsing to check whether the certificate or chain
% % satisfies the property.

% % \textbf{Single certificate property.}
% % For a given certificate, it must be the case that its \texttt{SignatureAlgorithm} field
% % contains the same algorithm identifier as the \texttt{Signature} field of
% % its \texttt{TBSCertificate} (R1 in Table~\ref{rules} of the Appendix).
% % As a formula of FOL, we could express this property with respect to
% % certificate \(c\) as
% % \[
% %   \forall s_1\, s_2, \mathit{SignAlg}(s_1,c) \land \mathit{TBSCertSignAlg}(s_2,c)
% %   \implies s_1 = s_2
% % \]
% % where \(\mathit{SignAlg}(s_1,c)\) and \(\mathit{TBSCertSignAlg}(s_2,c)\) express
% % respectively the properties that \(s_1\) is the signature algorithm identifier
% % of \(c\) and that \(s_2\) is the signature algorithm identifier of the
% % \texttt{TBSCertificate} of \(c\).
% % In Agda, we express this property, and the type of its corresponding
% % decidability proof, as follows (we omit the proof for space considerations).

% % \begin{code}
% % R1 : forall {@0 bs} -> Cert bs -> Set
% % R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c

% % r1 : forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
% % r1 c = ...  
% % \end{code}
% % The predicate |R1| expresses that the two signature algorithm
% % fields are equal using the binary relation |==| defined in Agda's standard library.
% % Compared to the proof |r1|, |R1| is relatively simple: |==| is
% % \emph{parametric} in the type of the values it relates (meaning it uses no
% % specifics about the |SignAlg| type family), and is defined as the smallest
% % reflexive relation.
% % In contrast, the checking code |r1| \emph{must} concern itself with the
% % specifics of |SignAlg|.
% % In \xfon, signature algorithm fields are defined as a pair where the first
% % component is an object identifier (OID) and the second is an optional parameters
% % field whose type \emph{depends upon that OID.}
% % So, to implement |r1| we must prove equality is decidable for OIDs
% % \emph{and} for all of the signature algorithm parameter types we support.

% % \textbf{Certificate chain property.}
% % For a certificate chain, it must be the case that a certificate does not appear
% % more than once in a prospective certificate path (R20 in Table~\ref{rules} of the Appendix).
% % As a formula of FOL, we could express this property with respect to a
% % certificate chain \(\mathit{cc}\) as
% % \[
% %   \begin{array}{l}
% %     \forall c_1\, c_2\, i_1\, i_2. \mathit{InChain}(c_1,i_1,\mathit{cc}) \land
% %     \mathit{InChain}(c_2,i_2,\mathit{cc})
% %     \\ \quad \land\ i_1 \neq i_2 \implies c_1 \neq c_2
% %   \end{array}
% % \]
% % where \(\mathit{InChain}(c_1,i_1,\mathit{cc})\) is the property that certificate
% % \(c_1\) is at index \(i_1\) in chain \(\mathit{cc}\).
% % The Agda standard library provides a definition of the property that all entries
% % of a list are distinct from each other, written below as |List.Unique|, as well
% % as a proof that this property is decidable, written |List.unique?|, provided
% % that the type of the list's elements support decidable equality.
% % We express this predicate and its corresponding decidability proof in Agda as
% % % We have proven equality is decidable for certificates, so we can express this
% % % property and corresponding decidability proof in Agda as
% % \begin{code}
% % R20 : forall {@0 bs} -> Chain bs -> Set
% % R20 c = List.Unique (chainToList c)

% % r20 : forall {@0 bs} (c : Chain bs) -> Dec (R20 c)
% % r20 c = List.unique? decCertEq (chainToList c)
% % \end{code}
% % where function |chainToList| converts a certificate chain to a
% % list of certificates and |decCertEq| is the proof that equality is decidable for
% % certificates.
% % Again, there is an asymmetry in the complexities of the specification and proof:
% % while |List.Unique| is defined in 3 lines of code as an inductive type, the proof
% % of |decCertEq| is substantially longer as it requires plumbing through the
% % details of our formalization of |Cert|.
% % By writing our checking function |r20| as a decision procedure, however, we do
% % not have to worry that there is a mistake hidden somewhere in this complexity:
% % by its very type, |r20| is \emph{correct-by-construction} with respect to the
% % specification given by |R20|.
