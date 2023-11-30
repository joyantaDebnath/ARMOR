\section{Verification Goals and Correctness Proofs}

As shown in Figure~\ref{armor}, we provide formal correctness guarantee for the following modules: \emph{parsers (\ie, PEM parser, Base64 decoder, X.690 DER and X.509 parsers)}, \emph{Semantic validator}, \emph{Chain builder}, and \emph{String canonicalizer}. For these verification, we use the \agda interactive theorem prover~\cite{bove2009brief, No07_agda}. In this section, we present a brief introduction to Agda and then describe the design and verified guarantees in detail.

\subsection{Preliminaries on Agda}
\agda is a \textit{dependently-typed} functional programming
language, meaning that types may involve term expressions\todo{\tiny explain}.
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

Consider the example shown in
Figure~\ref{fig:agda-ex} of length-indexed lists, provided as part of the \agda
standard library as |Vec|. 
\begin{figure}[h]
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

\subsection{Verification of Parsers} We conceptually separate each parser verification task into \emph{language
specification}, \emph{language security verification}, and \emph{parser correctness verification}.

\subsubsection{Language specification} \label{sec:s4-lang-spec}
We provide parser-independent formalizations of the PEM, Base64, X.690
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
machine-checked, rigorous alternative for the developers seeking to
understand the relevant specifications. 

More concretely, the relational specifications we give are of the
following form.
For a given language \(G\) with alphabet \(\Sigma\), a family of types
\(\mathit{GSpec}\ \mathit{xs}\) where the family \(\mathit{GSpec}\) is indexed
by strings \(\mathit{xs} \in \Sigma^*\) over the alphabet (for PEM and Base64 the alphabet
is characters, for X.690 and X.509 DER it is unsigned 8-bit integers).
Such a family of types can serve the dual role as the internal representation of
the value encoded by \(\mathit{xs}\), i.e., a value of type \(\mathit{GSpec}\
\mathit{xs}\) is not only a proof that \(\mathit{xs}\) is in the language \(G\),
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
\item \textbf{Minimum representation.} \xsno BER requires that the two's
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
  is the first content octet and |tl| contains the remaining bytes (if any).
  

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

We have proven \emph{unambiguousness} (a given input can encode \emph{at most one value} of a
particular type) for the supported subsets of formats
PEM,
\xsno \der, and \xfon, \emph{non-malleability} (distinct
inputs cannot encode identical values) for the supported
subsets of formats \xsno \der and \xfon, and \emph{no-substrings} (a language permits parsers no degrees
of freedom over which prefix of an input string it consumes) for all
TLV-encoded values.\todo{what is TLV-encoded? DER?}

\textbf{Unambiguous.}
We formally define unambiguousness of a language |G| in Agda as follows.
\begin{code}
Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
\end{code}
Read this definition as saying that for every string |xs|, any two inhabitants
of the internal representation of the value encoded by |xs| in |G| are equal.

\textit{Challenges--} |Unambiguous| expresses a property much stronger
than might be first apparent.
To illustrate, showing |Unambiguous IntegerValue| requires showing that the
corresponding fields are equal --- \emph{even the purely specificaional fields.}
Once established, the additional strength that |Unambiguous| significantly aids
development of the verified parser; however, this means that specifications must
be carefuly crafted so as to admit unique proof terms.
In the case of |IntegerValue|, this means showing that any two proofs of |MinRep
hd tl| are equal. Another challenging aspect in proving unambiguousness for X.690 DER in
particular is the format's support for sequences that have \emph{optional} and
\emph{default} fields, that is, fields that might not be present in the
sequence.
We are threatened with ambiguity if it is possible to mistake an optional field
whose encoding is present for another optional field that is absent.
To avoid this scenario, the X.690 format stipulates that every field of any
``block'' of optional or default fields must be given a tag distinct from every
other such field.
Our proof of unambiguousness for \xfon relies heavily on lemmas proving the
\xfon format obeys this stipulation.

\textbf{Non-malleable.}
Compared to unambiguousness, non-malleability requires more machinery to
express, so we begin by discussing the challenges motivating this machinery.
Since the bytestring encodings are part of \emph{the very types of internal
representations}, e.g., |IntegerValue xs|, it is impossible to express equality
between internal representations |a1 : G xs1| and |a2 : G xs2| without
\emph{already assuming |xs1| is equal to |xs2|}.
Thus, to make non-malleability non-trivial, we must express what is the
``raw'' internal datatype corresponding to |G|, discarding the specificational
components.
We express this general notion in Agda by |Raw|, given below.
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
\noindent This says that the raw representation for integer values is |IntZ| (a
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
The final language property we discuss, which we dub \emph{``no-substrings''}
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
Given that \xfon uses \(<T,L,V>\) encoding, it is
unsurprising that that we are able to prove |NoSubstrings| holds for our
specification.
This property is also an essential lemma to prove \emph{strong
  completeness} of our parser implementation (see Section~\ref{sec:s4-parser-sound-complete-strong}).

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
of its input is. That is to say, parsers are really proofs that membership (in \(G\)) of an
input's prefix is decidable.

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
data Dec (A : Set) : Set where
  yes : A -> Dec A
  no  : not A -> Dec A
\end{code}
Reading |Dec| as programmers, |Dec A| is a tagged union type which can be
populated using either values of type |A| or type |not A|; as mathematicians, we
read it as the type of proofs that |A| is \emph{decidable}.
Expressed as a formula of FOL, |Dec A| is simply \(A \lor \neg A\); however,
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

\textit{Challenges--}
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

\noindent\textbf{Correctness properties:}
\label{sec:s4-parser-sound-complete-strong}
We now show our formal definitions and proofs of soundness and completeness for
parsing, beginning with soundness.
\begin{figure}[h]
  \begin{code}
Sound : (G : @0 List A -> Set) -> Parser G -> Set
Sound G p =
  forall xs -> (w : IsYes (p xs)) -> G (Success.prefix (toWitness w))    

@0 soundness : forall {G} -> (p : Parser G) -> Sound G p
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
  strong : forall xs inG s -> (_ , inG) == (_ , Success.value s)
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


\subsection{Verification of Chain Builder}

\subsection{Verification of String Canonicalizer}


\subsection{Verification of Semantic Validator}
Our approach to semantic validation, as outlined in
Section~\ref{sec:s3-insights-on-tech-challenges}, is separating those properties that should
be verified for a single certificate and those that concern the entire chain.
For each property to validate, we formulate in Agda a predicate expressing
satisfaction of the property by a given certificate or chain, then prove that
these predicates are decidable (|Dec|, Section~\ref{sec:s4-parsers-cbc}).
In what follows, we illustrate with two relatively simple concrete examples: one
predicate for a single certificate and one for a certificate chain.

Before we illustrate with examples, we stress that the purpose of this setup is
\emph{not} to give decidability results for the semantic checks of the \xfon
specification, as the mere fact that they are decidable is intuitively obvious.
Instead, and just like with our approach to verified parsing, formulating these
semantic checks as decidability proofs (1) \emph{forces} us formalize the natural
language property we wish to check \emph{independently of the code that performs
the checking,} and (2) \emph{enables} us to write the checking code that is
\emph{correct-by-construction}, as these decidability proofs are the themselves
the functions called after parsing to check whether the certificate or chain
satisfies the property.

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
In Agda, we express this property, and the type of its corresponding
decidability proof, as follows (we omit the proof for space considerations).

\begin{code}
R1 : forall {@0 bs} -> Cert bs -> Set
R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c

r1 : forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
r1 c = ...  
\end{code}
The predicate |R1| expresses that the two signature algorithm
fields are equal using the binary relation |==| defined in Agda's standard library.
Compared to the proof |r1|, |R1| is relatively simple: |==| is
\emph{parametric} in the type of the values it relates (meaning it uses no
specifics about the |SignAlg| type family), and is defined as the smallest
reflexive relation.
In contrast, the checking code |r1| \emph{must} concern itself with the
specifics of |SignAlg|.
In \xfon, signature algorithm fields are defined as a pair where the first
component is an object identifier (OID) and the second is an optional parameters
field whose type \emph{depends upon that OID.}
So, to implement |r1| we must prove equality is decidable for OIDs
\emph{and} for all of the signature algorithm parameter types we support.

\textbf{Certificate chain property.}
For a certificate chain, it must be the case that a certificate does not appear
more than once in a prospective certificate path (R20 in Table~\ref{rules} of the Appendix).
As a formula of FOL, we could express this property with respect to a
certificate chain \(\mathit{cc}\) as
\[
  \begin{array}{l}
    \forall c_1\, c_2\, i_1\, i_2. \mathit{InChain}(c_1,i_1,\mathit{cc}) \land
    \mathit{InChain}(c_2,i_2,\mathit{cc})
    \\ \quad \land\ i_1 \neq i_2 \implies c_1 \neq c_2
  \end{array}
\]
where \(\mathit{InChain}(c_1,i_1,\mathit{cc})\) is the property that certificate
\(c_1\) is at index \(i_1\) in chain \(\mathit{cc}\).
The Agda standard library provides a definition of the property that all entries
of a list are distinct from each other, written below as |List.Unique|, as well
as a proof that this property is decidable, written |List.unique?|, provided
that the type of the list's elements support decidable equality.
We express this predicate and its corresponding decidability proof in Agda as
% We have proven equality is decidable for certificates, so we can express this
% property and corresponding decidability proof in Agda as
\begin{code}
R20 : forall {@0 bs} -> Chain bs -> Set
R20 c = List.Unique (chainToList c)

r20 : forall {@0 bs} (c : Chain bs) -> Dec (R20 c)
r20 c = List.unique? decCertEq (chainToList c)
\end{code}
where function |chainToList| converts a certificate chain to a
list of certificates and |decCertEq| is the proof that equality is decidable for
certificates.
Again, there is an asymmetry in the complexities of the specification and proof:
while |List.Unique| is defined in 3 lines of code as an inductive type, the proof
of |decCertEq| is substantially longer as it requires plumbing through the
details of our formalization of |Cert|.
By writing our checking function |r20| as a decision procedure, however, we do
not have to worry that there is a mistake hidden somewhere in this complexity:
by its very type, |r20| is \emph{correct-by-construction} with respect to the
specification given by |R20|.



\begin{table*}[h]
  % \captionsetup{font=footnotesize}
  \centering
  \sffamily\scriptsize
      \setlength\extrarowheight{1.5pt}
      \setlength{\tabcolsep}{1.5pt}
      \caption{Summary of correctness guarantees for each module}
      \sffamily\scriptsize
      \label{sum-ver}
  \centering
  \begin{tabular}{l||c||c||c||c||c||c||}
  \cline{2-7}
  \textbf{}                                                                                                        & \textbf{\begin{tabular}[c]{@@{}c@@{}}PEM \\ Parser\end{tabular}}                                                & \textbf{\begin{tabular}[c]{@@{}c@@{}}Base64 \\ Decoder\end{tabular}}                                             & \textbf{\begin{tabular}[c]{@@{}c@@{}}X.690 DER and\\ X.509 Parsers\end{tabular}}                   & 
  \textbf{\begin{tabular}[c]{@@{}c@@{}}Chain \\ Builder\end{tabular}} & 
  \textbf{\begin{tabular}[c]{@@{}c@@{}}String \\ Canonicalizer\end{tabular}} & 
  \textbf{\begin{tabular}[c]{@@{}c@@{}}Semantic\\ Validator\end{tabular}} \\ \hline
  \multicolumn{1}{||l||}{\textbf{\begin{tabular}[c]{@@{}l@@{}}Implementation\\ Correctness\\ Properties\end{tabular}}} & \begin{tabular}[c]{@@{}c@@{}}Soundness-by-construction\\ Completeness-by-construction\\ Maximality\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Soundness-by-construction\\ Completeness-by-construction\\ Isomorphism\end{tabular} & \begin{tabular}[c]{@@{}c@@{}}Soundness-by-construction\\ Completeness-by-construction\end{tabular} &                                                                   &                                                                          & Correct-by-construction                                               \\ \hline
  \multicolumn{1}{||l||}{\textbf{\begin{tabular}[c]{@@{}l@@{}}Language\\ Security\\ Properties\end{tabular}}}          & Unambiguousness                                                                                               &                                                                                                                & \begin{tabular}[c]{@@{}c@@{}}Unambiguousness\\ Non-malleability\\ No-substrings\end{tabular}       &                                                                   &                                                                          & N/A                                                                   \\ \hline
  \end{tabular}
  \end{table*}



% This section details the design and verified guarantees of our parser and
% semantic checker modules.
% \begin{itemize}
% \item We start with an overview of our specifications of the supported subsets
%   of the PEM, X.690 DER, and X.509 formats, emphasizing how their being
%   \emph{parser independent} facilitates verifying language properties without
%   mentioning implementation details.
  
% \item Next, we describe our parsers, which are designed to be \emph{correct by
%     construction} with respect to the language specifications.
%   We achieve this by having parsers return \emph{proofs} either affirming or
%   refuting language membership.
  
% \item Finally, we describe approach to \emph{correct-by-construction} semantic
%   validation.
%   We express the desired properties of semantic checking as predicates over the
%   internal data representations, with the code executing these checks
%   implemented as proofs that these properties are decidable.
% \end{itemize}

% % \subsubsection*{Input Strings}
% % Inputs to our parser have types of the form |List A|, where |A| is the type of
% % the language alphabet.
% % For our PEM parser, this is |Char|, Agda's primitive type for character
% % literals.
% % For our X.690 and X.509 parsers, this is the type |UInt8|, which is an alias for
% % the Agda standard library type |Fin 256| (the type for nonnegative integers
% % strictly less than 256).
% % \subsubsection*{Base64 Decoding}
% % We hand off the result of the PEM parser, which extracts the Base64 encoding of the
% % certificates, to the X.509 parser, which expects an octet string, through a
% % Base64 decoder that is verified with respect to an encoder.
% % Specifically, we prove: 1) that the encoder always produces a valid sextet
% % string (Base64 binary string); and 2) the encoder and decoder pair forms an
% % isomorphism between octet strings and valid sextet strings for encoding them.
% % This is summarized below in Figure~\ref{fig:s4-base64} (for space
% % considerations, all definitions have been omitted).

% % \begin{figure}[h]
% %   \begin{code}
% % ValidEncoding : List UInt6 -> Set
% % encode : List UInt8 -> List UInt6
% % decode : (bs : List UInt6) -> Valid64Encoding bs -> List UInt8

% % encodeValid : (bs : List UInt8) -> ValidEncoding (encode bs)

% % encodeDecode :  forall bs -> decode (encode bs) (encodeValid bs) == bs
% % decodeEncode :  forall bs -> (v : ValidEncoding bs)
% %                 -> encode (decode bs v) == bs
% %   \end{code}
% %   \caption{Base64 encoding and decoding (types only)}
% %   \label{fig:s4-base64}
% % \end{figure}


% \subsection{Independent Specification}
% \label{sec:s4-lang-spec}
% Our first challenge concerns how the specification is represented, that is,
% answering the question ``parser soundness and completeness \emph{with respect to
%   what?}''
% Our answer is that for each production rule |G| of the supported subset of the
% PEM, X.690, and X.509 grammars, we define a predicate |G : List A -> Set| over
% the input strings.
% Membership of an input string |xs| in the language denoted by |G| corresponds to
% the inhabitation of the type |G xs|.

% \begin{figure}[h]
%   \begin{code}
% MinRep : UInt8 -> List UInt8 -> Set
% MinRep b1 [] = Top
% MinRep b1 (b2 :: bs) =
%   (b1 > 0 Lor (b1 == 0 Land b2 >= 128))
%   Land (b1 < 255 Lor (b1 == 255 Land b2 <=127))
    
% record IntegerValue (@0 bs : List UInt8) : Set where
%   constructor mkIntVal
%   field
%     @0 hd : UInt8
%     @0 tl : List UInt8
%     @0 minRep : MinRep hd tl
%     val : IntZ
%     @0 valeq : val == Base256.twosComp bs
%     @0 bseq : bs == hd :: tl
%   \end{code}
%   \caption{Specification of integer values}
%   \label{fig:s4-integervalue}
% \end{figure}

% We illustrate our approach with a concrete example: our specification of X.690
% DER integer values, shown in Figure~\ref{fig:s4-integervalue}.
% This specification takes the form of an Agda record (roughly analogous to a
% C-style \texttt{struct}) that is parameterized by a bytestring |bs|.
% \begin{itemize}
% \item \textbf{Minimum representation.} \xsno BER requires that the two's
%   complement encoding of an integer value consists of the minimum number of
%   octets needed for this purpose.
%   We \emph{express} this property with |MinRep|, which defines a relation between the
%   first byte of the encoding and the remaining bytes; we \emph{enforce} that the
%   property holds with field |minRep| of |IntegerValue| (in order to construct an
%   expression of type |IntegerValue bs|, we must prove that |MinRep| holds for
%   the head and tail of |bs|).
  
%   The definition of |MinRep| proceeds by cases on whether or not the remaining
%   byte string is empty.
%   \begin{enumerate}
%   \item If it is, we return the trivially true proposition |Top|, because a
%     single byte is always minimal.
    
%   \item Otherwise, if the bits of the first byte are all 0, the first bit of the
%     second byte must be 1 (i.e., |b2 >= 128|); and if the bits of the first byte
%     are all 1 (i.e., |b1 == 255|), then the first bit of the second byte must be
%     0 (i.e., |b2 <= 127|).
%   \end{enumerate}
  
% \item \textbf{Erasure annotations.} The string |@0| is an annotation that marks
%   the accompanying identifier as \emph{erased at runtime}.
%   In the figure, only the field |val| (the integer encoded by |bs|) is present
%   at runtime, with the remaining fields (and the parameter |bs|) erased by
%   Agda's GHC backend.
%   The annotations for runtime erasure not only improves the performance of ARMOR,
%   but also serve to document, for programmers using ARMOR as a reference
%   implementation, which components of the internal representation serve only
%   specificational purposes.

% \item \textbf{Nonempty encoding.} Fields |hd|, |tl|, and |bseq| together ensure
%   that the encoding of an integer value ``consists of one or more
%   octets.''~\cite{rec2002x}
%   Specifically, |bseq| ensures that |bs| is of the form |hd :: tl|, where |hd|
%   is the first content octet and |tl| contains the remaining bytes (if any).
  

% \item \textbf{Linking the value and its encoding.}
%   Field |valeq| forecloses any possibility that an expression of type |IntegerValue
%   bs| populates the field |val| with an arbitrary integer by requiring that this
%   field \emph{must} be equal to the result of decoding |bs| as a two's complement
%   binary value, where |Base256.twosComp| is the decoding operation.
% \end{itemize}

% A major advantage of our approach to specifying X.509 is that it facilitates
% proving properties \emph{about the grammar} without having to reason about
% parser implementation details.
% By verifying properties of grammar itself, we can be more confident that we have
% accurately captured the meaning of the natural language descriptions. 
% Two properties in particular that we have proven hold of our specification
% capture the major design goal of X.690 DER formats: they are \emph{unambiguous},
% meaning that a given bytestring can encode \emph{at most one value} of a
% particular type; and they are \emph{non-malleable}, meaning that distinct
% bytestrings cannot encode identical values.

% \subsubsection{Unambiguous}
% We formally define unambiguousness of a language |G| in Agda as follows.
% \begin{code}
% Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
% \end{code}
% Read this definition as saying that for every string |xs|, any two inhabitants
% of the internal representation of the value encoded by |xs| in |G| are equal.

% \textbf{Challenges.} |Unambiguous| expresses a property much stronger
% than might be first apparent.
% To illustrate, showing |Unambiguous IntegerValue| requires showing that the
% corresponding fields are equal --- \emph{even the purely specificaional fields.}
% Once established, the additional strength that |Unambiguous| significantly aids
% development of the verified parser; however, this means that specifications must
% be carefuly crafted so as to admit unique proof terms.
% In the case of |IntegerValue|, this means showing that any two proofs of |MinRep
% hd tl| are equal.

% Another challenging aspect in proving unambiguousness for X.690 DER in
% particular is the format's support for sequences that have \emph{optional} and
% \emph{default} fields, that is, fields that might not be present in the
% sequence.
% We are threatened with ambiguity if it is possible to mistake an optional field
% whose encoding is present for another optional field that is absent.
% To avoid this scenario, the X.690 format stipulates that every field of any
% ``block'' of optional or default fields must be given a tag distinct from every
% other such field.
% Our proof of unambiguousness for \xfon relies heavily on lemmas proving the
% \xfon format obeys this stipulation.

% \subsubsection{Non-malleable}
% Compared to unambiguousness, non-malleability requires more machinery to
% express, so we begin by discussing the challenges motivating this machinery.
% Since the bytestring encodings are part of \emph{the very types of internal
% representations}, e.g., |IntegerValue xs|, it is impossible to express equality
% between internal representations |a1 : G xs1| and |a2 : G xs2| without
% \emph{already assuming |xs1| is equal to |xs2|}.
% Thus, to make non-malleability non-trivial, we must express what is the
% ``raw'' internal datatype corresponding to |G|, discarding the specificational
% components.
% We express this general notion in Agda by |Raw|, given below.
% \begin{code}
% record Raw (G : List A -> Set) : Set where
%   field
%     D : Set
%     to : {@0 xs : List A} -> G xs -> D
% \end{code}

% An inhabitant of |Raw G| consists of a type |D|, intended to be the
% ``raw data'' of |G|, together with a function |to| that should extract this data
% from any inhabitant of |G xs|.
% To illustrate, consider the case for |IntegerValue| below.
% \begin{code}
%   RawIntegerValue : Raw IntegerValue
%   Raw.D RawIntegerValue = IntZ
%   Raw.to RawIntegerValue = IntegerValue.val
% \end{code}
% \noindent This says that the raw representation for integer values is |IntZ| (a
% type for integers defined in Agda's standard library), and the extraction
% function is just the field accessor |IntegerValue.val|.

% Once we have defined an instance of |Raw G| for a language specification |G|,
% we express non-malleability of |G| with respect to that raw representation
% with the following property: give two input strings |xs1| and |xs2|, with witnesses
% |g1 : G xs1| and |g2 : G xs2|, if the raw representations of |g1| and |g2| are
% equal, then not only are strings |xs1| and |xs2| equal, but also |g1| and |g2|.
% In Agda, this is written as:
% \begin{code}
% NonMalleable : {G : @0 List A -> Set} -> Raw G -> Set
% NonMalleable{G} R =
%   forall {@0 xs1 xs2} -> (g1 : G xs1) (g2 : G xs2)
%   -> Raw.to R g1 == Raw.to R g2 -> (xs1 , g1) ==  (xs2 , g2)  
% \end{code}
% For |IntegerValue| in particular, proving |NonMalleable RawIntegerValue|
% requires showing |Base256.twosComp| is itself injective.

% \subsubsection{No Substrings}
% The final language property we discuss, which we dub \emph{``no substrings,''}
% expresses formally the intuitive idea that a language permits parsers no degrees
% of freedom over which prefix of an input string it consumes.
% As we are striving for \emph{parser independence} in our language
% specifications, we formulate this property as follows: for any two prefixes of
% an input string, if both prefixes are in the language |G|, then they are equal.
% In Agda, we express this as |NoSubstrings| below.
% \begin{code}
% NoSubstrings G =
%   forall {xs1 ys1 xs2 ys2} -> xs1 ++ ys1 == xs2 ++ ys2
%   -> G xs1 -> G xs2 -> xs1 == xs2
% \end{code}
% Given that \xfon uses \(<T,L,V>\) encoding, it is
% unsurprising that that we are able to prove |NoSubstrings| holds for our
% specification.
% However, this property is essential to understanding our \emph{strong
%   completeness} result (see Section~\ref{sec:s4-parser-sound-complete-strong})
% for parsing.

% \subsubsection{Summary of Language Guarantees}
% We have proven \emph{unambiguousness} for the supported subsets of formats
% PEM,\todo{\tiny Remove if we haven't}
% \xsno \der, and \xfon; we have proven \emph{non-malleability} for the supported
% subsets of formats \xsno \der and \xfon, and proven \emph{no substrings} for all
% TLV-encoded values.

% % In addition, two properties in particular are essential to our proof of parser
% % completeness.
% % \begin{itemize}
% % \item \textbf{Unambiguous:} at most one prefix of a bytestring can belong to
% %   |G|.
% %   That means, \(\forall \mathit{ws}\, \mathit{xs}\, \mathit{ys}\, \mathit{zs},
% %   \mathit{ws} +\!\!\!+ \mathit{xs} = \mathit{ys} +\!\!\!+ \mathit{zs} \land
% %   |G ws| \land |G ys| \implies \mathit{ws} = \mathit{ys}\).
  
% % \item \textbf{Uniqueness:} the internal representation of |G xs| is uniquely
% %   determined by |xs|.
% %   That means (using \(\mathit{Rep}_{|G|}(x,\mathit{xs})\) to express ``\(x\) is the
% %   internal representation of |G xs|''),
% %   \(\forall x\, y\, \mathit{xs}, \mathit{Rep}_{|G|}(x,\mathit{xs}) \land
% %   \mathit{Rep}_{|G|}(y,\mathit{xs}) \implies x = y\).
% % \end{itemize}
% % \noindent Both of these properties have been proven for our specification of
% % X.509 certificates.
% % In Agda, predicates |Unambiguous| and |Unique| are defined as follow.
% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %     Unambiguous : (List UInt8 -> Set) -> Set
% %     Unambiguous G =  forall {ws xs ys zs} -> ws ++ xs == ys ++ zs
% %                      -> G ws -> G ys -> ws == ys
% %     Unique : (List UInt8 -> Set) -> Set
% %     Unique G = forall {xs} -> (g h : G xs) -> g == h
% %   \end{code}
% %   \caption{Definition of unambiguousness and uniqueness}
% %   \label{fig:unambig-uniq}
% % \end{figure}

% \subsection{Sound and Complete Parsing}
% We now describe our approach to verified parsing.
% Recall that, for a language \(G\), \emph{soundness} of a parser means that every
% bytestring it accepts is in the language, and \emph{completeness} means that it
% accepts every bytestring in the language.
% Our approach to verifying these properties for all our parsers is to make them
% \emph{correct-by-construction}, meaning that parsers do not merely indicate
% success or failure with e.g.\ an integer code, but return \emph{proofs}. 
% If the parser is successful, this is a proof that some prefix of its input is in
% the language, and if the parser fails, it returns a proof that \emph{no} prefix
% of its input is.

% \subsubsection{The Type of Correct-by-Construction Parsers}
% \label{sec:s4-parsers-cbc}
% Our first step is to formally define what success in means.
% In FOL, we would express the condition for the parser's success on a prefix of
% |xs| as \(\exists \mathit{ys}\, \mathit{zs}, \mathit{xs} = \mathit{ys} +\!\!\!+
% \mathit{zs} \land |G ys|\).
% That is to say, on success the parser consumes some prefix of the input string
% that is in the language |G|.
% In Agda, we express the result of successful parsing as the parameterized record
% |Success|, shown below.
% \begin{figure}[h]
%   \centering
%   \begin{code}
%     record Success 
%       (G : List UInt8 -> Set) (xs : List UInt8) : Set where
%       constructor success
%       field
%         @0 prefix : List UInt8
%         suffix : List UInt8
%         @0 pseq : prefix ++ suffix == xs
%         value : G prefix
%   \end{code}
%   \caption{Success conditions for parsing}
%   \label{fig:parser-success}
% \end{figure}
% In the definition, understand parameters |G| and |xs| as the language denoted by
% a production rule and an input string, respectively.
% The fields of the record are: |prefix|, the consumed prefix of the input (erased
% at runtime); |suffix|, the remaining suffix of the input from which we parse
% subsequent productions; |pseq|, which relates |prefix| and |suffix| to the input
% string |xs| (also runtime erased); and |value|, which serves dual roles as both
% the internal data representation of the value encoded by |prefix| \textbf{and}
% a proof that |prefix| is in the language |G|.  
% As a consequence, \emph{soundness will be immediate}.

% Our next step is to define what parser failure means.
% We define this to be the condition that \emph{no} prefix of the input |xs| is in
% the language of |G|, which is to say the failure condition is the
% \emph{negation} of the success condition: |not Success G xs|.

% To have the parser return |Success G xs| on success and |not Success G xs| on
% failure, we use datatype |Dec| in the Agda standard library, shown below.
% \begin{code}
% data Dec (A : Set) : Set where
%   yes : A -> Dec A
%   no  : not A -> Dec A
% \end{code}
% Reading |Dec| as programmers, |Dec A| is a tagged union type which can be
% populated using either values of type |A| or type |not A|; as mathematicians, we
% read it as the type of proofs that |A| is \emph{decidable}.
% Expressed as a formula of FOL, |Dec A| is simply \(A \lor \neg A\); however,
% note that constructive logic (upon which Agda is based) does not admit LEM, so
% this disjunction must be proven on a case-by-case basis for each |A| in
% question, as there are some propositions which can neither be proven nor refuted.

% We are now able to complete the definition of the type of parsers, shown below.
% \begin{figure}[h]
%   \begin{code}
% Parser : (List UInt8 -> Set) -> Set
% Parser G = forall xs -> Dec (Success G xs)    
%   \end{code}
%   \caption{Definition of |Parser|}
%   \label{fig:parser-def}
% \end{figure}%
% |Parser| is a family of types, where for each language |G|, the type
% |Parser G| is the proposition that, for all bytestrings |xs|, it is decidable
% whether some prefix of |xs| is in |G|; alternatively, we can (as programmers)
% read it as the type of functions which take a bytestring and possibly return a
% parsed data structure and remaining bytestring to continue parsing.

% \textbf{Challenges.}
% The guarantee that, on failure, the parser returns |not Success G xs| is very
% strong, as it asserts a property concerning \emph{all possible prefixes} of the
% input.
% This strength is double-edged: while having this guarantee makes proving
% completeness straightforward, \emph{proving} it means ruling out all possible
% ways in which the input could be parsed.
% In some cases, we have made choices about parser implementations to facilitate
% the proofs concerning the failure case, at a cost to performance.
% The clearest example of such a trade-off is in our parsers for X.690
% \texttt{Choice} values, which are implemented using back-tracking.

% \subsubsection{Parser Soundness, Completeness, and Strong Completeness}
% \label{sec:s4-parser-sound-complete-strong}
% We now show our formal definitions and proofs of soundness and completeness for
% parsing, beginning with soundness.
% \begin{figure}[h]
%   \begin{code}
% Sound : (G : @0 List A -> Set) -> Parser G -> Set
% Sound G p =
%   forall xs -> (w : IsYes (p xs)) -> G (Success.prefix (toWitness w))    

% @0 soundness : forall {G} -> (p : Parser G) -> Sound G p
% soundness p xs w = Success.value (toWitness w)
%   \end{code}
%   \caption{Parser soundness (definition and proof)}
%   \label{fig:s4-parser-soundness}
% \end{figure}%

% \textbf{Soundness.}
% Recall that parser soundness means that, if a parser for \(G\) accepts a prefix of the
% input string, then that prefix is in \(G\).
% The Agda definition and proof of soundness for all of our parsers is
% shown in Figure~\ref{fig:s4-parser-soundness}, which we now detail.
% Beginning with |Sound|, the predicate expressing that parser |p| is sound with
% respect to language |G|, the predicate |IsYes| (definition omitted) expresses
% the property that a given decision (in this case, one of type |Dec (Success G
% xs)|) is affirmative (i.e., constructed using |yes|).
% The function |toWitness : forall {Q} {d : Dec Q} -> IsYes d -> Q| takes a
% decision |d| for proposition |Q| and proof that it is affirmative, and produces
% the underlying proof of |Q|.
% Thus, we read the definition of |Sound G p| as: ``for all input strings |xs|, if
% parser |p| accepts |xs|, the the prefix it consumes is in |G|.''

% The proof |soundness| states that \emph{all parsers are sound}.
% As our parsers are correct-by-construction, the definition is straightforward:
% we use |toWitness| to extract the proof of parser success, i.e., a term of type
% |Success G xs|, then use the field accessor |Success.value| to obtain the
% desired proof that the consumed prefix is in |G|.

% \textbf{Completeness.}
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

% \begin{figure}[h]
% \begin{code}
% Complete : (G : @0 List A -> Set) -> Parser G -> Set
% Complete G p = forall xs -> G xs -> IsYes (p xs)

% trivSuccess : forall {G} {xs} -> G xs -> Success G xs

% completeness : forall {G} -> (p : Parser G) -> Complete G p
% completeness p xs inG = fromWitness (p xs) (trivSuccess inG)
% \end{code}
%   \caption{Parser completeness (definition and proof)}
%   \label{fig:s4-parser-wkcompleteness}
% \end{figure}

% Figure~\ref{fig:s4-parser-wkcompleteness} shows our definition and proof of
% \emph{completeness} in \agda, which we now detail.
% The definition of |Complete| directly translates our notion of completeness: for
% every input string |xs|, if |xs| is in |G|, then parser |p| accepts some prefix
% of |xs|.
% For the proof, we first prove a straightforward lemma |trivSuccess| (definition
% omitted) that states any proof that |xs| is in |G| can be turned into a proof
% that some prefix of |xs| (namely, |xs| itself) is in |G|.
% With this, the proof of |completeness| uses the function |fromWitness : {Q :
%   Set} -> (d : Dec Q) -> Q -> IsYes d|, which intuitively states that if a
% proposition |Q| is true, then any decision for |Q| must be in the affirmative.


% \textbf{Strong completeness.}
% We will now see how, using language properties, our parser completeness result
% can be strengthened to rule out bad behavior that could compromises security.
% To be precise, when a string |xs| is in the language |G|, we desire that the
% parser consumes \emph{exactly} |xs|, and furthermore that there is only one way
% for it to construct the internal data representation of |G| from |xs|.
% To show both of these guarantees, it suffices that |G| satisfies the properties
% |Unambiguousness| and |NoSubstrings| (see Section~\ref{sec:s4-lang-spec}).

% \begin{figure}[h]
%   \begin{code}
% StronglyComplete : (G : @0 List A -> Set) -> Parser G -> Set
% StronglyComplete G p = forall xs -> (inG : G xs)
%   -> exists  (w : IsYes (p xs))
%              (  let s = toWitness w in
%                 (xs , inG) == (Success.prefix x , Success.value s))

% strongCompleteness
%   : forall {G} -> Unambiguous G -> NoSubstrings G
%     -> (p : Parser G) -> StronglyComplete G p
% strongCompleteness ua ns p xs inG = (w , strong xs inG s)
%   where
%   w = completeness p inG
%   s = toWitness w
%   strong : forall xs inG s -> (_ , inG) == (_ , Success.value s)
%   strong xs inG s with ns _ inG (Success.prefix s)
%   ... | refl with ua inG (Success.value s)
%   ... | refl = refl
%   \end{code}
%   \caption{Strong completeness (definition and proof)}
%   \label{fig:s4-parser-stcompleteness}
% \end{figure}

% Figure~\ref{fig:s4-parser-stcompleteness} shows the definition and proof of our
% strengthened completeness result.
% For the definition, |StronglyComplete G p| says that, if we have a proof |inG| that
% |xs| is in |G|, then not only does there exist a witness |w| that the parser
% accepts some prefix of |xs|, but prefix it consumes is |xs| and the
% proof it returns is |inG|.
% Recall that the assumption |inG| and the |value| field of the |Success| record
% serve dual roles: they are not only proofs that a string is in a language, but
% also the internal data representation of the value encoded by |xs|.
% So, saying they are equal means the internal representations are equal.

% The proof, |strongCompleteness|, shows that to prove |StronglyComplete|, it
% suffices that the language |G| satisfies |Unambiguous| and |NoSubstrings|.
% In the definition, we exhibit witness |w| using the previous proof
% |completeness|, and in the helper proof |strong| we use the assumptions |ns :
% NoSubstrings G| and |ua : Unambiguous G| to prove that |xs| and |inG| are equal
% to the |prefix| consumed and |value| returned by |p xs|.

% \subsection{Semantic Validation}

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
% \emph{correct-by-construction,} as these decidability proofs are the themselves
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
