\section{Verification and Correctness Proofs}
This section details the design and verified guarantees of our parser and
semantic checker modules (Figure~\ref{cert_validation}).
\begin{itemize}
\item We start with an overview of our specifications of the supported subsets
  of the PEM, X.690 DER, and X.509 formats, emphasizing how their being
  \emph{parser independent} facilitates verifying language properties without
  mentioning implementation details.
  
\item Next, we describe our parsers, which are designed to be \emph{correct by
    construction} with respect to the language specifications.
  We achieve this by having parsers return \emph{proofs} either affirming or
  refuting language membership.
  
\item Finally, we describe approach to \emph{correct by construction} semantic
  validation.
  We express the desired properties of semantic checking as predicates over the
  internal data representations, with the code executing these checks
  implemented as proofs that these properties are decidable.
\end{itemize}

\subsubsection*{Input Strings}
Inputs to our parser have types of the form |List A|, where |A| is the type of
the language alphabet.
For our PEM parser, this is |Char|, Agda's primitive type for character
literals.
For our X.690 and X.509 parsers, this is the type |UInt8|, which is an alias for
the Agda standard library type |Fin 256| (the type for nonnegative integers
strictly less than 256).
\subsubsection*{Base64 Decoding}
We hand-off the result of the PEM parser, which extracts the Base64 encoding of the
certificates, to the X.509 parser, which expects an octet string, through a
Base64 decoder that is verified with respect to an encoder.
Specifically, we prove: 1) that the encoder always produces a valid sextet
string (Base64 binary string); and 2) the encoder and decoder pair forms an
isomorphism between octet strings and valid sextet strings.\todo{\tiny Would
be nice to show the type signatures here, but they need cleaning up!}


\subsection{Independent Specification}
\label{sec:s4-lang-spec}
Our first challenge concerns how the specification is represented, that is,
answering the question ``parser soundness and completeness \emph{with respect to
  what?}''
Our answer is that for each production rule |G| of the supported subset of the
PEM, X.690, and X.509 grammars, we define a predicate |G : List A -> Set| over
the input strings.
Membership of an input string |xs| in the language denoted by |G| corresponds to
the inhabitation of the type |G xs|.

\begin{figure}[h]
  \begin{code}
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
The types of the fields of this record specify \emph{what it means} for |bs| to
be a valid encoding of an integer value, \emph{and} give integer value |bs| encodes.
\begin{itemize}
\item \textbf{Erasure annotations.} The string |@0| marks the
  accompanying identifier as \emph{erased at runtime}.
  In the figure, only the field |val| (the integer encoded by |bs|) is present
  at runtime, with the remaining fields erase by Agda's GHC backend.
  The annotations for runtime erasure not only improve the performance of ARMOR,
  but also serve to document, for programmers using ARMOR as a reference
  implementation, which components of the internal representation serve only
  specificational purposes.

\item \textbf{Nonempty encoding.} Fields |hd|, |tl|, and |bseq| together ensure
  that the encoding of an integer value ``consists of one or more
  octets.\todo{cite}''
  Specifically, |bseq| ensures that |bs| is of the form |hd :: tl|, where |hd|
  is the first content octet and |tl| contains the remaining bytes (if any).
  
\item \textbf{Minimum representation.} X.690 BER requires that the two's
  complement encoding of an integer value consists of the minimum number of
  octets needed for this purpose.
  This is enforced by the field |minRep| (we shall see the definition of the
  relation |MinRep| shortly).\todo{\tiny Show it or drop this.}

\item \textbf{Linking the value and its encoding.}
  Field |valeq| forecloses any possibility that an inhabitant of |IntegerValue
  bs| populates field |val| with an arbitrary integer by requiring that it
  \emph{must} be equal to the result of decoding |bs| as a two's complement
  binary value, where |Base256.twosComp| is the decoding operation.
\end{itemize}

A major advantage of our approach to specifying X.509 is that it facilitates
proving properties \emph{about the grammar} without having to reason about
parser implementation details.
By verifying properties of grammar itself, we can be more confident that we have
accurately captured the meaning of the natural language descriptions. 
Two properties in particular that we have proven hold of our specification
capture the major design goal of X.690 DER formats: they are \emph{unambiguous},
meaning that a given bytestring can encode \emph{at most one value} of a
particular type; and they are \emph{non-malleable}, meaning that distinct
bytestrings cannot encode identical values.

\subsubsection{Unambiguous}
We formally define unambiguousness of a language |G| in Agda as follows.
\begin{code}
Unambiguous G = forall {xs} -> (a1 a2 : G xs) -> a1 == a2
\end{code}
Read this definition as saying that for every string |xs|, any two inhabitants
of the internal representation of the value encoded by |xs| in |G| are equal.

\textbf{Challenges.} |Unambiguous| expresses a property much stronger
than might be first apparent.
To illustrate, showing |Unambiguous IntegerValue| requires showing that the
corresponding fields are equal --- \emph{even the purely specificaional fields.}
Once established, the additional strength that |Unambiguous| significantly aids
development of the verified parser; however, this means that specifications must
be carefuly crafted so as to admit unique proof terms.

Another challenging aspect in proving unambiguousness for X.690 DER in
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

\subsubsection{Non-malleable}
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

\textbf{Challenges.}\todo{\tiny Sig alg explicit null parameters}

\subsubsection{No Substrings}
The final language property we discuss, which we dub \emph{``no substrings,''}
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
However, this property is essential to understanding our \emph{strong
  completeness} result\todo{\tiny Forward ref} for parsing.

\subsubsection{Summary of Language Guarantees}
We have proven \emph{unambiguousness} for the supported subsets of formats
PEM,\todo{\tiny Remove if we haven't}
\xsno \der, and \xfon; we have proven \emph{non-malleability} for the supported
subsets of formats \xsno \der and \xfon, and proven \emph{no substrings} for all
TLV-encoded values.

% In addition, two properties in particular are essential to our proof of parser
% completeness.
% \begin{itemize}
% \item \textbf{Unambiguous:} at most one prefix of a bytestring can belong to
%   |G|.
%   That means, \(\forall \mathit{ws}\, \mathit{xs}\, \mathit{ys}\, \mathit{zs},
%   \mathit{ws} +\!\!\!+ \mathit{xs} = \mathit{ys} +\!\!\!+ \mathit{zs} \land
%   |G ws| \land |G ys| \implies \mathit{ws} = \mathit{ys}\).
  
% \item \textbf{Uniqueness:} the internal representation of |G xs| is uniquely
%   determined by |xs|.
%   That means (using \(\mathit{Rep}_{|G|}(x,\mathit{xs})\) to express ``\(x\) is the
%   internal representation of |G xs|''),
%   \(\forall x\, y\, \mathit{xs}, \mathit{Rep}_{|G|}(x,\mathit{xs}) \land
%   \mathit{Rep}_{|G|}(y,\mathit{xs}) \implies x = y\).
% \end{itemize}
% \noindent Both of these properties have been proven for our specification of
% X.509 certificates.
% In Agda, predicates |Unambiguous| and |Unique| are defined as follow.
% \begin{figure}[h]
%   \centering
%   \begin{code}
%     Unambiguous : (List UInt8 -> Set) -> Set
%     Unambiguous G =  forall {ws xs ys zs} -> ws ++ xs == ys ++ zs
%                      -> G ws -> G ys -> ws == ys
%     Unique : (List UInt8 -> Set) -> Set
%     Unique G = forall {xs} -> (g h : G xs) -> g == h
%   \end{code}
%   \caption{Definition of unambiguousness and uniqueness}
%   \label{fig:unambig-uniq}
% \end{figure}

\subsection{Sound and Complete Parsing}
We now describe our approach to verified parsing.
Recall that, for a language \(G\), \emph{soundness} of a parser means that every
bytestring it accepts is in the language, and \emph{completeness} means that it
accepts every bytestring in the language.
Our approach to verifying these properties for all our parsers is to make them
\emph{correct by construction}, meaning that parsers do not merely indicate
success or failure with e.g.\ an integer code, but return \emph{proofs}. 
If the parser is successful, this is a proof that some prefix of its input is in
the language, and if the parser fails, it returns a proof that \emph{no} prefix
of its input is.

\subsubsection{The Type of Correct-by-Construction Parsers}
Our first step is to formally define what success in means.
In FOL, we would express the condition for the parser's success on a prefix of
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
  \centering
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

\textbf{Challenges.}
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

\subsubsection{Parser Soundness, Completeness, and Strong Completeness}
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
As our parsers are correct by construction, the definition is straightforward:
we use |toWitness| to extract the proof of parser success, i.e., a term of type
|Success G xs|, then use the field accessor |Success.value| to obtain the
desired proof that the consumed prefix is in |G|.

\textbf{Completeness.}
Recall that the definition of parser completeness with respect to a language |G|
means that if an input string |xs| is in |G|, the parser accepts \emph{some
  prefix of |xs|}.
Of course, this property in isolation does not rule out certain bad behavior
that threatness security; specifically, it does not contrain the parser's
freedom over (1) which prefix of the input is consumed, and (2) how the internal
datastructure is constructed.
However, and as we have discussed in Section~\ref{sec:s4-lang-spec}, these are
properties of the \emph{language}, and not its parsers.
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
  \caption{Parser weak completeness (definition and proof)}
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
\begin{figure}[h]
  \begin{code}
StronglyComplete : (G : @0 List A -> Set) -> Parser G -> Set
StronglyComplete G p = forall xs -> (inG : G xs)
  -> exists  (w : IsYes (p xs))
             ((_ , inG) == (_ , Success.value (toWitness w)))

strongCompleteness
  : forall {G} -> Unambiguous G -> NoSubstrings G
    -> (p : Parser G) -> StronglyComplete G p
strongCompleteness ua nn p xs inG = (w , secure xs inG s)
  where
  w = completeness p inG
  s = toWitness w
  secure : forall xs inG s -> (_ , inG) == (_ , Success.value s)
  secure xs inG s with nn _ inG (Success.prefix s)
  ... | refl with ua inG (Success.value s)
  ... | refl = refl
  \end{code}
  \caption{Strong completeness (definition and proof)}
  \label{fig:s4-parser-stcompleteness}
\end{figure}

\subsubsection{Parser Failure and Completeness}

\textbf{Completeness.} To finish, we now explain how our setup guarantees
completeness.
Assuming |G| is a language that satisfies |Unambiguous| and |Unique|
(Figure~\ref{fig:unambig-uniq}) (in particular, our specification
of X.509 certificates satisfies both), we are given a bytestring |xs| such that
some prefix of |xs| is in |G| (i.e., a value of type |Success G xs|), and must
show that our parser accepts precisely the same prefix of |xs|.
We analyze the two possible results of running the parser.
If the parser fails, that means \emph{no} prefix of |xs| is in |G|, but this
contradicts our assumption, so it must be that the parser succeeds, giving us
another value of type |Success G xs|
By a lemma, that |G| satisfies |Unambiguous| and |Unique| gives us that
|Success G| is also unique, meaning in particular that the two prefixes are the same.

The preceding proof sketch is formalized in our Agda development.
Figure~\ref{fig:parse-unique-complete} shows a simplified version of the proof.
\begin{figure}[h]
  \centering
  \begin{code}
uniqueParse : Unique (Success G)
uniqueParse = ...

SucceedsAndEq : forall {A} -> Dec A -> A -> Set
SucceedsAndEq (yes x) v = x == v
SucceedsAndEq (no x) v = False

completeParse :  forall xs -> (v : Success Q xs)
                 -> SucceedsAndEq (parse xs) v
completeParse xs v
  with parse xs
... | no  x = contradiction v x
... | yes x = uniqueParse x v
  \end{code}
  \caption{Unique parse and completeness}
  \label{fig:parse-unique-complete}
\end{figure}
The code listing of the figure has as parameters |G : List UInt8 -> Set| (the
language), proofs that |G| satisfies |Unambiguous| and |Unique|, and a parser
|parse : Parser G|.
Lemma |uniqueParse| gives the result that successful parses are unique, and the
binary relation |SucceedsAndEq| expresses that our parser succeeds and returns a
value equal to a specified |v| (|False| is the trivially false proposition).
Finally, |completeParse| is the proof of completeness, which proceeds by running
|parse xs| and inspecting the result: the case that the parser fails contradicts
our assumption, and in the case that the parser succeeds, we invoke the lemma
|uniqueParse|.

\subsection{Semantic Validation}

Our approach to semantic validation, as outlined in
Section~\ref{sec:semantic-checker}, is separating those properties that should
be verified for a single certificate and those that concern the entire chain.
For each property to validate, we formulate in Agda a predicate expressing
satisfaction of the property by a given certificate or chain, then prove that
these predicates are decidable.
These decidability proofs then serve as the functions called after parsing to
check whether the certificate or chain satisfies the property.

We consider two concrete examples, one each for a single-certificate and
certificate chain property.
For a single certificate, it must be the case that the \texttt{SignatureAlgorithm} field
must contain the same algorithm identifier as the \texttt{Signature} field of
the \texttt{TbsCertificate} (R1 in Table~\ref{rules} of the Appendix).
As a formula of FOL, we could express this property with respect to
certificate \(c\) as
\[
  \forall s_1\, s_2, \mathit{SignAlg}(s_1,c) \land \mathit{TbsCertSignAlg}(s_2,c)
  \implies s_1 = s_2
\]
where \(\mathit{SignAlg}(s_1,c)\) and \(\mathit{TbsCertSignAlg}(s_2,c)\) express
respectively the properties that \(s_1\) is the signature algorithm identifier
of \(c\) and that \(s_2\) is the signature algorithm identifier of the
\texttt{TbsCertificate} of \(c\).
In Agda, we express this property, and its corresponding decidability proof, as
follows.

\begin{code}
R1 : forall {@0 bs} -> Cert bs -> Set
R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c

r1 : forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
r1 c = ...  
\end{code}

For a certificate chain, it must be the case that a certificate does not appear
more than once in a prospective certificate path (R20 in Table~\ref{rules} of the Appendix).
As a formula of FOL, we could express this property with respect to a
certificate chain \(\mathit{cc}\) as
\[
  \begin{array}{l}
    \forall c_1\, c_2\, i_1\, i_2, \mathit{InChain}(c_1,i_1,\mathit{cc}) \land
    \mathit{InChain}(c_2,i_2,\mathit{cc}) \land i_1 \neq i_2
    \\ \quad \implies c_1 \neq c_2
  \end{array}
\]
where \(\mathit{InChain}(c_1,i_1,\mathit{cc})\) is the property that certificate
\(c_1\) is at index \(i_1\) in chain \(\mathit{cc}\).
The Agda standard library provides a definition of the property that all entries
of a list are distinct from each other, written below as |List.Unique|, as well
as a proof that this property is decidable, written |List.unique?|, provided
that the type of the list's elements support decidable equality.
We have proven equality is decidable for certificates, so we can express this
property and corresponding decidability proof in Agda as
\begin{code}
R20 : forall {@0 bs} -> Chain bs -> Set
R20 c = List.Unique (chainToList c)

r20 : forall {@0 bs} (c : Chain bs) -> Dec (R20 c)
r20 c = List.unique?  (chainToList c)
\end{code}
where we have defined function |chainToList| to convert a certificate chain to a
list of certificates.
% (see Section~\ref{sec:design-agda}).
% As discussed in Section~\ref{sec:overview-agda}, 

% \section{Detailed Approach} 
% Our method to formally verify the syntactic and semantic requirements of X.509 CCVL consists of two stages. Initially, we develop formal specifications of the syntactic and semantic requirements. Subsequently, we employ theorem-proving techniques to verify that each formalized specification indeed satisfies the expected properties, which are stated below.

% \begin{itemize}
% \item \textbf{Soundness:} If the CCVL implementation accepts an input certificate chain, then the formal specification also accepts the certificate chain. 
% \item \textbf{Completeness:} If the formal specification accepts an input certificate chain, then the CCVL implementation also accepts the certificate chain.
% \item \textbf{Secure Completeness:} If the formal specification accepts an input certificate chain and there are no two distinct ways for the specification to accept the input, then the CCVL implementation also accepts the certificate chain.
% \end{itemize}

% \subsection{Syntactic Requirements}

% \subsubsection{Writing the Specification} The specification for X.509 syntactic requirements serves as a rigorous and unambiguous description of the structure of X.509 certificate and its parser, which can then be used in the subsequent verification stage. Particularly, we devise a grammar formulation that aligns with the X.509 and X.690 specifications and serves as a comprehensive and readable formalization of the X.509 certificate. In general-purpose functional languages, using inductive types has proven to be an intuitive and effective strategy for articulating the grammar of a language. In light of this, our approach to formalizing the X.509 and X.690 specifications is premised upon applying inductive families, which serve as an extension of inductive types in a dependently typed context. 






% % \subsection{ization of Specification}

% % \subsection{Development of X.509 CCVL Implementation}
% % \subsubsection{Input Pre-processing} pem to base64 decoding
% % \subsubsection{Enforcing Syntactic Checks} parser
% % \subsubsection{Enforcing Semantic Checks} string transformation and others


% % \subsection{Design Challenges and Solutions}

% % \subsubsection{Correctness of Certificate Parser} We aspire to ensure that the construction of the certificate parser intrinsically embodies both soundness and completeness. This means that the parser, by design, should correctly accept all valid certificates (completeness) and reject all invalid ones (soundness), thereby eliminating the need for additional verification steps post-construction.

% % \textbf{Approach:} In pursuit of a sound parser, we architect it such that upon successful execution, it returns a proof confirming that the byte-string aligns with the grammar. In parallel, to ensure completeness, in cases of failure, the parser provides a refutation - a proof substantiating the impossibility of the grammar accepting the given byte-string. The combination of these characteristics is neatly encapsulated by the concept of decidability, formally defined in the Agda standard library as |Dec|. For clarity, we present a simplified and more intuitive version of this type below.

% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %     module DecSimple where
% %       data Dec (A : Set) : Set where
% %         yes : A -> Dec A
% %         no  : not A -> Dec A
% %   \end{code}
% %   \label{code2}
% %   \caption{Code Listing 2}
% % \end{figure}

% % Let us delve into a somewhat streamlined version of the definition of |Parser| utilized in ARMOR. In the following representation, the module parameter |S| corresponds to the type of characters in the alphabet, over which we have delineated a grammar.

% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %   module ParserSimple (S : Set) where
% %     record Success (@0 A : List S -> Set) (@0 xs : List S) 
% %         : Set where
% %       constructor success
% %       field
% %         @0 prefix : List S
% %         read   : N
% %         @0 readeq : read == length prefix
% %         value  : A prefix
% %         suffix : List S
% %         @0 pseq    : prefix ++ suffix == xs
% %     record Parser (M : Set -> Set) (@0 A : List S -> Set) 
% %         : Set where
% %       constructor mkParser
% %       field
% %         runParser : (xs : List S) -> M (Success A xs)
% %     open Parser public
% % \end{code}
% % \label{code3}
% % \caption{Code Listing 3}
% % \end{figure}

% % Let us break down the components of the above code.
% % \begin{enumerate}[(1)]

% % \item Initially, we must stipulate what the parser returns when it succeeds. This is denoted by the record |Success|.

% % \begin{itemize}
% % \item The parameter |A| represents the production rule (e.g., |BoolValue|), and |xs| represents the generic-character string we have parsed. Both of these are marked to be erased from runtime.
% % \item The field |prefix| is the prefix of our input string that the parser consumes. While we do not need to retain this at runtime, we maintain its length |read| available at runtime for the sake of length-bound checking.
% % \item The field |value| proves the prefix adheres to the production rule |A|.
% % \item The field |suffix| corresponds to the remainder of the string post-parsing. We need this at runtime to continue parsing any subsequent production rules.
% % \item Finally, the field |pseq| correlates |prefix| and |suffix| to the string |xs| that we started with, substantiating that they genuinely are a prefix and a suffix of the input.
% % \end{itemize}

% % \item Following this, we define the type |Parser| for parsers.
% % \begin{itemize}
% % \item The parameter |M| provides some flexibility in the type of values the parser returns. In most cases, it is instantiated with |Logging . Dec|, where |Logging| offers us lightweight debugging information. The parameter |A| is, once again, the production rule we wish to parse.
% % \item |Parser| comprises a single field |runParser|, which is a dependently typed function that takes a character string |xs| and returns |M (Success A xs)| (typically |Logging (Dec (Success A xs))|).
% % \end{itemize}

% % \end{enumerate}

% % This representation encapsulates the essential elements of the parser's structure and function, providing a basis for sound and complete parsing of the specified grammar.

% % \paragraph{\textbf{An Example Parser for Boolean:}}

% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %   private
% %     here' = "X690-DER: Bool"
  
% %   parseBoolValue : Parser (Logging . Dec) BoolValue
% %   runParser parseBoolValue [] = do  {- 1 -}
% %     tell $ here' String.++ ": underflow"
% %     return . no $ \ where
% %       (success prefix read readeq value suffix pseq) ->
% %         contradiction (++-conicall _ suffix pseq) 
% %           (nonempty value)
% %   runParser parseBoolValue (x :: xs) {- 2 -}
% %     with x =? UInt8.fromN 0 {- 3 -}
% %   ... | yes refl =
% %     return (yes (success _ _ refl 
% %               (mkBoolValue _ _ falser refl) xs refl))
% %   ... | no x/=0
% %     with x =? UInt8.fromN 255 {- 3 -}
% %   ... | yes refl =
% %     return (yes (success _ _ refl 
% %               (mkBoolValue _ _ truer refl) xs refl))
% %   ... | no  x/=255 = do {- 4 -}
% %     tell $ here' String.++ ": invalid boolean rep"
% %     return . no $ \ where
% %       (success prefix _ _ 
% %               (mkBoolValue v _ vr refl) suffix pseq) -> !!
% %         (case vr of \ where
% %           falser -> contradiction 
% %               (::-injectivel (sym pseq)) x/=0
% %           truer  -> contradiction 
% %               (::-injectivel (sym pseq)) x/=255)
% %   \end{code}
% %   \label{code4}
% %   \caption{Code Listing 4}
% %   \end{figure}

% %   Here is an explanation of the actions taken in different scenarios:
% %   \begin{enumerate}[(1)]
  
% %   \item If the input string is devoid of any characters (empty), we first generate an error message, then return a proof establishing that there is no possible parse of a |BoolValue| for an empty string. We employ Agda's |do|-notation for sequencing our operations.
% %   \item If there is at least one character present in the input string, we proceed with the following checks.
% %   \begin{itemize}
% %   \item We ascertain whether the character is equal to either 0 or 255. If it is, we affirm that this complies with the grammar.
% %   \item If the character does not equal either 0 or 255, we generate an error message and then return a parse refutation. This indicates that in order to adhere to the |BoolValue| requirement, our byte must be either 0 or 255.
% %   \end{itemize}
% %   \end{enumerate}

% %   In summary, these steps ensure the parser correctly identifies valid and invalid input strings, confirming its soundness and completeness.

% % \subsubsection{Backtracking}

% % Although the parsing of X.509 does not necessitate backtracking, our parser has been designed with some backtracking features to aid in the formalization process. For instance, the X.690 specification for |DisplayText| states that it may constitute an |IA5String|, |VisibleString|, |VisibleString|, or |UTF8String|. If the given byte-string does not conform to |DisplayText|, furnishing a refutation becomes more straightforward when we have direct evidence demonstrating its failure to comply with each possible type. This approach, while possibly adding complexity to the implementation, allows for more precise and verifiable proof of non-conformance. It also provides a more detailed understanding of the reasons for parsing failure, facilitating potential debugging or refinement of the input data.



% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %   private
% %     here' = "X509: DisplayText"
  
% %   parseDisplayText : Parser (Logging . Dec) DisplayText
% %   runParser parseDisplayText xs = do
% %     no not ia5Str <- runParser 
% %         (parseTLVLenBound 1 200 parseIA5String) xs
% %       where yes b -> return (yes (mapSuccess 
% %                       (\ {bs} -> ia5Str{bs}) b))
% %     no not visibleStr <- runParser 
% %         (parseTLVLenBound 1 200 parseVisibleString) xs
% %       where yes b -> return (yes (mapSuccess
% %                       (\ {bs} -> visibleStr{bs}) b))
% %     no not bmpStr <- runParser 
% %         (parseTLVLenBound 1 200 parseBMPString) xs
% %       where yes b -> return (yes (mapSuccess 
% %                       (\ {bs} -> bmpStr{bs}) b))
% %     no not utf8Str <- runParser 
% %         (parseTLVLenBound 1 200 parseUTF8String) xs
% %       where yes u -> return (yes (mapSuccess 
% %                       (\ {bs} -> utf8Str{bs}) u))
% %     return . no $ \ where
% %       (success prefix read readeq (ia5Str x) suffix pseq) ->
% %         contradiction (success _ _ readeq x _ pseq) not ia5Str
% %       (success prefix read readeq (visibleStr x) suffix pseq) ->
% %         contradiction (success _ _ readeq x _ pseq) not visibleStr
% %       (success prefix read readeq (bmpStr x) suffix pseq) ->
% %         contradiction (success _ _ readeq x _ pseq) not bmpStr
% %       (success prefix read readeq (utf8Str x) suffix pseq) ->
% %         contradiction (success _ _ readeq x _ pseq) not utf8Str
% %       \end{code}
% %       \label{code5}
% %       \caption{Code Listing 5}
% %       \end{figure}

% % \subsubsection{Complete and Secure Parsing}
% % The completeness of the parser is constructively ensured, and its rationale is relatively straightforward. Given a byte-string, if it complies with the grammar, the parser will accept the byte-string. The crux of this proof lies in proof by contradiction (which is constructively valid, given that the parser itself serves as evidence that the conformance to the grammar is decidable). Let us assume the parser rejects a string that actually conforms to the grammar. This rejection, however, comes bundled with a refutation of the possibility that the string aligns with the grammar, thereby contradicting our initial assumption.

% % When focusing on secure completeness, it is also crucial that the grammar is unambiguous, implying that there is a maximum of one way in which the grammar could be parsed. This concept is formally embodied as |UniqueParse| in the subsequent text. This is formalized as |UniqueParse| below.

% % % This combination of proof for both the soundness and completeness of the parser, alongside the formalization of unambiguity, ensures the robustness and security of our X.509 certificate chain validation implementation.


% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %   Unique : Set -> Set
% %   Unique A = (p1 p2 : A) -> p1 == p2


% %   UniqueParse : (List S -> Set) -> Set
% %   UniqueParse A = forall {@0 xs} -> Unique (Success A xs)
% % \end{code}
% % \label{code6}
% % \caption{Code Listing 6}
% % \end{figure}

% % We have derived a lemma that elucidates a sufficient condition for holding |UniqueParse|. The premises of this lemma are articulated solely in terms of the properties of the grammar itself. These properties include:
% % \begin{itemize}
% % \item Any two witnesses (under the Curry-Howard isomorphism, we interpret inhabitants of a type as witnesses when that type is taken as a proposition) that a specified string adheres to the grammar are equivalent. This is termed as |Unambiguous|.
% % \item If two prefixes of the identical string comply with the grammar, those prefixes are equal. This is referred to as |NonNesting|.
% % \end{itemize}
  
% %   \begin{figure}[h]
% %     \centering
% %     \begin{code}
% %   Unambiguous : (A : List S -> Set) -> Set
% %   Unambiguous A = forall {xs} -> Unique (A xs)
% %   NonNesting : (A : List S -> Set) -> Set
% %   NonNesting A =
% %     forall {xs1 ys1 xs2 ys2}
% %     -> (prefixSameString : xs1 ++ ys1 == xs2 ++ ys2)
% %     -> (a1 : A xs1) (a2 : A xs2) -> xs1 == xs2
% %   module _ {A : List S -> Set} (uA : Unambiguous A) 
% %         (nnA : NonNesting A) where
% %     @0 uniqueParse : UniqueParse A
% %     uniqueParse p1 p2
% %     {- = ... -}
% %   \end{code}
% %   \label{code7}
% %   \caption{Code Listing 7}
% %   \end{figure}
  
% %   This finally brings us to the statement and proof of complete and secure parsing.
% %   \begin{figure}[h]
% %     \centering
% %     \begin{code}
% %   Yes_And_ : {A : Set} -> Dec A -> (A -> Set) -> Set
% %   Yes (yes pf) And Q = Q pf
% %   Yes (no not pf) And Q = bot
  
  
% %   CompleteParse : (A : List S -> Set) -> Parser Dec A -> Set
% %   CompleteParse A p =
% %     forall {bs} -> (v : Success A bs) -> 
% %         Yes (runParser p bs) And (v ==_)
% %   module _ {A : List S -> Set}
% %     (uA : Unambiguous A) (nnA : NonNesting A) 
% %       (parser : Parser Dec A)
% %     where
% %     @0 completeParse : CompleteParse A parser
% %     completeParse{bs} v
% %       with runParser parser bs
% %     ... | (yes v')  = uniqueParse uA nnA v v'
% %     ... | no not v     = contradiction v not v
% %   \end{code}
% %   \label{code8}
% %   \caption{Code Listing 8}
% %   \end{figure}

% %   \begin{enumerate}[(1)]
% %   \item We first define an auxiliary predicate |Yes_And_| over decisions, signifying that the decision is |yes| and the predicate |Q| holds for the affirmative proof accompanying it.
% %   \item Next, we define the predicate |CompleteParse| in terms of |Yes_And_|. This expresses that if |v| serves as a witness that some prefix of |bs| complies with |A|, then the parser returns in the affirmative, and the witness it returns matches |v|.
% %   \item We then prove the property |CompleteParse| under the presupposition that |A| is |Unambiguous| and |NonNesting|. The proof follows a case-by-case analysis based on the result of running the parser on the given string.

% %   \begin{itemize}
% %   \item If the parser produces an affirmation, we appeal to the lemma |uniqueParse|.
% %   \item If the parser produces a refutation, we encounter a |contradiction|.
% %   \end{itemize}
% % \end{enumerate}

% %   Through these steps, we demonstrate that the parser is complete, meaning it correctly recognizes all strings that conform to the grammar. This ensures the correctness of the parser and provides a robust foundation for the formal verification of our X.509 certificate chain validation implementation.


% % \subsubsection{Semantic Checks}
% % Certain properties we wish to verify may not lend themselves well to formalization as part of the grammar. For instance, the X.509 specification mandates that the signature algorithm field of the TBS (To-Be-Signed) certificate aligns with the signature algorithm outlined in the outer certificate - a highly non-local property. Aeres performs checks for such properties post-parsing.

% % We first draft a property specification for each of these properties, followed by proof that this property is decidable. The proof serves as the function we employ to ascertain whether the property holds. When interpreted in this manner, it is sound and complete by construction, paralleling the reasoning that ensures the soundness and completeness of our parser.

% % This method allows us to formally verify properties beyond the immediate grammar rules, providing a more comprehensive and robust verification of our X.509 certificate chain validation implementation. This approach ensures adherence to the syntactic rules of the certificate format and the fulfillment of broader, semantically meaningful properties.

% % \begin{figure}[h]
% %   \centering
% %   \begin{code}
% %   R1 : forall {@0 bs} -> Cert bs -> Set
% %   R1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c
  
% %   r1 :  forall {@0 bs} (c : Cert bs) -> Dec (R1 c)
% %   r1 c =
% %     case (proj2 (Cert.getTBSCertSignAlg c) =? 
% %         proj2 (Cert.getCertSignAlg c)) ret (const _) of \ where
% %       (yes eqrefl) -> yes refl
% %       (no not eq) -> no \ where refl -> contradiction eqrefl not eq
% %     \end{code}
% %     \label{code9}
% %     \caption{Code Listing 9}
% %     \end{figure}


% % \subsection{Executable Extraction}


