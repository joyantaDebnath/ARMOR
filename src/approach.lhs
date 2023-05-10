\section{Detailed Approach}

\subsection{Formalization of Specification}

\subsection{Development of X.509 CCVL Implementation}
\subsubsection{Input Pre-processing} pem to base64 decoding
\subsubsection{Enforcing Syntactic Checks} parser
\subsubsection{Enforcing Semantic Checks} string transformation and others

\section{Correctness Proofs}

\subsection{Correctness Criteria}
\begin{itemize}
\item \textbf{Soundness:} If the CCVL implementation accepts an input certificate chain, then the formal specification also accepts the certificate chain. 
\item \textbf{Completeness:} If the formal specification accepts an input certificate chain, then the CCVL implementation also accepts the certificate chain.
\item \textbf{Secure Completeness:} If the formal specification accepts an input certificate chain and there are no two distinct ways for the specification to accept the input, then the CCVL implementation also accepts the certificate chain.
\end{itemize}


\subsection{Design Challenges and Solutions}

\subsubsection{Represetation of Certificate Grammar} Our primary challenge is determining the most effective method for representing the X.509 certificate grammar. Our goal is to devise a grammar formulation that aligns with the X.509 and X.690 specifications and serves as a comprehensive and readable formalization thereof.

\textbf{Approach.} In general-purpose functional languages, using inductive types has proven to be an intuitive and effective strategy for articulating the grammar of a language. In light of this, our approach to formalizing the X.509 and X.690 specifications is premised upon applying inductive families, which serve as an extension of inductive types in a dependently typed context.

To illustrate this, consider a straightforward example: the Boolean values in the X.690 Distinguished Encoding Rules (DER). Per the Basic Encoding Rules (BER), Boolean values must comprise a singular octet, with FALSE denoted by setting all bits to 0 and TRUE denoted by setting at least one bit to 1. The DER further mandates that the value TRUE is signified by setting all bits to 1. We capture these constraints in our formal representation as follows.


\begin{figure}[h]
  \centering
  \begin{code}
    module BoolExample where
      data BoolRep : Bool -> UInt8 -> Set where
        falser : BoolRep false (UInt8.fromN 0)
        truer  : BoolRep true (UInt8.fromN 255)
      record BoolValue (@0 bs : List UInt8) -> Set where
        constructor mkBoolValue
        field
          v     : Bool
          @0 b  : UInt8
          @0 vr : BoolRep v b
          @0 bseq : bs == [ b ]
    \end{code}
    \label{code1}
    \caption{Code Listing 1}
  \end{figure}


\begin{enumerate} [(1)]
\item Here, we establish a binary relation, |BoolRep|, which correlates Boolean values in Agda, denoted as |Bool|, with the octet values stipulated by the X.690 DER. The function |UInt8.fromN| transforms a non-negative unbounded integer into its equivalent |UInt8| representation. It is important to note that this transformation is contingent upon Agda's ability to automatically verify that the provided number is less than 256.

\item Subsequently, we construct a record, |BoolValue|, to represent the Boolean value defined by X.690.

\begin{itemize}
\item Each grammar production rule, such as |BoolValue|, is exemplified by a type family of type |@0 List UInt8 -> Set|. We interpret this as the type of predicates over byte strings.

\item The components of the record consist of the Boolean value |v|, its byte-string representation |b|, a proof |vr| of type |BoolRep v b| validating that |b| is the correct representation of |v|, and a proof |bseq| establishing that the byte string representation of this terminal of the grammar is the singleton list comprising |b| (denoted as |[ b ]|).

\item The |@0| annotations applied to types and fields signify that the respective values are erased at run-time. This approach is implemented for a dual purpose: firstly, to diminish the space and time overhead associated with ARMOR executions; and secondly, to function as a form of machine-enforced documentation that specifies those portions of the formalization that are purely intended for verification purposes.
\end{itemize}
\end{enumerate}

\subsubsection{Correctness of Certificate Parser} We aspire to ensure that the construction of the certificate parser intrinsically embodies both soundness and completeness. This means that the parser, by design, should correctly accept all valid certificates (completeness) and reject all invalid ones (soundness), thereby eliminating the need for additional verification steps post-construction.

\textbf{Approach:} In pursuit of a sound parser, we architect it such that upon successful execution, it returns a proof confirming that the byte-string aligns with the grammar. In parallel, to ensure completeness, in cases of failure, the parser provides a refutation - a proof substantiating the impossibility of the grammar accepting the given byte-string. The combination of these characteristics is neatly encapsulated by the concept of decidability, formally defined in the Agda standard library as |Dec|. For clarity, we present a simplified and more intuitive version of this type below.

\begin{figure}[h]
  \centering
  \begin{code}
    module DecSimple where
      data Dec (A : Set) : Set where
        yes : A -> Dec A
        no  : not A -> Dec A
  \end{code}
  \label{code2}
  \caption{Code Listing 2}
\end{figure}

Let us examine (a slightly simplified version of) the definition of
|Parser| used in Aeres.
Below, module parameter |S| is the type of the characters of the
alphabet over which we have defined a grammar.

\begin{figure}[h]
  \centering
  \begin{code}
  module ParserSimple (S : Set) where
    record Success (@0 A : List S -> Set) (@0 xs : List S) 
        : Set where
      constructor success
      field
        @0 prefix : List S
        read   : N
        @0 readeq : read == length prefix
        value  : A prefix
        suffix : List S
        @0 pseq    : prefix ++ suffix == xs
    record Parser (M : Set -> Set) (@0 A : List S -> Set) 
        : Set where
      constructor mkParser
      field
        runParser : (xs : List S) -> M (Success A xs)
    open Parser public
\end{code}
\label{code3}
\caption{Code Listing 3}
\end{figure}

\begin{itemize}
\item We first must specify what the parser returns when it succeeds.
This is given by the record |Success|.

\begin{itemize}
\item Parameter |A| is the production rule (e.g.,
|BoolValue|), and |xs| is the generic-character
string which we parsed.
Both are marked erased from run-time

\item Field |prefix| is the prefix of our input string consumed by
the parser.
We do not need to keep this at run-time, however for the purposes of
length-bounds checking we do keep its length |read| available
at run-time.

\item Field |value| is a proof that the prefix conforms to the
production rule |A|.

\item Field |suffix| is what remains of the string after parsing.
We of course need this at run-time to continue parsing any subsequent
production rules.

\item Finally, field |pseq| relates |prefix| and
|suffix| to the string |xs| that we started with,
i.e., they really are a prefix and suffix of the input.
\end{itemize}

\item Next, we define the type |Parser| for parsers.
\begin{itemize}
\item Parameter |M| is used to give us some flexibility in the type
of the values returned by the parser.
Almost always, it is instantiated with
|Logging . Dec|,
where |Logging| provides us lightweight debugging
information.
Parameter |A| is, again, the production rule we wish to parse.

\item |Parser| consists of a single field |runParser|,
which is a dependently type function taking a character string
|xs| and returning
|M (Success A xs)|
(again, usually |Logging (Dec (Success A xs))|)
\end{itemize}
\end{itemize}

\textbf{Example}

It is helpful to see an example parser.

\begin{figure}[h]
  \centering
  \begin{code}
  private
    here' = "X690-DER: Bool"
  
  parseBoolValue : Parser (Logging . Dec) BoolValue
  runParser parseBoolValue [] = do  {- 1 -}
    tell $ here' String.++ ": underflow"
    return . no $ \ where
      (success prefix read readeq value suffix pseq) ->
        contradiction (++-conicall _ suffix pseq) 
          (nonempty value)
  runParser parseBoolValue (x :: xs) {- 2 -}
    with x =? UInt8.fromN 0 {- 3 -}
  ... | yes refl =
    return (yes (success _ _ refl 
              (mkBoolValue _ _ falser refl) xs refl))
  ... | no x/=0
    with x =? UInt8.fromN 255 {- 3 -}
  ... | yes refl =
    return (yes (success _ _ refl 
              (mkBoolValue _ _ truer refl) xs refl))
  ... | no  x/=255 = do {- 4 -}
    tell $ here' String.++ ": invalid boolean rep"
    return . no $ \ where
      (success prefix _ _ 
              (mkBoolValue v _ vr refl) suffix pseq) -> !!
        (case vr of \ where
          falser -> contradiction 
              (::-injectivel (sym pseq)) x/=0
          truer  -> contradiction 
              (::-injectivel (sym pseq)) x/=255)
  \end{code}
  \label{code4}
  \caption{Code Listing 4}
  \end{figure}

\begin{enumerate}
\item When the input string is empty, we emit an error message, then return a
proof that there is no parse of a |BoolValue| for the empty
string

We use Agda's |do|-notation to sequence our operations

\item If there is at least one character, we check
\item whether it is equal to 0 or 255.
If so, we affirm that this conforms to the grammar.
\item If it is not equal to either, we emit an error message then return a
parse refutation: to conform to |BoolValue|, our byte must
be either 0 or 255.
\end{enumerate}

\paragraph{\textbf{Backtracking}}

Although backtracking is not required to parse X.509, our parser has been
implemented with some backtracking to facilitate the formalization.
For an example, the X.690 specification for |DisplayText|
states it may comprise an |IA5String|,
|VisibleString|, |VisibleString|, or
|UTF8String|.
In the case that the give byte-string does not conform to |DisplayTex|
providing a refutation is easier when we have direct evidence that it fails
to conform to each of these.



    \begin{code}
  private
    here' = "X509: DisplayText"
  
  parseDisplayText : Parser (Logging . Dec) DisplayText
  runParser parseDisplayText xs = do
    no not ia5String <- runParser (parseTLVLenBound 1 200 parseIA5String) xs
      where yes b -> return (yes (mapSuccess (\ {bs} -> ia5String{bs}) b))
    no not visibleString <- runParser (parseTLVLenBound 1 200 parseVisibleString) xs
      where yes b -> return (yes (mapSuccess (\ {bs} -> visibleString{bs}) b))
    no not bmp <- runParser (parseTLVLenBound 1 200 parseBMPString) xs
      where yes b -> return (yes (mapSuccess (\ {bs} -> bmpString{bs}) b))
    no not utf8 <- runParser (parseTLVLenBound 1 200 parseUTF8String) xs
      where yes u -> return (yes (mapSuccess (\ {bs} -> utf8String{bs}) u))
    return . no $ \ where
      (success prefix read readeq (ia5String x) suffix pseq) ->
        contradiction (success _ _ readeq x _ pseq) notia5String
      (success prefix read readeq (visibleString x) suffix pseq) ->
        contradiction (success _ _ readeq x _ pseq) notvisibleString
      (success prefix read readeq (bmpString x) suffix pseq) ->
        contradiction (success _ _ readeq x _ pseq) notbmp
      (success prefix read readeq (utf8String x) suffix pseq) ->
        contradiction (success _ _ readeq x _ pseq) notutf8
      \end{code}

\subsubsection{Complete and Secure Parsing}
Completeness of the parser is by construction, and straightforward to explain:
given a byte-string, if it conforms to the grammar then the parser accepts the
byte-string. The heart of the proof is proof by contradiction (which is
constructively valid, since the parser is itself evidence that conformance to
the grammar is decidable): suppose the parser rejects a string which conforms
to the grammar. Then, this rejection comes with a refutation of the
possibility that the string conforms with the grammar, contradicting our
assumption.
When it comes to security, we also care that the grammar is \emph{unambiguous},
by which we mean that there is at most one way in which the grammar might be
parsed.
This is formalized as |UniqueParse| below
  \begin{code}
  Unique : Set -> Set
  Unique P = (p1 p2 : P) -> p1 == p2
  UniqueParse : (List S -> Set) -> Set
  UniqueParse A = forall {@0 xs} -> Unique (Success A xs)
  \end{code}
  We have a lemma that establishes a sufficient condition for when
  |UniqueParse| holds, whose premises are stated only in terms of
  properties of the grammar itself.
  These properties are:
  1. Any two witness[fn|::|By which we mean inhabitants of a type, when we interpret that type as a proposition under the Curry-Howard isomorphism]
     that a given string conforms to the grammar are equal (|Unambiguous|), and
  2. If two prefixes of the same string conform to the grammar, those prefixes are equal (|NonNesting|)
  \begin{code}
  Unambiguous : (A : List S -> Set) -> Set
  Unambiguous A = forall {xs} -> Unique (A xs)
  NonNesting : (A : List S -> Set) -> Set
  NonNesting A =
    forall {xs1 ys1 xs2 ys2}
    -> (prefixSameString : xs1 ++ ys1 == xs2 ++ ys2)
    -> (a1 : A xs1) (a2 : A xs2) -> xs1 == xs2
  module _ {A : List S -> Set} (uA : Unambiguous A) (nnA : NonNesting A) where
    @0 uniqueParse : UniqueParse A
    uniqueParse p1 p2
    {- = ... -}
    \end{code}
  
  This finally brings us to the statement and proof of complete and secure parsing.
  \begin{code}
  Yes_And_ : {P : Set} -> Dec P -> (P -> Set) -> Set
  Yes (yes pf) And Q = Q pf
  Yes (no notpf) And Q = bot
  CompleteParse : (A : List S -> Set) -> Parser Dec A -> Set
  CompleteParse A p =
    forall {bs} -> (v : Success A bs) -> Yes (runParser p bs) And (v ==_)
  module _ {A : List S -> Set}
    (uA : Unambiguous A) (nnA : NonNesting A) (parser : Parser Dec A)
    where
    @0 completeParse : CompleteParse A parser
    completeParse{bs} v
      with runParser parser bs
    ... | (yes v')  = uniqueParse uA nnA v v'
    ... | no notv     = contradiction v notv
  \end{code}

\begin{enumerate}
\item We define an auxiliary predicate |Yes\_And\_| over decisions,
expressing that the decision is |yes| and
the predicate |Q| holds for the affirmative proof that comes with
it.
\item The predicate |CompleteParse| is defined in terms of
|Yes\_And\_|, expressing that if |v| is a witness that
some prefix of |bs| conforms to |A|, then the parser
returns in the affirmative and the witness it returns is equal to
|v|.
\item We then prove the property |CompleteParse| under the
assumption that |A| is |Unambiguous| and
|NonNesting|.
The proof proceeds by cases on the result of running the parser on the
given string.
\begin{itemize}
\item If the parser produces an affirmation, we appeal to lemma
|uniqueParse|.
\item If the parser produces a refutation, we have a
|contradiction|
\end{itemize}
\end{enumerate}


\paragraph{\textbf{Semantic Checks}}
Some properties that we wish to verify are not as suitable for formalization
as part of the grammar.
For example, the X.509 specification requires that the signature algorithm
field of the TBS certificate matches the signature algorithm listed in the
outer certificate --- a highly non-local property.
Aeres checks such properties after parsing.
For each of these, we first write a specification of the property, then a
proof that that property is \emph{decidable}.
This proof is itself the function that we call to check whether the property
holds, and interpreted as such, it is sound and complete by construction for
the same reasons that our parser is.

% \begin{code}
%   SCP1 : forall {@0 bs} -> Cert bs -> Set
%   SCP1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c
%   scp1 :  forall {@0 bs} (c : Cert bs) -> Dec (SCP1 c)
%   scp1 c =
%     case (proj2 (Cert.getTBSCertSignAlg c) ===? proj2 (Cert.getCertSignAlg c)) ret (const _) of \ where
%       (yes === -refl) -> yes refl
%       (no noteq) -> no \ where refl -> contradiction === -refl noteq
% \end{code}


\subsection{Executable Extraction}