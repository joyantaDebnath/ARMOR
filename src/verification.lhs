\section{Verification and Correctness Proofs}
We saw in Section~\ref{sec:design-agda} that Agda allows us to write precise
specifications of X.690 DER and X.509 encoding.
These specifications are themselves one of our contributions, as they are
rigorous formalizations of the natural-language descriptions of these encodings.
The other contributions of our verification efforts are our sound and complete
parser, proofs of \emph{uniqueness} and \emph{unambiguousness} of the
specification, and the specifications of, and correct implementations for, the
semantic validations. 


\subsection{Sound and Complete Parsing}
Recall that, for a language \(G\), \emph{soundness} of a parser means that every
bytestring it accepts is in the language, and \emph{completeness} means that it
accepts every bytestring in the language.
Our approach to verifying these properties for our X.509 CCVL parser is to make
it \emph{correct by construction}, meaning that when the parser executes, it
returns a proof.
If the parser is successful, this is a proof that some prefix of its input is in
the language, and if the parser fails, it returns a proof that \emph{no} prefix
of its input is (we will see later in this section how this treatment of the
failure case, along with a couple of proofs about the language itself,
establishes completeness).

Taking |BoolValue| as our running example, the type of the
parser is |Parser BoolValue|, where |Parser| (a simplified version of our actual
parser type) is defined below.
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

    data Dec (A : Set) : Set where
      yes : A -> Dec A
      no  : not A -> Dec A
        
    Parser : (List UInt8 -> Set) -> Set
    Parser G = (xs : List UInt8) -> Dec (Success G xs)
  \end{code}
  \caption{Definition of |Parser|}
  \label{fig:parser-def}
\end{figure}

We start by explaining the meaning of |Success|, which expresses what it means
for the parser to succeed.
\begin{itemize}
\item Record |Success| is parameterized by |G : List UInt8 -> Set|, which is the
  production rule for the grammar (e.g., |BoolValue|), and |xs : List UInt8|,
  the bytestring input of the parser.
  
\item The parser consumes some |prefix| of the string, with a |suffix|
  remaining.
  Field |pseq| captures the relation between the original input and the |prefix|
  and |suffix| fields: |prefix ++ suffix == xs|.
  
% \item For parsing TLV-encoded values, it is useful to record the number of bytes
%   consumed in parsing.
%   Since the |prefix| is erased, the field |read| (an unbounded nonnegative
%   integer) stores this number, and field |readeq| enforces that |read| really is
%   this number.
  
\item Finally, field |value| is a proof that the |prefix| conforms to the
  production rule |G|.
\end{itemize}

With |Success|, we have already \emph{soundness}: whenever the parser succeeds,
we produce a proof (field |value|) that a prefix of the bytestring is in the
language denoted by the production rule we parsed.
Of course, parsing can fail, and a parser that \textbf{always} fails is
trivially sound.
To prove \emph{completeness}, we need to know that failure of our parser means
\emph{no prefix of the input is in the language}.
This is the role played by |Dec| (which is part of Agda's standard library,
and whose name refers to \emph{decidability} of a proposition).
Constructor |yes| is used when the parser succeeds, as it takes a proof of e.g.,
|Success BoolValue xs|; constructor |no| is used when the parser fails, as it
takes a proof of e.g., |not Success BoolValue xs| (that is, a proof that the
truth of |Success BoolValue xs| would entail a contradiction).

With these definitions understood, we turn to the definition of |Parser|
itself, which we can read two complementary ways.
As programmers, we can read |Parser BoolValue| as the type for functions which
type a bytestring |xs| and returns a tagged union type, where one tag
corresponds to a successful parse and the other corresponds to a parse failure.
Reading as mathematicians, |Parser BoolValue| is the proposition that, for all
bytestrings |xs|, it is decidable whether some prefix of |xs| is in the language
denoted by |BoolValue|.

\subsubsection{Completeness}
While soundness comes as a direct consequence of the definition of |Success|,
for completeness we need to know some properties hold for the language itself.
Specifically, the grammar may be ambiguous, meaning multiple prefixes of the
same input may be in the language; by their types, however, our parser can
choose only one possibility.
The challenge that this poses to proving completeness is that if we assume some
prefix of a bytestring is in the language, even though we can conclude that the
parser will succeed (by contradiction: if the parser fails, no prefix is in the
language, contradicting our assumption), we \emph{cannot} know that what we
parsed was in fact the bytestring we were give (we only know \emph{some} prefix
was parsed).

An issue related to this concern the specifications themselves, which serve as
an internal representation of the X.509 certificate.
If the specification leaves any degrees of freedom in how the parser populates
this internal data structure, this becomes a source of bugs that undermine the
very purpose of verification.
It is desirable to know, therefore, that there is \emph{at most one way} to
populate these fields.

We call the two properties discussed above \emph{unambiguousness} and
\emph{uniqueness}, and there meaning is expressed formally in Agda by the
definitions below.
\begin{figure}[h]
  \centering
  \begin{code}
Unambiguous : (List UInt8 -> Set) -> Set
Unambiguous G =  forall {ws xs ys zs} -> ws ++ xs == ys ++ zs
                 -> G ws -> G ys -> ws == ys
Unique : (List UInt8 -> Set) -> Set
Unique G = forall {xs} -> (g h : G xs) -> g == h
  \end{code}
  \caption{Definition of unambiguousness and uniqueness}
  \label{fig:unambig-uniq}
\end{figure}

Continuing with |BoolValue| as the example, our proofs of |Unambiguous BoolValue|
and |Unique BoolValue| enable us to prove a lemma that there is only one way to
successfully parse a Boolean value.
This lemma is in turn used to prove completeness.
The statements for both properties, as well as the proof of completeness, are
shown below.
\begin{figure}[h]
  \centering
  \begin{code}
uniqueParse : Unique (Success BoolValue)
uniqueParse = ...

YesAnd : forall {A} -> Dec A -> (A -> Set)
YesAnd (yes x) Q = Q x
YesAnd (no x) = False

completeParse :  forall xs -> (v : Success BoolValue xs)
                 -> YesAnd (parseBoolValue xs) \ x -> x == v
completeParse xs unique v
  with parseBoolValue xs
... | yes x = uniqueParse x v
... | no  x = contradiction v x
  \end{code}
  \caption{Unique parse and completeness}
  \label{fig:parse-unique-complete}
\end{figure}

The type of |completeParse| is a bit tricky for those unfamiliar with Agda, so
we endeavor to explain only the big picture.
Definition |YesAnd| expresses that a yes-no decision (of type |Dec A|) is
actually a |yes|, \emph{and} an additional property |Q| holds for the proof
carried with that |yes|.
So, |completeParse| says that if some prefix of |xs| is in the language denoted
by |BoolValue|, then not only will |parseBoolValue| succeed, the |BoolValue| it
returns is identical to the arbitrary one we have been given.
In particular, this means we parsed the same prefix as the one assumed to be in
the language.

\subsection{Semantic Validation}
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
% %   SCP1 : forall {@0 bs} -> Cert bs -> Set
% %   SCP1 c = Cert.getTBSCertSignAlg c == Cert.getCertSignAlg c
  
% %   scp1 :  forall {@0 bs} (c : Cert bs) -> Dec (SCP1 c)
% %   scp1 c =
% %     case (proj2 (Cert.getTBSCertSignAlg c) =? 
% %         proj2 (Cert.getCertSignAlg c)) ret (const _) of \ where
% %       (yes eqrefl) -> yes refl
% %       (no not eq) -> no \ where refl -> contradiction eqrefl not eq
% %     \end{code}
% %     \label{code9}
% %     \caption{Code Listing 9}
% %     \end{figure}


% % \subsection{Executable Extraction}


