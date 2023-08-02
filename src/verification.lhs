\section{Verification and Correctness Proofs}
This section describes our verification goals and how we achieved them.
In Section~\ref{sec:our-objective}, we gave a high-level description of our
primary objectives for verified parsing, \emph{soundness} and
\emph{completeness}.
We now explain concretely how this is expressed in Agda (specifically, how
language membership and parser acceptance are defined) and detail the challenges
faced for obtaining soundness and completeness.
We also describe our approach to semantic validation.
% We saw in Section~\ref{sec:design-agda} that Agda allows us to write precise
% specifications of X.690 DER and X.509 encoding.
% These specifications are themselves one of our contributions, as they are
% rigorous formalizations of the natural-language descriptions of these encodings.
% The other contributions of our verification efforts are our sound and complete
% parser, proofs of \emph{uniqueness} and \emph{unambiguousness} of the
% specification, and the specifications of, and correct implementations for, the
% semantic validations. 

\subsection{X.509 Specification}
Our first challenge concerns how the specification is represented, that is,
answering the question ``soundness and completeness \emph{with respect to
  what?}''
Figure~\ref{fig:code1} (Section~\ref{sec:design-agda}) shows the essence of our
approach: for each production rule |G| of the X.509 and X.690 grammar we
support, we define a predicate |G : List UInt8 -> Set| over bytestrings (such as
|BoolValue|).
Membership of a bytestring |xs| in the language denoted by |G| corresponds to
the truth of the proposition |G xs|.

For each defined |G| we are careful to document which components are ``data''
and which are ``specification.''
For example, field |v| of |BoolValue| is data and the remaining fields are
specification.
One of the primary advantages of Agda is that there is one language for both
programs and proofs, but this strength becomes a challenge when trying to
enforce this distinction.
Our approach is to use erasure annotations (|@0|) on components serving
specificational purposes only.
This not only improves the performance of ARMOR, as these components are removed
by the Agda's GHC backend, but it also gives programmers using ARMOR as a reference
assurance that that those components need not be present in implementations
designed to run in resource-constrained environments.

\subsubsection{Properties}
A major advantage of our approach to specifying X.509 is that we can prove
properties \emph{about} these specifications, increasing trust that we have
accurately captured the meaning of the natural language descriptions.
In addition, two properties in particular are essential to our proof of parser
completeness.
\begin{itemize}
\item \textbf{Unambiguous:} at most one prefix of a bytestring can belong to
  |G|.
  That means, \(\forall \mathit{ws}\, \mathit{xs}\, \mathit{ys}\, \mathit{zs},
  \mathit{ws} +\!\!\!+ \mathit{xs} = \mathit{ys} +\!\!\!+ \mathit{zs} \land
  |G ws| \land |G ys| \implies \mathit{ws} = \mathit{ys}\).
  
\item \textbf{Uniqueness:} the internal representation of |G xs| is uniquely
  determined by |xs|.
  That means (using \(\mathit{Rep}_{|G|}(x,\mathit{xs})\) to express ``\(x\) is the
  internal representation of |G xs|''),
  \(\forall x\, y\, \mathit{xs}, \mathit{Rep}_{|G|}(x,\mathit{xs}) \land
  \mathit{Rep}_{|G|}(y,\mathit{xs}) \implies x = y\).
\end{itemize}
\noindent Both of these properties have been proven for our specification of
X.509 certificates.
In Agda, predicates |Unambiguous| and |Unique| are defined as follow.
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

\subsection{Sound and Complete Parsing}
Recall that, for a language \(G\), \emph{soundness} of a parser means that every
bytestring it accepts is in the language, and \emph{completeness} means that it
accepts every bytestring in the language.
Our approach to verifying these properties for our X.509 CCVL parser is to make
it \emph{correct by construction}, meaning that the parser does not merely
indicate success or failure as a Boolean or integer code, but returns a proof.
If the parser is successful, this is a proof that some prefix of its input is in
the language, and if the parser fails, it returns a proof that \emph{no} prefix
of its input is.

\subsubsection{Parser Success and Soundness}
Our first step is to formally define what it means for the parser to be
successful.
In FOL, we would express the condition for the parser's success on a prefix of
|xs| as \(\exists \mathit{ys}\, \mathit{zs}, \mathit{xs} = \mathit{ys} +\!\!\!+
\mathit{zs} \land |G ys|\).
In Agda, we express this as the parameterized record |Success|, shown below.
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

Note that fields |prefix| (the consumed prefix) and |pseq| (relating the prefix
and suffix to the original bytestring) are erased from runtime; the data carried
at runtime is the remaining bytestring to parse, |suffix|, and the parsed value,
|value|, a proof that |prefix| is in the language denoted by |G|.
As a consequence, \textbf{soundness is immediate}.

\subsubsection{Parser Failure and Completeness}
Our next step is to define what parser failure means.
We define this to be the condition that \emph{no} prefix of the input |xs| is in
the language of |G|, which is to say the failure condition is the
\emph{negation} of the success condition: |not Success G xs|.

To have the parser return |Success G xs| on success and |not Success G xs| on
failure, we turn datatype |Dec| in the Agda standard library, shown below.
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
Parser G = (xs : List UInt8) -> Dec (Success G xs)    
  \end{code}
  \caption{Definition of |Parser|}
  \label{fig:parser-def}
\end{figure}%
|Parser| is a family of types, where for each language |G| family member
|Parser G| is the proposition that, for all bytestrings |xs|, it is decidable
whether some prefix of |xs| is in |G|; alternatively, we can (as programmers)
read it as the type of functions with take a bytestring and possibly return a
parsed data structure and remaining bytestring to continue parsing.

\textbf{Completeness:} To finish, we now explain how our setup guarantees
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
more than once in a prospective certificate path (R23 in Table~\ref{rules} of the Appendix).
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
R23 : forall {@0 bs} -> Chain bs -> Set
R23 c = List.Unique (chainToList c)

r23 : forall {@0 bs} (c : Chain bs) -> Dec (R23 c)
r23 c = List.unique?  (chainToList c)
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


