\section{Detailed Approach}

\subsection{Formalization of Specification}

\subsection{Development of X.509 CCVL Implementation}
\subsubsection{Input Pre-processing} pem to base64 decoding
\subsubsection{Enforcing Syntactic Checks} parser
\subsubsection{Enforcing Semantic Checks} string transformation and others

\subsection{Correctness Proofs}

\subsection{Executable Extraction}


% \begin{code}[hide]
%     open import Aeres.Prelude
%       hiding (Dec ; yes ; no ; Unique)
%     open import Aeres.Binary
    
%     module summary where
    
%     open Base256
%     \end{code}

% \section{Operative Notions}
% \label{sec:org7332b29}

% \begin{itemize}
% \item \textbf{soundness} If the parser accepts the string, so does the grammar

% \item \textbf{completeness} If the grammar accepts the string, so does the parser

% \item \textbf{secure completeness} If the grammar accepts the string, so does the parser,
% and there are no two distinct ways for the grammar to accept the string.

% NOTE TO OMAR: I'm not sure if this is good terminology, or even if it is a
% good idea to group completeness (a relation between the grammar and parser)
% and uniqueness (a property of the grammar).
% \end{itemize}

% \section{Overview}
% \label{sec:orgedf3fce}

% \begin{enumerate}
% \item The Aeres external driver is invoked with the filepath of the certificate
% chain we wish to check.
% The driver invokes Aeres with the contents of this file.

% \item Aeres uses its verified PEM parser library to parse the PEM certificate
% chain, then decodes the Base64-encoded certificates into a single
% bytestring.\footnote{We maybe could have decoded it to a list of bytestrings and
% parsed each, come to think of it\ldots{}}

% (Sound and complete parsing)

% \item Aeres uses its verified X.509 parser library to parse the bytestring into a
% list of certificates.

% (Sound, complete, secure)

% \item Aeres then checks several semantic properties not suitable for expressing
% in the grammar (e.g., validity period of cert contains current time)

% \item For each cert, Aeres outputs the bytestring serializations for the TBS
% certificate, signature, and public key, and also outputs the signature
% algorithm OIDLeastBytes

% \item The external driver verifies the public key signatures.
% \end{enumerate}



% \section{Design (Challenges and Solutions)}
% \label{sec:org4bf85da}
% \subsection{Grammar}
% \label{sec:org29db303}
% \textbf{Challenge} Our first and most fundamental question is: how shall we represent
% the grammar?
% Recall that our operative notion of soundness is "if the parser accepts the
% string, then so does the grammar."
% We also wish for our formulation of the grammar to serve as a readable
% formalization of the X.509 and X.690 specification.

% \textbf{Solution} In general purpose functional languages, inductive types are a
% natural choice for expressing the grammar of a language.
% Our choice of formalizing X.509 and X.680 is \emph{inductive families}, the
% generalization of inductive types to a dependently typed setting.

% Let us consider a simple example: X.690 DER Boolean values.
% The BER require that Boolean values consists of a single octet
% with \texttt{FALSE} represented by the setting all bits to 0, and the DER further
% stipulates that \texttt{TRUE} be represented by setting all bits to 1.
% We represent these constraints as follows.

% \begin{code}
% module BoolExample where
%   data BoolRep : Bool → UInt8 → Set where
%     falseᵣ : BoolRep false (UInt8.fromℕ 0)
%     trueᵣ  : BoolRep true (UInt8.fromℕ 255)
%   record BoolValue (@0 bs : List UInt8) : Set where
%     constructor mkBoolValue
%     field
%       v     : Bool
%       @0 b  : UInt8
%       @0 vᵣ : BoolRep v b
%       @0 bs≡ : bs ≡ [ b ]
% \end{code}

% \begin{enumerate}
% \item First, we define a binary relation \AgdaDatatype{BoolRep} that relates Agda
% \AgdaDatatype{Bool} values to the octet values specified by X.690 DER
% (\AgdaFunction{UInt8.fromℕ} converts a non-negative unbounded integer to its
% \AgdaFunction{UInt8} representation, provided Agda can verify automatically
% the given number is less than 256).

% \item Next, we define a record \AgdaDatatype{BoolValue} for the representation of
% the X.690 Boolean value itself.

% \begin{itemize}
% \item Each production rule of the grammar, such as \AgdaDatatype{BoolValue}, is
% represented by a type family of type
% \AgdaSymbol{@}\AgdaSymbol{0}\AgdaSpace{}\AgdaDatatype{List}\AgdaSpace{}\AgdaDatatype{UInt8}\AgdaSpace{}\AgdaSymbol{→}\AgdaSpace{}\AgdaPrimitive{Set},
% which we interpret as the type of predicates over byte-strings (we will
% explain the \AgdaSymbol{@}\AgdaSymbol{0} business shortly).

% \item The fields of the record are the Boolean value \AgdaField{v}, its
% byte-string representation \AgdaField{b}, a proof of type
% \AgdaDatatype{BoolRep}\AgdaSpace{}\AgdaField{v}\AgdaSpace{}\AgdaField{b}
% that \AgdaField{b} is the correct representation of \AgdaField{b}, and a
% proof that the byte-string representation of this terminal of the grammar
% is the singleton list consisting of \AgdaField{b} (written \AgdaFunction{[}\AgdaSpace{}\AgdaField{b}\AgdaSpace{}\AgdaFunction{]})
% \end{itemize}
% \end{enumerate}


% The \AgdaSymbol{@}\AgdaSymbol{0} annotations on types and fields indicate that
% the values are \emph{erased at run-time.}
% We do this for two reasons: to reduce the space and time overhead for
% executions of Aeres, and to serve as machine-enforced documentation
% delineating the parts of the formalization that are purely for the purposes of
% verification.
% \subsection{Parser}
% \label{sec:org2821fe9}

% \textbf{Challenge:} Next, we must design the parser.
% We desire that the parser by sound and complete \emph{by construction}.

% \textbf{Solution:} For our parser to be sound, when it succeeds we have it return a
% proof that the byte-string conforms to grammar. For completeness, when it
% fails we have it return a \emph{refutation} --- a proof that there is no possible
% way for the grammar to accept the given byte-string.
% The two of these together are captured nicely by the notion of
% \emph{decidability}, formalized in the Agda standard library as \AgdaDatatype{Dec}
% (we show a simplified, more intuitive version of this type below)
\begin{code}
module DecSimple where
  data Dec (A : Set) : Set where
    yes : A -> Dec A
    no  : not A -> Dec A
\end{code}

% Let us examine (a slightly simplified version of) the definition of
% \AgdaDatatype{Parser} used in Aeres.
% Below, module parameter \AgdaBound{S} is the type of the characters of the
% alphabet over which we have defined a grammar.

% \begin{code}
% module ParserSimple (S : Set) where
%   record Success (@0 A : List S → Set) (@0 xs : List S) : Set where
%     constructor success
%     field
%       @0 prefix : List S
%       read   : ℕ
%       @0 read≡ : read ≡ length prefix
%       value  : A prefix
%       suffix : List S
%       @0 ps≡    : prefix ++ suffix ≡ xs
%   record Parser (M : Set → Set) (@0 A : List S → Set) : Set where
%     constructor mkParser
%     field
%       runParser : (xs : List S) → M (Success A xs)
%   open Parser public
% \end{code}

% \begin{itemize}
% \item We first must specify what the parser returns when it succeeds.
% This is given by the record \AgdaDatatype{Success}.

% \begin{itemize}
% \item Parameter \AgdaBound{A} is the production rule (e.g.,
% \AgdaDatatype{BoolValue}), and \AgdaBound{xs} is the generic-character
% string which we parsed.
% Both are marked erased from run-time

% \item Field \AgdaField{prefix} is the prefix of our input string consumed by
% the parser.
% We do not need to keep this at run-time, however for the purposes of
% length-bounds checking we do keep its length \AgdaField{read} available
% at run-time.

% \item Field \AgdaField{value} is a proof that the prefix conforms to the
% production rule \AgdaBound{A}.

% \item Field \AgdaField{suffix} is what remains of the string after parsing.
% We of course need this at run-time to continue parsing any subsequent
% production rules.

% \item Finally, field \AgdaField{ps≡} relates \AgdaField{prefix} and
% \AgdaField{suffix} to the string \AgdaBound{xs} that we started with,
% i.e., they really are a prefix and suffix of the input.
% \end{itemize}

% \item Next, we define the type \AgdaDatatype{Parser} for parsers.
% \begin{itemize}
% \item Parameter \AgdaBound{M} is used to give us some flexibility in the type
% of the values returned by the parser.
% Almost always, it is instantiated with
% \AgdaDatatype{Logging}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaDatatype{Dec},
% where \AgdaDatatype{Logging} provides us lightweight debugging
% information.
% Parameter \AgdaBound{A} is, again, the production rule we wish to parse.

% \item \AgdaDatatype{Parser} consists of a single field \AgdaField{runParser},
% which is a dependently type function taking a character string
% \AgdaBound{xs} and returning
% \AgdaBound{M}\AgdaSpace{}\AgdaSymbol{(}\AgdaDatatype{Success}\AgdaSpace{}\AgdaBound{A}\AgdaSpace{}\AgdaBound{xs}\AgdaSymbol{)}
% (again, usually \AgdaDatatype{Logging}\AgdaSpace{}\AgdaSymbol{(}\AgdaDatatype{Dec}\AgdaSpace{}\AgdaSymbol{(}\AgdaDatatype{Success}\AgdaSpace{}\AgdaBound{A}\AgdaSpace{}\AgdaBound{xs}\AgdaSymbol{)}\AgdaSymbol{)})
% \end{itemize}
% \end{itemize}

% \subsubsection{Example}
% \label{sec:orgf89fca6}

% It is helpful to see an example parser.

%     \begin{AgdaAlign}
%     \begin{code}[hide]
% module BoolParseExample where
%   open import Aeres.Data.X690-DER.Boool.Properties
%   open import Aeres.Data.X690-DER.Boool.TCB
%   import      Aeres.Grammar.Definitions
%   import      Aeres.Grammar.Parser
%   open Aeres.Grammar.Definitions UInt8
%   open Aeres.Grammar.Parser      UInt8
%   open Aeres.Prelude
%     using (Dec ; yes ; no)
%     \end{code}

%     \begin{code}
%   private
%     here' = "X690-DER: Bool"
  
%   parseBoolValue : Parser (Logging ∘ Dec) BoolValue
%   runParser parseBoolValue [] = do  {- 1 -}
%     tell $ here' String.++ ": underflow"
%     return ∘ no $ λ where
%       (success prefix read read≡ value suffix ps≡) →
%         contradiction (++-conicalˡ _ suffix ps≡) (nonempty value)
%   runParser parseBoolValue (x ∷ xs) {- 2 -}
%     with x ≟ UInt8.fromℕ 0 {- 3 -}
%   ... | yes refl =
%     return (yes (success _ _ refl (mkBoolValue _ _ falseᵣ refl) xs refl))
%   ... | no x≢0
%     with x ≟ UInt8.fromℕ 255 {- 3 -}
%   ... | yes refl =
%     return (yes (success _ _ refl (mkBoolValue _ _ trueᵣ refl) xs refl))
%   ... | no  x≢255 = do {- 4 -}
%     tell $ here' String.++ ": invalid boolean rep"
%     return ∘ no $ λ where
%       (success prefix _ _ (mkBoolValue v _ vᵣ refl) suffix ps≡) → ‼
%         (case vᵣ of λ where
%           falseᵣ → contradiction (∷-injectiveˡ (sym ps≡)) x≢0
%           trueᵣ  → contradiction (∷-injectiveˡ (sym ps≡)) x≢255)
%     \end{code}
%     \end{AgdaAlign}

% \begin{enumerate}
% \item When the input string is empty, we emit an error message, then return a
% proof that there is no parse of a \AgdaDatatype{BoolValue} for the empty
% string

% We use Agda's \AgdaKeyword{do}-notation to sequence our operations

% \item If there is at least one character, we check
% \item whether it is equal to 0 or 255.
% If so, we affirm that this conforms to the grammar.
% \item If it is not equal to either, we emit an error message then return a
% parse refutation: to conform to \AgdaDatatype{BoolValue}, our byte must
% be either 0 or 255.
% \end{enumerate}

% \subsubsection{Backtracking}
% \label{sec:orgb054f08}

% Although backtracking is not required to parse X.509, our parser has been
% implemented with some backtracking to facilitate the formalization.
% For an example, the X.690 specification for \AgdaDatatype{DisplayText}
% states it may comprise an \AgdaDatatype{IA5String},
% \AgdaDatatype{VisibleString}, \AgdaDatatype{VisibleString}, or
% \AgdaDatatype{UTF8String}.
% In the case that the give byte-string does not conform to \AgdaDatatype{DisplayTex}
% providing a refutation is easier when we have direct evidence that it fails
% to conform to each of these.

%     \begin{AgdaAlign}
%     \begin{code}[hide]
% module DisplayTextExample where
%   open import Aeres.Data.X509.DisplayText.TCB
%   open import Aeres.Data.X509.IA5String
%   open import Aeres.Data.X509.Strings
%   open import Aeres.Data.X690-DER.TLV
%   import      Aeres.Grammar.Parser 
%   open Aeres.Grammar.Parser UInt8
%   open Aeres.Prelude
%     using (Dec ; yes ; no)
%     \end{code}
%     \begin{code}
%   private
%     here' = "X509: DisplayText"
  
%   parseDisplayText : Parser (Logging ∘ Dec) DisplayText
%   runParser parseDisplayText xs = do
%     no ¬ia5String ← runParser (parseTLVLenBound 1 200 parseIA5String) xs
%       where yes b → return (yes (mapSuccess (λ {bs} → ia5String{bs}) b))
%     no ¬visibleString ← runParser (parseTLVLenBound 1 200 parseVisibleString) xs
%       where yes b → return (yes (mapSuccess (λ {bs} → visibleString{bs}) b))
%     no ¬bmp ← runParser (parseTLVLenBound 1 200 parseBMPString) xs
%       where yes b → return (yes (mapSuccess (λ {bs} → bmpString{bs}) b))
%     no ¬utf8 ← runParser (parseTLVLenBound 1 200 parseUTF8String) xs
%       where yes u → return (yes (mapSuccess (λ {bs} → utf8String{bs}) u))
%     return ∘ no $ λ where
%       (success prefix read read≡ (ia5String x) suffix ps≡) →
%         contradiction (success _ _ read≡ x _ ps≡) ¬ia5String
%       (success prefix read read≡ (visibleString x) suffix ps≡) →
%         contradiction (success _ _ read≡ x _ ps≡) ¬visibleString
%       (success prefix read read≡ (bmpString x) suffix ps≡) →
%         contradiction (success _ _ read≡ x _ ps≡) ¬bmp
%       (success prefix read read≡ (utf8String x) suffix ps≡) →
%         contradiction (success _ _ read≡ x _ ps≡) ¬utf8
%       \end{code}
%       \end{AgdaAlign}
% \section{Complete and Secure Parsing}
% \label{sec:org0321583}
% Completeness of the parser is by construction, and straightforward to explain:
% given a byte-string, if it conforms to the grammar then the parser accepts the
% byte-string. The heart of the proof is proof by contradiction (which is
% constructively valid, since the parser is itself evidence that conformance to
% the grammar is decidable): suppose the parser rejects a string which conforms
% to the grammar. Then, this rejection comes with a refutation of the
% possibility that the string conforms with the grammar, contradicting our
% assumption.
% When it comes to security, we also care that the grammar is \emph{unambiguous},
% by which we mean that there is at most one way in which the grammar might be
% parsed.
% This is formalized as \AgdaFunction{UniqueParse} below
%   \begin{AgdaAlign}
%   \begin{code}[hide]
% module CompSec (S : Set) where
%   open import Aeres.Grammar.Parser S
%   open Aeres.Prelude
%     using (Dec ; yes ; no)
%   \end{code}
%   \begin{code}
%   Unique : Set → Set
%   Unique P = (p₁ p₂ : P) → p₁ ≡ p₂
%   UniqueParse : (List S → Set) → Set
%   UniqueParse A = ∀ {@0 xs} → Unique (Success A xs)
%   \end{code}
%   We have a lemma that establishes a sufficient condition for when
%   \AgdaFunction{UniqueParse} holds, whose premises are stated only in terms of
%   properties of the grammar itself.
%   These properties are:
%   1. Any two witness[fn::By which we mean inhabitants of a type, when we interpret that type as a proposition under the Curry-Howard isomorphism]
%      that a given string conforms to the grammar are equal (\AgdaFunction{Unambiguous}), and
%   2. If two prefixes of the same string conform to the grammar, those prefixes are equal (\AgdaFunction{NonNesting})
%   \begin{code}
%   Unambiguous : (A : List S → Set) → Set
%   Unambiguous A = ∀ {xs} → Unique (A xs)
%   NonNesting : (A : List S → Set) → Set
%   NonNesting A =
%     ∀ {xs₁ ys₁ xs₂ ys₂}
%     → (prefixSameString : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
%     → (a₁ : A xs₁) (a₂ : A xs₂) → xs₁ ≡ xs₂
%   module _ {A : List S → Set} (uA : Unambiguous A) (nnA : NonNesting A) where
%     @0 uniqueParse : UniqueParse A
%     uniqueParse p₁ p₂
%     {- = ... -}
%     \end{code}
%     \begin{code}[hide]
%       with ‼ nnA (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂))) (Success.value p₁) (Success.value p₂)
%     ... | refl
%       with ‼ Lemmas.++-cancel≡ˡ (Success.prefix p₁) _ refl (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂)))
%     ... | refl
%       with ‼ (trans (Success.read≡ p₁) (sym (Success.read≡ p₂)))
%     ... | refl
%       with ‼ ≡-unique (Success.read≡ p₂) (Success.read≡ p₁)
%       |    ‼ ≡-unique (Success.ps≡ p₂) (Success.ps≡ p₁)
%     ... | refl | refl
%       with ‼ uA (Success.value p₁) (Success.value p₂)
%     ... | refl = refl
%   \end{code}
%   This finally brings us to the statement and proof of complete and secure parsing.
%   \begin{code}
%   Yes_And_ : {P : Set} → Dec P → (P → Set) → Set
%   Yes (yes pf) And Q = Q pf
%   Yes (no ¬pf) And Q = ⊥
%   CompleteParse : (A : List S → Set) → Parser Dec A → Set
%   CompleteParse A p =
%     ∀ {bs} → (v : Success A bs) → Yes (runParser p bs) And (v ≡_)
%   module _ {A : List S → Set}
%     (uA : Unambiguous A) (nnA : NonNesting A) (parser : Parser Dec A)
%     where
%     @0 completeParse : CompleteParse A parser
%     completeParse{bs} v
%       with runParser parser bs
%     ... | (yes v')  = uniqueParse uA nnA v v'
%     ... | no ¬v     = contradiction v ¬v
%   \end{code}
%   \end{AgdaAlign}
% \begin{enumerate}
% \item We define an auxiliary predicate \AgdaFunction{Yes\_And\_} over decisions,
% expressing that the decision is \AgdaInductiveConstructor{yes} and
% the predicate \AgdaBound{Q} holds for the affirmative proof that comes with
% it.
% \item The predicate \AgdaFunction{CompleteParse} is defined in terms of
% \AgdaFunction{Yes\_And\_}, expressing that if \AgdaBound{v} is a witness that
% some prefix of \AgdaBound{bs} conforms to \AgdaBound{A}, then the parser
% returns in the affirmative and the witness it returns is equal to
% \AgdaBound{v}.
% \item We then prove the property \AgdaFunction{CompleteParse} under the
% assumption that \AgdaBound{A} is \AgdaFunction{Unambiguous} and
% \AgdaFunction{NonNesting}.
% The proof proceeds by cases on the result of running the parser on the
% given string.
% \begin{itemize}
% \item If the parser produces an affirmation, we appeal to lemma
% \AgdaFunction{uniqueParse}.
% \item If the parser produces a refutation, we have a
% \AgdaFunction{contradiction}
% \end{itemize}
% \end{enumerate}
% \section{Semantic Checks}
% \label{sec:orgcf94a3f}
% Some properties that we wish to verify are not as suitable for formalization
% as part of the grammar.
% For example, the X.509 specification requires that the signature algorithm
% field of the TBS certificate matches the signature algorithm listed in the
% outer certificate --- a highly non-local property.
% Aeres checks such properties after parsing.
% For each of these, we first write a specification of the property, then a
% proof that that property is \emph{decidable}.
% This proof is itself the function that we call to check whether the property
% holds, and interpreted as such, it is sound and complete by construction for
% the same reasons that our parser is.
%   \begin{AgdaAlign}
% \begin{code}[hide]
% module SemanticExample where
%   open Aeres.Prelude using (Dec ; yes ; no)
%   open import Aeres.Data.X509
%   import      Aeres.Grammar.Definitions
%   open Aeres.Grammar.Definitions UInt8
% \end{code}
% \begin{code}
%   SCP1 : ∀ {@0 bs} → Cert bs → Set
%   SCP1 c = Cert.getTBSCertSignAlg c ≡ Cert.getCertSignAlg c
%   scp1 :  ∀ {@0 bs} (c : Cert bs) → Dec (SCP1 c)
%   scp1 c =
%     case (proj₂ (Cert.getTBSCertSignAlg c) ≋? proj₂ (Cert.getCertSignAlg c)) ret (const _) of λ where
%       (yes ≋-refl) → yes refl
%       (no ¬eq) → no λ where refl → contradiction ≋-refl ¬eq
% \end{code}
%   \end{AgdaAlign}


\begin{figure}[t]
    \centering
    \begin{code}
  prog : (St -> Maybe Wr) -> RWS Unit
  prog g = pass inner where
    inner : RWS (Unit times (List Wr -> List Wr))
    inner = do  m <- gets g
                maybe  (\ w -> do  tell [ w ]
                                   return (unit , \ _ -> []))
                       (return (unit , \ x -> x ++ x)) m
    \end{code}
    \caption{An example effectful program}
    \label{fig:ex-prog1}
  \end{figure}