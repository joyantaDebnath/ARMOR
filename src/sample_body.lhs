% -*- eval: (flyspell-mode); TeX-master: "index.lhs"; reftex-default-bibliography: ("../references.bib"); -*-
\section{Introduction}
\label{sec:introduction}

Interactive theorem provers (ITPs) based on dependent type theory provide a
flexible way to formally verify program properties, as they unify the
language of specification and computation into an expressive pure functional
programming language~\cite{SU06_Lectures-on-the-Curry-Howard-Isomorphism}.
By virtue of referential transparency, properties of pure functions (those
without side effects) can be proven with equational reasoning.
However, when the computation of interest is inherently effectful, other
techniques may be required.
For example, in the case of distributed systems, participants
perform state updates, emit messages, and invoke subroutines that may throw
exceptions; the network's ability to tolerate faults rests upon participants'
behaviors.

One approach to reasoning about effects, described by
Swierstra and Baanen~\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects},
is to model the abstract syntax tree (AST) of the effectful program with a
datatype and assign to this type both an operational semantics and
\emph{predicate transformer} semantics (PTS).
PTS provides a structured way for reasoning about effectful code
\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects,SWSCL13_Verifying-Higher-Order-Programs-Dijkstra-Monad},
reducing the goal of showing a given postcondition \(P\) holds of a program
\(m\) to proving the  weakest-precondition \(\mathit{wp}\ m\ P\) of \(P\)
w.r.t.\ that program.
As \(\mathit{wp}\ m\) maps \emph{arbitrary} postconditions to preconditions,
we may view it as giving a meaning (semantics) to \(m\) in terms of functions
from postconditions to preconditions (predicate transformers).

\paragraph*{Contributions}
In this paper, we describe a generic Agda framework for manually verifying
effectful programs using PTS.
This framework is designed to reduce the mental overhead for proof engineers
(hereafter, ``users'')
by tailoring the phrasing of intermediate proof obligations.
In particular, our framework allows directly assigning predicate transformers
not only to expected effectful operations, but also to monadic bind and pure
operations for branching.
Careful phrasing of proof obligations also facilitates a limited form of proof
synthesis when the goal type can be decomposed with a unique type-correct
constructor.

Our framework was developed as a part of our efforts to verify safety properties
of an implementation of \textsc{LibraBFT} in Agda.
We have previously reported on some aspects of that work~\cite{NASAFM-2022}.
Details of the work presented in this paper are available in the same open source
repository~\cite{librabft-agda}.
\textsc{LibraBFT} (a.k.a. \textsc{DiemBFT})~\cite{libra-2019-06-28} is a
real-world Byzantine-fault tolerant consensus protocol.
However, we believe the techniques we describe generalize to other domains and
ITPs, including those with greater levels of
automation~\cite{AHMMPPRS17_Dijkstra-Monads-for-Free}.


\section{Proof Engineering with Predicate Transformers}
\label{sec:proof-engineering-pts}

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

As motivation, we consider the small effectful program |prog| in
Figure~\ref{fig:ex-prog1}.
The type of |prog g| is |RWS Unit|\footnote{Many names in the
  repository---including |RWS|---have |AST| suffixes for disambiguation, which
  are usually omitted in this paper for brevity.}, which says that it produces
no interesting values (|Unit| is the unitary type) and that it uses the
effects of the \emph{reader, writer, state} monad~\cite{RWS}: it may read and
write to state of type |St|, emit messages of type |Wr|, and read from an
environment of type |Ev|.
To avoid confusion, we say that an effectful program of type |RWS A|
\emph{returns} or \emph{produces} a value of type |A|, as opposed to
\emph{emitting} messages (always of type |List Wr|).
We assume the reader is familiar with Haskell-style |do|-notation and the basics
of dependent type theory; we explain Agda-specific syntax and conventions as
they are introduced.

Given a function |g : St -> Maybe Wr| that may compute a message from a
state, |prog g| calls |pass| on |inner|; |pass| has the effect of
applying the function of type
|List Wr -> List Wr| returned by |inner| to the messages emitted
by |inner|, the result of which is then emitted by |prog g|.
In |inner|, we use |gets| to apply |g| to the current state, binding the result as
|m : Maybe Wr|.
Using the |maybe| operation to scrutinize |m|,
if a message item |w : Wr| is produced by |g| (i.e., |m == just w|), then we emit it and
return a constant function that returns the empty list, in effect erasing what
was just emitted.
In case |m == nothing|, |prog g| returns a function that concatenates a list of
messages with itself.

The operational semantics for |RWS| programs is given by |runRWS|, whose type is
shown below (the definition of |runRWS| is in module |Dijkstra.AST.RWS|; module
|X.Y.Z| lives in \texttt{src/X/Y/Z.agda} in~\cite{librabft-agda}).

\begin{code}
Input     = Ev times St
Output A  = A times St times List Wr

runRWS : forall {A} -> RWS A -> Input -> Output A
\end{code}
To run a program of type |RWS A|, |runRWS| requires as input an environment
value and prestate, and the result of executing such a program is a triple
consisting of a value of type |A|, a poststate, and a list of emitted messages.

\subsubsection*{Direct Approach to Proof Engineering}
\label{sec:prog-direct}

Suppose we are tasked with verifying that |prog|
satisfies postcondition |ProgPost| below, which expresses the property that the
prestate and poststate are equal and that there are no outputs.
\begin{code}
ProgPost : Input -> Output Unit -> Set
ProgPost (e1 , s1) (u1 , s2 , o) = s1 == s2 times 0 == length o 
\end{code}
(|Set| is a classifier for types in Agda; the type of |ProgPost|
says that it is a relation between inputs to, and outputs of,
programs of type |RWS Unit|.)

Attempting the proof directly, we begin with:
\begin{code}
progPost : forall g i -> ProgPost i (runRWS (prog g) i)
progPost g (e , s) = ?
\end{code}
where the |?| marks a hole in the proof.
When Agda unfolds the proof obligation at the hole,
the result is unwieldy!
To give an idea, here is (a cleaned-up version of) the obligation for
just the second conjunct of the postcondition |ProgPost|:
\begin{code}
  0 ==  length (snd (fst (runRWS
           (maybe (return (unit , \ x -> x ++ x))
             (\ w -> tell [ w ] >> return (unit , \ _ -> [])) (g s)) (e , s)))
           (snd (snd (runRWS
             (maybe (return (unit , \ x -> x ++ x))
               (\ w -> tell [ w ] >> return (unit , \ _ -> [])) (g s)) (e , s)))))
\end{code}
\noindent
(The proofs in this section are in the |Dijkstra.AST.Examples.PaperIntro| module with more detail,
including the entire goal for the hole above in gory detail that a user attempting a direct
proof encounters.)

This obligation has parts of the program text from |inner| repeated
\emph{twice,} once for the function it returns and once for the messages it
emits.
The issue is that the execution of |prog| is stuck on the branching operation
|maybe| whose scrutinee |g s| is not in weak head normal form (that is, it is
not of the form |nothing| or |just x|).
Because our proof obligation refers directly to the evaluation of |prog|
twice, the continuation in |inner| is also referenced twice.

One way to proceed in this case is
to use the |with| keyword to abstract over the expression blocking progress:
\begin{code}
progPost g (e , s) with g s
...  | nothing  = ?
...  | just w   = ?
\end{code}
with the result that the new subgoals this generates (|s == s times 0 == 0| in
both cases) are much easier to understand than the original goal.

Though |prog| is a small example, and the property we wish to verify is
relatively simple, the preceding discussion illustrates difficulties that are
greatly magnified as the complexity of the task increases.
First, proof obligations for ``stuck'' code can explode in size, especially when
the code branches, making it difficult to read the proof state and identify
\emph{why} execution is stuck.
Second, once identified, using |with| to inspect the cases of the scrutinee of
branching code means recapitulating the effectful operations performed up to that point.
In the example considered above, there were no updates to the state |s| before
the |gets| operation was used, but had there been for example a preceding |puts
p| (for some |p : St -> St|), the user would instead have to write
|with g (p s)|.

\subsubsection*{Simplifying Proof Obligations with PTS}
Our Agda framework is designed to address these issues.
Following the general approach of Swierstra and
Baanen~\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects}, our framework
uses a datatype for the ASTs of effectful computations (|AST|,
Figure~\ref{fig:ast-gadt}); |RWS| is an instance of this datatype.
To prove that |ProgPost| holds of |prog|, we first prove a \emph{precondition}
obtained by the function
\begin{code}
predTrans : forall {A} -> RWS A -> (Output A -> Set) -> Input -> Set
\end{code}
which assigns to each |RWS| program (by induction over its AST) a function that
maps postconditions to preconditions.
Put another way, it gives each |RWS| program a \emph{semantics} as a
\emph{predicate transformer,} as it transforms predicates over |Output| types to
predicates over the |Input| type.

We begin our proof that precondition for |ProgPost| holds with:
\begin{code}
progPostWP : forall g i -> predTrans (prog g) (ProgPost i) i
progPostWP g (e , s) = ?
\end{code}
\noindent where the proof obligation at the hole is now much more understandable:
\begin{code}
(r : Maybe Wr) -> r == g s ->
  (nothing == r -> (o' : List Wr) -> o' == [] ->
     (s == s) times (length o' == 0))
  times  ((x1 : Wr) -> just x1 == r -> (r1 : Unit) -> r1 == unit ->
           (o' : List Wr) -> o' == [] -> (s == s) times (length o' == 0))  
\end{code}

The user's next few steps are entirely type
directed: introduce the premises of the implication to the context, then (because
this leaves us with a product) decompose the proof obligation into two
subobligations (the detailed commentary in |Dijkstra.AST.Examples.PaperIntro|
shows how to develop the proof largely automatcally using Emacs's Agda mode).
This yields:
\begin{code}
proj1 (progPostWP g (e , s) m mId) = ?
proj2 (progPostWP g (e , s) m mId) = ?
\end{code}

At this point, we note two things.
First, the framework has enabled us to alias |g s| as |m| (we 
choose the name |m|, rather than |r| as shown in the proof obligation, to
better match the local name in |prog|), and the remaining proof obligations
\emph{only} mention |m|.
Term |mId : m == g s| enables us to undo this aliasing as needed, as
dependent pattern matching on |mId| replaces |m| with |g s| in the proof state.
Recall that, in the direct proof above, |g s| was repeated in the proof
obligation. 
If we had a more complex expression as the scrutinee, it too would be repeated
in the direct proof---but in a proof using our framework, \emph{only the alias}
is repeated!
Second, and relatedly, in the direct approach, the user must
explicitly invoke |with| on the scrutinee |g s| in order to generate two
subobligations (one each for |nothing| and |just|).
With our framework, these two cases are \emph{already} present in the proof
obligation, in the form of a product of obligations in which, while proving each
component, the user assumes that the alias |m| is either |nothing| or |just w|
for some |w : Wr|.

The rest of the proof is similarly type-directed by the framework and is fairly
straightforward; see |Dijkstra.AST.Examples.PaperIntro| for the details.
Finally, having proved |progPostWP|, we can
obtain a proof of the desired postcondition by using |sufficient|, which is a proof
that the preconditions computed by |predTrans| are \emph{sufficient} for proving the
given postcondition for the given program.
\begin{code}
progPost : forall g i -> ProgPost i (runRWS (prog g) i)
progPost g i = sufficient (prog g) (ProgPost i) i (progPostWP g i)
\end{code}

\section{Framework for PTS}
\label{sec:pts-rws}

In this section, we describe our generic framework for modeling effectful
computations and reasoning about them with predicate transformer semantics.
We define a generalized algebraic datatype (GADT) for the ASTs of
effectful programs, parameterized by a collection of operations supplied by the
user.
To set up the framework for a particular set of effects, the user provides an
operational and predicate transformer semantics (PTS) for the operations, then
proves that these two semantics agree; this enables
verifying a postcondition by proving the sufficient
precondition generated by the PTS.
It is at the point of specifying the predicate transformer semantics that one
may tailor the computed proof obligations to suit one's needs, for example,
introducing aliasing or reducing the goal to some set of subgoals;
proof obligations can be rephrased in any convenient way,
provided the two semantics can be shown to agree.

\subsection{|AST|}
\label{sec:ast}

\begin{figure}[t]
  \begin{code}
record ASTOps : Set where
  field
    Cmd     : (A : Set) -> Set
    SubArg  : {A : Set} (c : Cmd A) -> Set
    SubRet  : {A : Set} {c : Cmd A} (r : SubArg c) -> Set
open ASTOps

data AST (OP : ASTOps) : Set -> Set where
  ASTreturn  : forall {A} -> A                              -> AST OP A
  ASTbind    : forall {A B} -> AST OP A -> (A -> AST OP B)  -> AST OP B
  ASTop      : forall {A} -> (c : Cmd OP A)
               -> (f : (r : SubArg OP c) -> AST OP (SubRet OP r))
                                                            -> AST OP A
  \end{code}
  \caption{Datatype for effectful code}
  \label{fig:ast-gadt}
\end{figure}

Figure~\ref{fig:ast-gadt} shows the definition of |AST|, the GADT for effectful
program ASTs (in Agda, |Set| is a classifier for types, and the sort |Set ->
Set| is for type constructors; to improve readability, our Agda code listings
omit universe levels~\cite{Agda22_Agda-Docs-Universe}).
These definitions are in the |Dijkstra.AST.Core| module.
We make the monadic \emph{unit} operation (|ASTreturn|) a constructor and, deviating from
the recipe of Hancock and Setzer~\cite{HS00_Interactive-Programs-in-DTT}, we also
make the \emph{bind} operation (|ASTbind|) a constructor.
In Section~\ref{sec:ast-pts}, we will see that, by making the bind operator a
constructor, we avoid the need for an additional lemma to assign a predicate
transformer to composite computations (such as needed by Swierstra and
Baanen~\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects}, \S 4).
The last constructor, |ASTop|, enables us to describe effectful operations.

|AST| is parameterized by a value of type |ASTOps|, which comprises three
fields that describe the syntax of effectful operations.
First, |Cmd| is the family of types for commands, indexed by a type |A| for the
result value of the command.
Next, |SubArg| is the family of argument types for the subcomputations (if any)
of a given command.
Finally, |SubRet| is the family of types for values returned by subcomputations
(these need not be the same as the given type |A| for the result type of the
whole command).
Curly braces around bound type variables indicate that we wish Agda to
infer instantiations of that type argument.


The |ASTop| constructor of |AST| takes as arguments a
command |c| and a |(r : SubArg OP c)|-indexed family |f| of subcomputations of the
command, each producing values of type |SubRet OP r|, where the type of values
produced by the whole operation is |A|.
As |AST| has an explicit sequencing constructor (|ASTbind|), we understand |f|
not as a continuation for the next computation, but a family of computations
subordinate to the command itself (see Example~\ref{ex:ast-rws-op}).
These changes give us the flexibility to encode complex operations as primitive
nodes of the AST, enabling us to assign bespoke predicate transformers to them
when we reason about the behaviors of the programs in which they occur.

\begin{figure}[t]
  \begin{subfigure}{0.48\linewidth}
    \begin{code}
record ASTTypes : Set where
  field
    Input  : Set
    Output : (A : Set) -> Set

  Exec : Set -> Set
  Exec A = Input -> Output A      
    \end{code}
  \end{subfigure}%
  \begin{subfigure}{0.50\linewidth}
    \begin{code}
record  ASTOpSem  (OP : ASTOps)
          (Ty : ASTTypes) : Set where
  open ASTTypes Ty
  field
    runAST : forall {A}  -> AST OP A
                         -> Exec A      
    \end{code}
  \end{subfigure}
  \caption{Operational semantics for an |AST|}
  \label{fig:ast-opsem}
\end{figure}

\paragraph*{Operational Semantics}
Figure~\ref{fig:ast-opsem} shows what is required for \emph{running} |AST|
programs. 
First, the user must supply the |Input| type and
|Output| type family (type argument |A| is the type of values returned by the
program).
The type of \emph{executions} of a program producing values of type |A| is a
function |Exec A| that maps an |Input| to an |Output A|.
The user then provides an instance of |ASTOpSem| for
the desired operations and types.
The only field of |ASTOpSem| is |runAST|, a function that transforms the AST of
an effectful computation producing values of type |A| to a function of type
|Exec A|.

\begin{example}
  \label{ex:ast-rws-op}
  \begin{figure}[t]
    \centering
    \begin{code}
data RWSCmd (A : Set) : Set where
  RWSgets :  (g : St -> A) -> RWSCmd A
  RWSpass :  RWSCmd A
  ...
RWSSubArg : {A : Set} (c : RWSCmd A) -> Set
RWSSubArg (RWSgets g)  = Void
RWSSubArg RWSpass      = Unit
...
RWSSubRet : {A : Set} {c : RWSCmd A} (r : RWSSubArg c) -> Set
RWSSubRet {_} {RWSgets g}  ()
RWSSubRet {A} {RWSpass}    _ = A times (List Wr -> List Wr)
...
RWSOps : ASTOps
Cmd RWSOps     = RWSCmd
SubArg RWSOps  = RWSSubArg
SubRet RWSOps  = RWSSubRet
    \end{code}
    \caption{Commands and operational types for |RWS|}
    \label{fig:ast-rws-op}
  \end{figure}

  Figure~\ref{fig:ast-rws-op} sketches the instantiation of |ASTOps| for
  modeling |RWS| programs.
  Due to space constraints, we only show two operations and omit the (straightforward)
  definition of the operational semantics; for the full definition,
  see module |Dijkstra.AST.RWS|.
  |RWS| operations |gets : forall {A} -> (St -> A) -> A| and |pass : forall {A} -> RWS
  (A times  (List Wr -> List Wr)) -> RWS A| are modeled with constructors
  |RWSgets| and |RWSpass|.
  |RWSgets| has no |RWS| subcomputations, so the arity (given by
  |RWSubArg (RWSgets g)|) is |Void| (the empty type).
  |RWSpass| has a single subcomputation (so the arity is |Unit|); the type it
  returns is |A times (List Wr -> List Wr)|, where |A| is the type of the entire
  |RWSpass| computation.
  The |ASTTypes| instance for |RWS| (not shown)
  sets the fields to the definitions of |Input| and |Output| given in
  Section~\ref{sec:proof-engineering-pts}.
\end{example}

\subsection{Predicate Transformer Semantics}
\label{sec:ast-pts}

\begin{figure}[t]
  \begin{code}
record ASTTypes : Set where
  ...
  Pre          = Input -> Set
  Post A       = Output A -> Set
  PredTrans A  = Post A -> Pre

record ASTPredTrans (OP : ASTOps) (Ty : ASTTypes) : Set₂ where
  open ...   -- opens to avoid explicit references are omitted hereafter
  field
    returnPT  : forall {A} -> A        -> PredTrans A
    bindPT    : forall {A B} -> (A -> PredTrans B) -> Input
                -> Post B              -> Post A
    opPT      : forall {A} -> (c : Cmd OP A)
                -> ((r : SubArg OP c)  -> PredTrans (SubRet OP r))
                                       -> PredTrans A

  predTrans : forall {A} -> AST OP A   -> PredTrans A
  predTrans (ASTreturn x) P i  = returnPT x P i
  predTrans (ASTbind m f) P i  = predTrans m (bindPT (predTrans . f) i P) i
  predTrans (ASTop c f) P i    = opPT c (predTrans . f) P i
  \end{code}
  \caption{Predicate transformer semantics for an |AST|}
  \label{fig:ast-pts}
\end{figure}

We can now define what it means to give a PTS to an |AST|.
It is at \emph{this step} where the proof engineer instantiating the framework
decides what proof obligations are generated for effectful operations and
sequencing; we will see this more concretely in Example~\ref{ex:ast-rws-pts}.
The step that follows, described in Section~\ref{sec:ast-suff}, requires showing
that PTS \emph{agree} with the operational semantics. 

In Figure~\ref{fig:ast-pts}, we continue the listing of the record
|ASTTypes|, which includes some definitions for convenience:
|Pre| and |Post| are the definitions of preconditions and
postconditions, and |PredTrans| defines a predicate transformer as a function
that produces preconditions from postconditions.
A user wishing to assign a PTS to a particular choice of AST operations |OP| and
input and output types |Ty| provides three items, expressed as the three fields
of |ASTPredTrans|.

Each field  of |ASTPredTrans| corresponds to a clause of the definition of
|predTrans|, the function that assigns a predicate transformer to |AST OP| programs.
Field |returnPT| is a family of predicate transformers for |ASTreturn|.
Field |bindPT| is for composite operations of the form |ASTbind m f :
AST OP B|.
Its purpose is to take a postcondition |P : Post B| for the entire computation
and rephrase it as a postcondition (of type |Post A|) for |m : AST OP A|.
The definition of |bindPT| supplied by the user should use the assumed
family of predicate transformers (the argument of type |A -> PredTrans B|) to
express a sufficient precondition of |f| to prove |P|, and then make that
precondition the \emph{postcondition} for |m| (see
Example~\ref{ex:ast-rws-pts}). 
Field |opPT| gives a predicate transformer for every command |c : Cmd OP
A|, given a family of predicate transformers for the subcomputations (if any)
given as arguments to that command.

Given these pieces, the function |predTrans| that assigns a predicate
transformer to every |m : AST OP A| is defined by induction over |m|.
We again call attention to the fact that, because our |AST| type has the
constructor |ASTbind|, users can tailor a convenient predicate transformer to
assign to composite operations directly, rather than requiring an explicit
compositionality lemma.

\begin{example}
  \label{ex:ast-rws-pts}
  \begin{figure}[t]
    \begin{code}
RWSbindPost : (outs : List Wr) {A : Set} -> Post A -> Post A
RWSbindPost outs P (x , st , outs') = P (x , st , outs ++ outs')

RWSpassPost : forall {A} -> Post A -> Post (A times (List Wr → List Wr))
RWSpassPost P ((x , h) , s , o) = forall o' -> o' == h o → P (x , s , o')

RWSPT : ASTPredTrans RWSOps RWSTypes
returnPT  RWSPT x P (e , s) = P (x , st, [])
bindPT    RWSPT f (e , s0) P (x , s1 , o) =
  forall r -> r == x -> f r (RWSbindPost o P) (e , s1)
opPT      RWSPT    (RWSgets g)  f P (e , s) = P (g s , s , [])
opPT      RWSPT{A} RWSpass      f P (e , s) = f unit (RWSpassPost P) (e , s)
    \end{code}
    \caption{Predicate transformer semantics for |RWS|}
    \label{fig:ast-rws-pts}
  \end{figure}

  Figure~\ref{fig:ast-rws-pts} shows the instantiation of |ASTPredTrans|
  (omitting operations other than |RWSgets| and |RWSpass|).
  For |returnPT|, the precondition we return is that the postcondition |P|
  holds for the returned value, the current state, and an empty list of messages
  (there are no state changes or messages emitted).
  The \emph{post}condition we return for |bindPT| is trickier: |P| is the
  postcondition we wish to hold for |ASTbind m1 m2|, and what we return is the
  postcondition that should hold of |m1| to establish this.
  Because |x| (the result of executing |m1|) may be instantiated to an unwieldy
  expression, we alias |x| as |r| and give this to the predicate transformer |f|
  that is assigned to |m2|.
  We also have that |m1| emitted |o| as output, so we use |RWSbindPost| to express
  that the postcondition should hold for the result of appending these to the
  emitted messages of |m2|.

  We treat |RWSgets| similarly to |returnPT|: we require the postcondition to
  hold of |g s|, where |g| is the user-supplied getter function.
  For |RWSpass|, we apply the predicate transformer |f| assigned to the
  subcomputation (think |inner| from Section~\ref{sec:proof-engineering-pts}) to
  |RWSpassPost P|, which says that postcondition |P| holds when we modify the
  output of the subcomputation with the returned function |h : List Wr -> List
  Wr|.

\end{example}

\subsection{Agreement of Semantics}
\label{sec:ast-suff}

In Sections~\ref{sec:ast} and \ref{sec:ast-pts}, we described
how to assign operational and predicate transformer semantics to a set of
effectful operations.
We now describe how to show that two such semantics \emph{agree}.
The obligations to show one direction of this agreement are
formalized by |ASTSufficientPT|, shown in Figure~\ref{fig:ast-suff}.

\begin{figure}
  \centering
  \begin{code}
record ASTSufficientPT {OP : ASTOps} {Ty : ASTTypes}
  (OpSem : ASTOpSem OP Ty) (PT : ASTPredTrans OP Ty) : Set where

  Sufficient : (A : Set) (m : AST OP A) -> Set
  Sufficient A m = forall P i -> (wp : predTrans m P i) -> P (runAST m i)

  field
    returnSuf  :  forall {A} x -> Sufficient A (ASTreturn x)
    bindSuf    :  forall {A B} (m : AST OP A) (f : A -> AST OP B)
                  -> Sufficient A m -> (forall x -> Sufficient B (f x))
                  -> Sufficient B (ASTbind m f)
    opSuf      :  forall {A}  -> (c : Cmd OP A)(f : Resp OP c -> AST OP (Sub OP c))
                              -> (forall r -> Sufficient (Sub OP c) (f r))
                              -> Sufficient A (ASTop c f)

  sufficient : forall {A} -> (m : AST OP A) -> Sufficient A m
  sufficient = ...
  \end{code}
  \caption{Sufficiency lemmas for operational semantics and PTS}
  \label{fig:ast-suff}
\end{figure}

|Sufficient| says that,
for a given effectful program |m : AST OP A|, the predicate transformer
|predTrans m| returns, for every postcondition |P|, a precondition
\emph{sufficient} for proving that, for any input |i|, |P| is true of the result
obtained from running |m| with input |i| using the operational semantics;
henceforth we abbreviate this and say that \emph{the predicate transformer for
  |m| is sufficient}.
To prove sufficiency, our framework imposes three obligations on the user,
corresponding to the three constructors of |AST|; they are as follows.
\begin{enumerate}
\item Instantiating the field |returnSuf| requires that the predicate
  transformer corresponding to |ASTreturn x| (for any |x : A|) is sufficient. 

\item For field |bindSuf|, the user assumes that the predicate transformers
  assigned to |m| and (all instances of) |f| are sufficient, and must prove that
  the predicate transformer obtained from |ASTbind m f| is sufficient.
  
\item Finally, for field |opSuf|, assuming that, for an arbitrary command
  |c| and subcomputation |f|, the predicate transformer obtained from the result
  of running |f| with any possible response value is sufficient, the user must
  show that the predicate transformer for |ASTop c f| is sufficient.
\end{enumerate}

\noindent With these three obligations met, the proof of sufficiency
(|sufficient|) proceeds by a straightforward induction.

The other direction of agreement is captured by |Necessary| (not shown), which says that,
for an effectful program |m : AST OP A|, for every postcondition |P| and
input |i|, if the output achieved by running |m| on |i| satisfies |P|, then |i|
satisfies the precondition returned by |predTrans m P|.
Similar to |Sufficient|, the framework imposes an obligation on the user for
each constructor of |AST|, and uses these to prove |Necessary|; details can be
found in module |Dijstra.AST.Core|.

\section{Generic Branching Operations}
\label{sec:branching}

Branching operations may be used \emph{in} effectful code, but do not
\emph{themselves} have effects.
Therefore, our framework can \emph{generically} extend any
set of commands and their predicate transformer semantics to include a few
common branching operations (see module |Dijkstra.AST.Core|), re-expressing their proof obligations
to avoid the issues outlined in
Section~\ref{sec:prog-direct}.

\subsection{Branching Commands}
\label{sec:branch-cmd}

\begin{figure}[t]
  \begin{code}
data BranchCmd (A : Set) : Set where
  BCif      : Bool                         -> BranchCmd A
  BCeither  : forall {B C}  -> Either B C  -> BranchCmd A
  BCmaybe   : forall {B}    -> Maybe B     -> BranchCmd A

BranchSubArg : forall {A} -> BranchCmd A -> Set
BranchSubArg (BCif x)            = Bool
BranchSubArg (BCeither{B}{C} x)  = Either B C
BranchSubArg (BCmaybe {B} x)     = Maybe B

BranchSubRet : forall {A} {c : BranchCmd A} -> BranchSubArg c -> Set
BranchSubRet{A} _ = A

module ASTExtension (O : ASTOps) where

  BranchOps : ASTOps
  Cmd  BranchOps A = Either (Cmd O A) (BranchCmd A)
  SubArg BranchOps     (left x)      = SubArg O x
  SubArg BranchOps     (right y)     = BranchSubArg y
  SubRet BranchOps{_}  {left x}   r  = SubRet O r
  SubRet BranchOps{_}  {right y}  r  = BranchSubRet r

  unextend : ∀ {A} -> AST BranchOps A -> AST O A
  unextend = ...
  \end{code}
  \caption{Extending |ASTOps| with branching commands}
  \label{fig:ast-op-branch}
\end{figure}

Figure~\ref{fig:ast-op-branch} shows how we model these branching commands,
similar to how we model effectful commands (\Cref{sec:ast}).
Datatype |BranchCmd| enumerates the branching commands (see module
|Dijkstra.AST.Branching|); so far, we support commands for Booleans (|BCif|),
coproducts (|BCeither|), and the |Maybe| type (|BCmaybe|).
Each constructor of |BranchCmd| takes the scrutinee (the subject of case
analysis) for the operation it models.
For |BranchSubArg|, the arity of the family of subcomputations
for a branching command is given by the type of the scrutinee (e.g.,
there are two subcomputations for |if|, so its arity is given by the two-element
type |Bool|).
Finally, for |BranchSubRet|, the type of result values for the subcomputations is
|A|, the type of result values for the entire computation.

|BranchOps| extends a given set of operations |O : ASTOps| with the
branching commands just described.
We take the set of command codes to the disjoint union of the command codes of
|O| and |BranchOps|, and extend the |SubArg| and |SubRet| fields
accordingly.
We also define the function |unextend| to traverse a program AST and remove all
branching commands; this is used in the developments discussed next for
extending existing operational and predicate transformer semantics to the
branching operations.

\begin{figure}[t]
  \centering
  \begin{code}
module OpSemExtension
  {O : ASTOps} {T : ASTTypes} (OpSem : ASTOpSem O T) where

  BranchOpSem : ASTOpSem BranchOps T
  runAST BranchOpSem m i = runAST OpSem (unextend m) i

module PredTransExtension
  {O : ASTOps} {T : ASTTypes} (PT : ASTPredTrans O T) where

  BranchPT  : ASTPredTrans BranchOps T
  returnPT  BranchPT           = returnPT PT
  bindPT    BranchPT           = bindPT   PT
  opPT      BranchPT (left x)  = opPT PT x
  opPT      BranchPT (right (BCif c)) f P i =
    (c == true -> f true P i) times (c == false -> f false P i)
  opPT      BranchPT (right (BCeither e)) f P i =
                   (forall l ->  e == left l   -> f (left l) P i)
            times  (forall r -> e == right r  -> f (right r) P i)
  opPT      BranchPT (right (BCmaybe m)) f P i =
                   (forall j ->  m == just j   -> f (just j) P i)
            times  (             m == nothing  -> f nothing  P i)
  \end{code}
  \caption{Operational and predicate transformer semantics for branching commands}
  \label{fig:ast-sem-branch}
\end{figure}

\subsubsection*{Semantics}
\label{sec:branching-semantics}

In Figure~\ref{fig:ast-sem-branch}, we assign
operational and predicate transformer semantics to |BranchOps|.
The operational semantics for the extended set of commands reduces to the
operational semantics |OpSem : ASTOpSem O T| for the base set of commands via
|unextend|, as shown by the definition of |BranchOpSem|.
For the predicate transformer semantics, the precondition returned for the given
postcondition |P| is expressed as a product of properties, where each component
of the product corresponds to a particular branch taken.
For example, for the case of |BCeither e| (where |e : Either B C|), the first
component of the product is for the case in which |e| is of the form |left l|
for some |l : B|.
Recall from Section~\ref{sec:proof-engineering-pts} that expressing the proof
obligation in this way means that: the proof state is often much more
comprehensible; the proof does not need to recapitulate (for example, using
|with|) the case distinction performed by the code being verified; and the
immediate next step in the proof effort is entirely type directed (copattern
matching generates the two subobligations).


\subsection{Semantic Agreement for Branching Operations}
\label{sec:branching-agree}

So far, we have augmented an arbitrary set of effectful operations with
branching commands and extended the operational and predicate transformer
semantics accordingly.
In this section, we describe our result showing that, if the original operational
and predicate transformer semantics agree---and furthermore the PTS satisfies a
certain monotonicity property, then the two extended semantics for branching
commands agree.
This ensures that the extension can be used to verify effectful code with
branching.
Furthermore, the monotonicity property is valuable in its own right when it is
easier to prove that the precondition for a postcondition that is stronger than
the one required in a given context holds.

\begin{figure}[t]
  \begin{code}
record ASTTypes : Set where
  ...
  subseteqo : forall {A} -> (P1 P2 : Post A) -> Set
  P1 `subseteqo` P2 = forall o -> P1 o -> P2 o

  sqsubseteq : forall {A} -> (p1 p2 : PredTrans A) -> Set
  f1 `sqsubseteq` f2 = forall P i -> f1 P i -> f2 P i

  MonoPT : forall {A} -> PredTrans A -> Set
  MonoPT f = forall P1 P2 -> P1 `subseteqo` P2 -> forall i -> f P1 i -> f P2 i

record ASTPredTransMono {OP} {Ty} (PT : ASTPredTrans OP Ty) : Set₂ where
  field
    returnPTMono :  forall {A} (x : A) -> MonoPT (returnPT x)
    bindPTMono : forall {A B} (f1 f2 : A -> PredTrans B)
         -> (forall x -> MonoPT (f1 x)) -> (forall x -> MonoPT (f2 x))
         -> (forall x -> f1 x `sqsubseteq` f2 x)
         -> forall P1 P2 i -> P1 `subseteqo` P2 -> bindPT f1 i P1 `subseteqo` bindPT f2 i P2
    opPTMono : forall {A}  (c : Cmd OP A)
                           (f1 f2 : (r : SubArg OP c) -> PredTrans (SubRet OP r))
         -> (forall r -> MonoPT (f1 r)) -> (forall r -> MonoPT (f2 r))
         -> (forall r -> f1 r `sqsubseteq` f2 r)
         -> forall P1 P2 i -> P1 `subseteqo` P2 -> opPT c f1 P1 i -> opPT c f2 P2 i
  predTransMono : forall {A} (m : AST OP A) -> MonoPT (predTrans m)
  predTransMono = ...
  \end{code}
  \caption{Monotonicity of PTS}
  \label{fig:ast-mono}
\end{figure}

\paragraph*{Monotonicity properties}
Figure~\ref{fig:ast-mono} gives a partial listing of
|ASTPredTransMono|, the record that describes the monotonicity lemma required by
our framework, as well as some further definitions within the scope of the
|ASTTypes| record, which we now describe.
The type |P1 `subseteqo` P2| expresses entailment of postcondition |P2| by |P1|
on all outputs (that is, that |P1| is at least as strong a postcondition as
|P2|).
For two predicate transformers |f1| and |f2|, |f1 `sqsubseteq` f2| is read as
saying that |f2| is a \emph{refinement} of |f1| because, for the same
postcondition |P|, we have that |f2| produces a precondition no stronger than
that of |f1| (as long as both preconditions are sufficient for proving |P| holds
of some program, a weaker precondition is preferable because it is more general).
Finally, monotonicity of a predicate transformer is expressed by |MonoPT|, where
|MonoPT f| says that |f| sends stronger postconditions to stronger preconditions.

Next, we consider the types of the fields
|returnPTMono|, |bindPTMono|, and |opPTMono| of record |ASTPredTransMono|,
  which the user must provide to enable proving that
the predicate transformer for any effectful computation |m : AST Op A| is monotonic.
The first, |returnPTMono|, requires that the predicate transformers in the
family assigned to |ASTreturn| are monotonic.
The monotonicity property for composite computations (|bindPTMono|) says that
we can map both refinement of (families of) predicate transformers
(|forall x -> f1 x `sqsubseteq` f2 x|) and entailment of postconditions (|P1
`subseteqo` P2|) over |bindPT|.
Similarly, for operations, |opPTMono| says that we can map predicate
transformer refinement and postcondition entailment over the function
|opPT| that assigns a predicate transformer to every command |c : Cmd Op A|.

\begin{figure}[t]
  \begin{code}
module SufficientExtension
  {O} {T} {OS : ASTOpSem O T} {PT : ASTPredTrans O T}
  (M : ASTPredTransMono PT) (S : ASTSufficientPT OS PT) where

  BranchPTMono : ASTPredTransMono BranchPT
  BranchPTMono = ...

  unextendPT :  forall {A} (m : AST BranchOps A)
    ->            ASTPredTrans.predTrans BranchPT m
    `sqsubseteq`  ASTPredTrans.predTrans PT (unextend m)
  unextendPT = ...
     
  extendPT :  forall {A} (m : AST BranchOps A)
    ->            ASTPredTrans.predTrans PT (unextend m)
    `sqsubseteq`  ASTPredTrans.predTrans BranchPT m
  extendPT = ...
       
  BranchSuf : ASTSufficientPT BranchOpSem BranchPT
  BranchSuf = ...
  \end{code}
  \caption{Sufficiency of PTS for branching operations}
  \label{fig:ast-suff-branch}
\end{figure}

\paragraph*{Agreement for the extended PTS}
Figure~\ref{fig:ast-suff-branch} shows a sketch of the proof that the extended
PTS produces, from any program |m : AST BranchOps A| and postcondition |P : Post
A|, a precondition sufficient for proving that |P| holds of the result of
running |m| with the operational semantics (|BranchSuf| in the figure).
We prove a similar result for |Necessary| (not shown; see module
|Dijkstra.AST.Branching|).
The lemmas |unextendPT| and |extendPT| are the workhorses of these proofs: taken
together, they state that, for every such effectful program |m|, the predicate
transformer obtained from |BranchPT| (Figure~\ref{fig:ast-sem-branch}) is
equivalent to the one obtained from invoking the original predicate transformer
|PT| on the result of using |unextend| to traverse the AST of |m| and
remove branching commands.

\section{Conclusion and Related Work}
\label{sec:concl}

We have presented an Agda framework for modeling effectful programs and
reasoning about them with predicate transformer semantics.
This framework enables users greater flexibility in expressing intermediate
proof obligations by using a novel (to the best of our knowledge) GADT
definition of program ASTs that enables assigning bespoke predicate
transformers to complex operations.
As evidence of the framework's generality, we describe a result showing that
the common branching operations |if|, |maybe|, and |either|, can be added
\emph{\'{a} la carte} (in the sense of
Swierstra~\cite{Swi08_Data-types-a-la-Carte}) to any existing set of effects,
with the PTS extended to cover the new operations provided that the original PTS
satisfies a monotonicity condition.

Our framework codifies and generalizes techniques used in
our work \cite{NASAFM-2022} formally verifying properties of the
\textsc{LibraBFT} consensus protocol; we have used it to prove
some properties in that context, and this has confirmed
that the framework is usable for and can significantly ease real-world verification tasks.

Our work is most closely related to that of Swierstra and
Baanen~\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects} on assigning
predicate transformer semantics to effectful programs.
Like us, they represent these programs with a datatype---in their case, a free
monad~\cite{HS00_Interactive-Programs-in-DTT}---and assign to it operational and
predicate transformer semantics, proving agreement of these semantics in order
to carry out verification tasks.
Our approach differs from theirs by making the datatype of program ASTs a GADT that
has the monadic bind operation as a constructor, enabling us to avoid the use of
a lemma for decomposing proof obligations found in
\cite{SB19_A-Predicate-Transformer-Semantics-for-Effects} \S 4 for composite
computations, and an expanded notion of effectful command that enables complex 
operations to be assigned bespoke predicate transformer semantics directly.
These differences give greater control to users of the framework in managing the
intermediate proof obligations generated during verification tasks.

PTS has also been combined profitably with \emph{Dijkstra
  monads}~\cite{SWSCL13_Verifying-Higher-Order-Programs-Dijkstra-Monad,Jac15_Dijkstra-and-Hoare-Monads-in-Monadic-Computationa}
which leverage the monadic nature of predicate transformers (specifically, they
arise from a |Set|-valued continuation monad
transformer~\cite{MAAMHRT19_Dijkstra-Monads-for-All}) to pack together
effectful code with a formal specification.
The dependently typed programming language F* has direct support for Dijkstra
monads \cite{SHKRD+16_Dependent-Types-and-Multi-Monadic-Effects-in-FStar} and
integrates these with SMT solvers for automatic reasoning about effectful code.
The main advantage enjoyed by our GADT-based approach (and also by the free
monad approach of \cite{SB19_A-Predicate-Transformer-Semantics-for-Effects}) is
\emph{freedom of interpretation:} the |AST| datatype describes only the syntax
of programs, meaning multiple operational and predicate transformer semantics
may be assigned to the same program.

% LocalWords:  blockchain cryptographic BFT HotStuff effectful provers ITPs AST
% LocalWords:  monads equational Swierstra Baanen DiemBFT Setzer Agda monadic
% LocalWords:  postconditions postcondition ASTreturn returnPT bindPT ASTbind
% LocalWords:  predTrans ASTop ASTPredTrans effectfully relatedly monotonicity
% LocalWords:  instantiation subcomputations scrutinee
