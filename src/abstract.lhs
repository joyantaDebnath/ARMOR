% -*- eval: (flyspell-mode); -*-
\begin{abstract}
  \xfon PKI is an authentication mechanism that is widely used as a 
  building block for achieving security guarantees in many applications and protocols.
  At the core of its authentication guarantees lies the assumption 
  that one can correctly check whether a given chain of \xfon certificates 
  is considered legitimate. However, implementations of the \xfon certificate chain validation are hailed as the ``\emph{most dangerous
    code in the world,}'' as noncompliance with the \xfon standard or other vulnerabilities can
  lead to interoperability issues or even impersonation attacks.
  Almost all existing efforts in evaluating the correctness of implementations of \xfon
  rely on software testing approaches. 
  In the words of the famous computer scientist Edsger Dijkstra, \emph{``Program
    testing can be used to show the presence of bugs, but never to show their
    absence!''}
  This sentiment is corroborated by the discovery of highly influential bugs
  and vulnerabilities in widely used and tested open-source \xfon
  implementations.
  \emph{Therefore, we set out to substantially improve this
    unsatisfactory status quo by developing a high-assurance implementation of
    the \xfon certificate chain validation, called \armor, with formal correctness
    guarantees}.
  \armor is developed using \agda, a dependently typed
  functional programming language and interactive theorem prover, and features a
  modular architecture to cover each stage of certificate chain validation.
  Finally, \armor is evaluated for its specificational accuracy and runtime
  overhead compared to $11$ open-source \xfon implementations, showcasing its
  practical effectiveness and reasonable performance in real-world
  applications. 
\end{abstract}



