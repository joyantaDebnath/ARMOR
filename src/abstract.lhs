% -*- eval: (flyspell-mode); -*-
\begin{abstract}


      The X.509 PKI is an authentication mechanism that is widely used as a 
  building block for achieving security guarantees in many applications and protocols.
  At the core of its authentication guarantees lies the assumption 
  that one can correctly check whether a given chain of X.509 certificates 
  is considered legitimate. Implementations that realizes this assumption 
  is hailed as the ``\emph{most dangerous
    code in the world}'', as non-compliance with the X.509
  standard or other vulnerabilities  can
  lead to interoperability issues or even impersonation attacks.
  Almost all existing efforts in evaluating the correctness of an X.509
  certificate validation implementation
  rely on
  software testing approaches. 
  In the words of the famous computer scientist Edsger Dijkstra: \emph{Program
    testing can be used to show the presence of bugs, but never to show their
    absence!}
    This sentiment is corroborated by the discovery of highly influential bugs and vulnerabilities in widely used and tested open-source libraries.
  \emph{Therefore, we set out to substantially improve this
    unsatisfactory status quo by developing a high-assurance implementation of
    the X.509 certificate chain validation called \armor with formal correctness guarantees (\ie, soundness, completeness, termination, unambiguity, and non-malleability)}. \armor is developed using \agda, a dependently typed functional programming language and interactive theorem prover, and features a modular architecture to cover each stage of certificate chain validation. Our empirical evaluation demonstrates that \armor's specificational accuracy and overhead, when compared to $11$ open-source libraries against real-world and synthetic certificate chains, show its reasonable performance and effectiveness in practice.

\end{abstract}



