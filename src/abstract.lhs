% -*- eval: (flyspell-mode); -*-
\begin{abstract}
  \xfon PKI as an authentication mechanism is widely used as a 
  building block for achieving security guarantees in many applications and protocols.
  At the core of its authentication guarantees lies the assumption 
  that one can \emph{correctly} check whether a given chain of \xfon certificates 
  is  legitimate. 
  %However, implementations of the \xfon certificate 
  %chain validation are hailed as the ``\emph{most dangerous
  %code in the world,}'' because noncompliance with the \xfon standard or 
  %other vulnerabilities can
  %lead to interoperability issues or even impersonation attacks.
  Since noncompliance with the \xfon standard and other vulnerabilities in 
  implementations of the \xfon certificate chain validation
  can lead to interoperability issues or even impersonation attacks, they are  
  hailed as the ``\emph{most dangerous code in the world.}''
  Almost all existing efforts in evaluating the correctness of implementations of \xfon
  rely on software testing. 
  In the words of the famous computer scientist Edsger Dijkstra, \emph{``Program
    testing can be used to show the presence of bugs, but never to show their
    absence!''}
  This sentiment is corroborated by the discovery of highly influential bugs
  and vulnerabilities in widely used and tested open-source \xfon
  implementations.
  %\emph{
    Therefore, we set out to substantially improve this
    unsatisfactory status quo by developing a high-assurance implementation for
    the \xfon certificate chain validation with formal correctness
    guarantees, called \armor.
    %}.
  \armor features a modular architecture in which each stage of 
  the certificate chain validation process is captured as a separate 
  module. 
  The formal correctness guarantees for each of these modules 
  are then mechanically proved using the \agda interactive theorem prover. 
  To demonstrate its efficacy, 
 % practical effectiveness and reasonable performance in real-world
 % applications, 
  \armor is compared with $11$ open-source \xfon implementations 
  %evaluated 
  for its specificational accuracy and runtime
  overhead. %comparing with $11$ open-source \xfon implementations. 
  In our evaluation, \armor incurs high overhead but remains strictly 
  standards-compliant. Finally, we  show an end-to-end application 
  of \armor by integrating it with the TLS 1.3 implementation of \boringssl 
  %in \curl. 
  and testing it with \curl.
\end{abstract}



