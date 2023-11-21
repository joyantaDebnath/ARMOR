% -*- eval: (flyspell-mode); -*-
\begin{abstract}





    % The X.509 Public Key Infrastructure (PKI) standard is a scalable and flexible authentication mechanism that utilizes X.509 certificate chains to establish trust in entities. Validating these certificate chains is critical, as it forms the foundation for achieving other security guarantees and preventing significant threats, including man-in-the-middle attacks. Unfortunately, numerous bugs and security issues have arisen in various implementations of certificate chain validation over the last decade, often due to misinterpreting natural language specifications or errors in certificate parsing. Though previous research efforts focus on testing X.509 implementations and writing certificate parsers with correctness guarantees, they lack a formal specification for X.509 certificate validation, explicit proof of soundness and completeness in certificate parsing, and correctness proofs for the semantic aspects of certificate chain validation. To address these issues, we introduce ARMOR, a formally verified implementation of X.509 certificate chain validation, developed using Agda, a dependently typed functional programming language and interactive theorem prover. ARMOR features a modular architecture with independent modules for parsing and semantic-checking, all rigorously verified and machine-checked in Agda. We finally empirically evaluate ARMOR against 11 open-source X.509 libraries using both real-world and synthetic certificates to simulate adverse scenarios. We find ARMOR achieves a 99.49\% agreement rate with these libraries, strictly adhering to RFC 5280 standards. Although ARMOR has a relatively higher runtime and memory overhead compared to C/C++ libraries, it offers competitive performance against those in Python, Java, and Go. Thus, ARMOR is a suitable choice in application areas where formal correctness is more paramount than efficiency concerns.


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
    the X.509 certificate chain validation called \armor with formal correctness guarantees (\ie, soundness, completeness, termination, unambiguity, and non-malleability)}. \armor is developed using \agda, a dependently typed functional programming language and interactive theorem prover, and features a modular architecture for the validation stages. Finally, we evaluate \armor with respect to its specificational accuracy and overhead against $11$ open-source libraries using real-world and synthetic certificates, and demonstrate its reasonable performance and effectiveness in practice.

\end{abstract}



%   The X.509 PKI is an authentication mechanism that is widely used as a 
%   building block for achieving security guarantees in many applications and protocols.
%   At the core of its authentication guarantees lies the assumption 
%   that one can correctly check whether a given chain of X.509 certificates 
%   is considered legitimate. Source code that realizes this assumption 
%   is hailed as the ``\emph{most dangerous
%     code in the world,}'' as non-compliance with the X.509
%   standard  or other vulnerabilities  can
%   lead to interoperability issues or even impersonation attacks.
%   Almost all existing efforts in evaluating the correctness of an X.509
%   certificate validation implementation
%   rely on
%   software testing approaches. 
%   In the words of the famous computer scientist Edsger Dijkstra: ``\emph{Program
%     testing can be used to show the presence of bugs, but never to show their
%     absence!}''
%     This sentiment is corroborated by the discovery of highly influential bugs and vulnerabilities in widely used and tested open-source libraries.
%   \emph{In this ambitious project, we set out to substantially improve this
%     unsatisfactory status quo by developing a high-assurance implementation of
%     the X.509 PKI with formal guarantees}. 
%   Despite the ambitious nature of the project, the PIs have 
%   already performed substantial preliminary work related to the proposed efforts, 
%   demonstrating its feasibility within the proposed duration. 
%   The  impact of this project will be immediate, 
%   as it will enable the development of a fully formally verified implementation of TLS, a holy grail 
%   of the security community. This project will also positively contribute towards the security 
%   of Amazon products such as the Silk Browser.