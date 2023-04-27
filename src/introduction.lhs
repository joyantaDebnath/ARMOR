\section{Introduction}

X.509 Public Key Infrastructure (PKI) is a widely used authentication and key distribution mechanism that plays a critical role in establishing trust in secure communication. X.509 PKI utilizes a chain of digital certificates, each containing a binding between an entity and its public key. Moreover, the certificate chain validation is crucial since it entails that an end-user certificate presented by an entity is signed by a third-party organization called Certificate Authority (CA) and that the CA's certificate can be chained back to a root CA that the verifier trusts. However, flaws in implementing X.509 certificate chain validation logic (CCVL) are profound in practice and often lead to severe implications, such as the interception and modification of communication by man-in-the-middle (MITM) attackers. Hence, developing a formally verified X.509 CCVL implementation is paramount to ensure that it is compliant with the standard specifications and bolsters confidence in digital communication security.

Some notable works have already analyzed the use of fuzzing (e.g., Frankencert, Mucert) and dynamic symbolic execution (e.g., SymCert, RFCCert) to find vulnerabilities in renowned X.509 CCVL implementations. While these previous efforts found numerous instances of noncompliance and implementation flaws, they intrinsically suffer from false negatives. Though there is a recent effort, CERES, which used satisfiability modulo theories (SMT) to formalize the X.509 standard specification and develop a high-assurance reference implementation for X.509 CCVL, it was not formally proven to be functionally correct with respect to the specification. 

\textbf{Problem and scope.} \says{joyanta}{write the problem we are trying to solve (implementation flaws -> MITM attack). we can mention the threat model here with client - server example.}

\textbf{Challenges.} \says{joyanta}{natural language spec, producer, consumer rules, der context sensitivity for parsing, challenges specific to doing formal verification}

\textbf{Approach.} \says{joyanta}{mention that we followed the idea of CERES to divide syntactic and semantic requirements, talk about how did we prove soundness and completeness of each module, define soundness completeness, mention Agda, why chose agda, how did you solve the challenges (e.g., backtracking, context sensitivity) -- 2-3 paragraphs}

\textbf{Findings.} \says{joyanta}{mention some noteable findings in one paragraph}

\textbf{Our Contributions.}
\begin{enumerate}[label=(\arabic*)]
    \item formally veridied X.509 implementation, AERES
    \item 2-3 lines about our approach
    \item evaluation with differential testing of 10 libraries, findings are responsibly disclosed
\end{enumerate}

\textbf{Organization.}