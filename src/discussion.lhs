\section{Discussion}
\noindent\textbf{Threat to Validity.} Recall that 
the specification of \armor is 
part of its TCB. Although \armor's compliance with its specification is mechanically 
proven, we cannot in principle guarantee the specification's consistency with
the natural language description in RFC 5280.
Empirical evaluation with real and synthetic 
certificate chains did not reveal any inconsistencies, which gives 
confidence in our interpretation of the RFC's natural language specification. 
Additionally, \armor does not include formal guarantees on its cryptographic 
operations, instead outsourcing signature verification to external libraries 
like \haclstar and \morpheus. Notably, an attempt to use the formally-verified 
WhyMP library~\cite{melquiond2020whymp} for \emph{modular exponentiation} 
proved unsuccessful for some inputs, leading to our reliance on \python's 
cryptography library for this task.  

\noindent\textbf{Room for improvement.} 
Although \armor makes a substantial stride towards having a high-assurance
implementation of \xfon PKI with formally proven correctness properties, there
is still room for improvement before it can be incorporated to an application
such as a web browser.
As an example, in contrast to existing open-source libraries, \armor does not yet support \emph{hostname 
verification} and \emph{revocation}. Although hostname 
verification is a critical step towards achieving the desired security guarantees of 
\xfon PKI, we follow the lead of RFC 5280, in which it is not part of the standard but 
is left to the application developer. 
% Revocation, albeit highly desirable, is also not 
% supported by many mainstream SSL/TLS libraries such as \gnutls and \matrixssl  
% (See Table~\ref{table:features}). 
Concerning extensions, we currently do not 
support the enforcement of Subject key identifier (SKI) and Authority key identifier (AKI) 
extensions. SKI and AKI can substantially simplify the construction of candidate 
certificate chains. However, in a recent measurement study on Censys data \cite{debnath2021re}, 
SKI and AKI are found to be present only on $\sim 95\%$ of the certificates. For generality, 
we use name matching as our basis of certificate chain building instead of AKI and SKI. 
Dictated by CA/B forum, browsers often enforce more stringent requirements that are 
not necessarily warranted by RFC 5280. These additional constraints are currently missing 
from \armor. Finally, to realize the incorporation of \armor into a web browser,
its overhead must be reduced and it must come with formal guarantees of memory
safety.
Improving \armor in these directions is left as future work. 
% The current version of \armor can be used in applications 
% where high-level assurance is more important than the overhead. 

\noindent\textbf{Lessons learned.}
\armor currently does not feature a formally-verified string canonicalizer. 
\armor{}'s string canonicalizer does not handle bidirectional 
characters and only supports UTF-8 encoded unicode characters. We, however, observe 
that \emph{none of the existing libraries} performs this suggested step. 
Similarly, \armor does not yet enforce name constraints and Policy Checking, 
which are also unsupported by some mainstream libraries. These are only a few examples 
of features present in RFC 5280 whose complexities make them daunting to
implement correctly in practice.
Furthermore, some constraints RFC 5280 places on issuers lack clear directions
regarding whether \emph{consumers} should reject noncompliance.
Overall, we believe that the specification can and should be substantially 
simplified and streamlined, removing bloat due to historical features, 
to ensure improved interoperability and security. 




% The 
% justification of library developers' ignoring these features is dictated by the engineering 
% cost-benefit analysis tilts towards cost.  

%\says{joy}{TODO for Omar}

% \noindent\textbf{Limitations.} ARMOR has certain limitations: \emph{First}, it does not include verification of cryptographic operations, instead outsourcing signature verification to external libraries like \haclstar and \morpheus. Notably, an attempt to use the formally-verified WhyMP library~\cite{melquiond2020whymp} for \emph{modular exponentiation} proved unsuccessful for some inputs, leading to our reliance on \python's cryptography library for thus task. \emph{Second}, ARMOR offers no formal correctness guarantees for its memory-safety. \emph{Third}, \armor does not feature a formally-verified string canonicalizer. The existing string canonicalizer is limited, as it does not handle bidirectional characters and only supports UTF-8 encoded unicode characters. \emph{Finally}, \armor does not support features like hostname verification and revocation checking. This exclusion simplifies our verification efforts but limits \armor's practical usage with SSL/TLS protocol.

% \says{joy}{TODO for Omar: how will you use the features table here?}








