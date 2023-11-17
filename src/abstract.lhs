% -*- eval: (flyspell-mode); -*-
\begin{abstract}





    The X.509 Public Key Infrastructure (PKI) standard is a scalable and flexible authentication mechanism that utilizes X.509 certificate chains to establish trust in entities. Validating these certificate chains is critical, as it forms the foundation for achieving other security guarantees and preventing significant threats, including man-in-the-middle attacks. Unfortunately, numerous bugs and security issues have arisen in various implementations of certificate chain validation over the last decade, often due to misinterpreting natural language specifications or errors in certificate parsing. Though previous research efforts focus on testing X.509 implementations and writing certificate parsers with correctness guarantees, they lack a formal specification for X.509 certificate validation, explicit proof of soundness and completeness in certificate parsing, and correctness proofs for the semantic aspects of certificate chain validation. To address these issues, we introduce ARMOR, a formally verified implementation of X.509 certificate chain validation, developed using Agda, a dependently typed functional programming language and interactive theorem prover. ARMOR features a modular architecture with independent modules for parsing and semantic-checking, all rigorously verified and machine-checked in Agda. We finally empirically evaluate ARMOR against 11 open-source X.509 libraries using both real-world and synthetic certificates to simulate adverse scenarios. We find ARMOR achieves a 99.49\% agreement rate with these libraries, strictly adhering to RFC 5280 standards. Although ARMOR has a relatively higher runtime and memory overhead compared to C/C++ libraries, it offers competitive performance against those in Python, Java, and Go. Thus, ARMOR is a suitable choice in application areas where formal correctness is more paramount than efficiency concerns.

% The X.509 Public-Key Infrastructure (PKI) is a ubiquitous authentication mechanism, 
% used as a fundamental building block for achieving the required security guarantees 
% in many security-critical applications. Vulnerabilities or noncompliances with the 
% X.509 standard (i.e., RFC 5280) in an X.509 certificate chain validation implementation 
% can result in impersonation attacks and/or interoperability issues. In this paper, 
% we focus on developing a modular X.509 certificate chain validation library called 
% \armor that avoids such pitfalls by formally verifying its implementation with respect 
% to the requirements in RFC 5280. \armor{}'s guarantees are mechanically 
% proven using the \agda theorem prover, taking advantage of its advanced type
% system. To achieve better confidence in our formalization of the natural  
% language requirements of X.509 PKI prescribed in RFC 5280, we differentially test \armor with respect 
% to $11$ widely used X.509 PKI libraries. In our evaluation, we observe that \armor agrees 
% with these libraries most of the times. When it differs, we notice that 
% \armor strictly follows the requirements in RFC 5280, whereas the other libraries 
% have a more relaxed enforcement of these requirements.
% Finally, in the context of runtime overhead, we observe that although \armor has a higher overhead than libraries 
% in our evaluation that are written in \cpp, it has better or comparable performance 
% to the libraries written in Go, Java, and Python.


% , thus offering formal assurances of (partial) correctness in accordance 
% to the \xfon standard specification.  


% The X.509 Public-Key Infrastructure (PKI) is a ubiquitous authentication mechanism 
% that is used as a fundamental building block for achieving desired security 
% guarantees such as confidentiality, integrity, and non-repudiation in many 
% security-critical applications, including but not limited to SSL/TLS, HTTPS, 
% Email, DNS, WiFi, secure boot, firmware/software verification, and secure software update. 
% Vulnerabilities or noncompliances with the \xfon standard (i.e., RFC 5280) in a 
% \xfon certificate chain validation implementation can result in violations of these desired 
% security guarantees  and/or can give rise to interoperability issues. To avoid these pitfalls, 
% this paper takes the substantial first step towards developing a formally verified \xfon certificate 
% chain validation library \armor, which supports the widely used functionality specified in RFC 5280. 





% Despite the omnipresence of the \xfon Public Key Infrastructure (PKI) as an authentication method, 
% flaws in \xfon certificate chain validation can expose relying applications to impersonation attacks 
% and interoperability issues. The complex, ambiguous, and occasionally under-specified nature of the 
% \xfon specification often leads to non-compliance issues across many libraries implementing the logic of 
% \xfon certificate chain validation. To improve this situation, this work formally specifies the most-used 
% segment of the \xfon standard using the \agda interactive theorem prover and finally develops a 
% formally-verified implementation \armor. \armor's \soundness and \completeness are proven by 
% leveraging \agda's advanced type system and dependent types, thus offering formal assurances of 
% correctness in line with the \xfon standard specification. This rigorously designed implementation is 
% subsequently employed as a benchmark in a differential testing framework to scrutinize $11$ open-source 
% \xfon implementations, helping uncover potential vulnerabilities. When tested against $2$ million 
% real-world certificate chains, \armor demonstrates its effectiveness and robustness by appropriately 
% rejecting non-compliant certificates while maintaining a reasonable runtime and memory overhead.
\end{abstract}