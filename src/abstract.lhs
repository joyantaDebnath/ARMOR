\begin{abstract}
The X.509 Public-Key Infrastructure (PKI) is a ubiquitous authentication mechanism, 
used as a fundamental building block for achieving the required security guarantees 
in many security-critical applications. Vulnerabilities or non-compliances with the 
X.509 standard (i.e., RFC 5280) in an X.509 certificate chain validation implementation 
can result in impersonation attacks and/or interoperability issues. In this paper, 
we focus on developing a modular X.509 certificate chain validation library called 
\armor that avoids such pitfalls by formally verifying its implementation with respect 
to the requirements in RFC 5280. \armor{}'s guarantees are mechanically 
proven using the \agda theorem prover, taking advantage of its advanced type
system. To achieve better confidence in our formalization of the natural  
language requirements of X.509 PKI prescribed in RFC 5280, we differentially test \armor with respect 
to $11$ widely used X.509 PKI libraries. In our evaluation, we observe that \armor agrees 
with these libraries most of the times. When it differs, we notice that 
\armor strictly follows the requirements in RFC 5280, whereas the other libraries 
have a more relaxed enforcement of these requirements.
Finally, in the context of runtime overhead, we observe that although \armor has a higher overhead than libraries 
in our evaluation that are written in \cpp, it has better or comparable performance 
to the libraries written in Go, Java, and Python.


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