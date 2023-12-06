\section{Conclusion}
In this paper, we present the design and development of a high-assurance \xfon certificate chain validation implementation, 
called \armor, whose correctness guarantees are established through formal proofs. One of the main technical 
challenges in this pursuit is a clear lack of an end-to-end formal, relational specification of the whole certificate chain 
validation algorithm. \armor addresses this challenge by decomposing the algorithm into certain self-contained steps; realizing 
them as separate modules. \armor then establishes correctness guarantees for most of these modules. As the specification of 
\armor is part of its TCB, we evaluate its specificational accuracy by differentially comparing it 
against $11$ open-source X.509 libraries while identifying several noncompliance 
issues in the tested libraries. We are currently in the process of communicating our findings to the developers of those tested 
libraries. We also provide an end-to-end application of \armor, integrating it with the TLS 1.3 implementation of \boringssl 
and testing it with the \curl data transfer tool. Our evaluation suggests that \armor is currently a suitable option 
for \xfon certificate validation in scenarios where formal correctness is prioritized over runtime overhead. 
Overall, we realize that the current RFC 5280 standard is bloated with historical features and lacks clear directions 
on enforcing certain constraints, which not only impedes any formal verification efforts but also imposes a high engineering 
overhead. Streamlining and simplifying the standard can improve the overall standard compliance of these libraries substantially. 