\section{Design Overview}

\subsection{Problem Definition}

\subsection{High-Level Approach}

\begin{enumerate}
\item The Aeres external driver is invoked with the filepath of the certificate
chain we wish to check. The driver invokes Aeres with the contents of this file.

\item Aeres uses its verified PEM parser library to parse the PEM certificate
chain, then decodes the Base64-encoded certificates into a single
bytestring. (Sound and complete parsing)

\item Aeres uses its verified X.509 parser library to parse the bytestring into a
list of certificates. (Sound, complete, secure)

\item Aeres then checks several semantic properties not suitable for expressing
in the grammar (e.g., validity period of cert contains current time)

\item For each cert, Aeres outputs the bytestring serializations for the TBS
certificate, signature, and public key, and also outputs the signature
algorithm OIDLeastBytes

\item The external driver verifies the public key signatures.
\end{enumerate}
