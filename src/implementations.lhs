\section{Implementation}

\subsection{Code Extraction to Binary of Agda} 
\agda is primarily a proof assistant, not commonly used to produce executable binaries directly. However, we can indirectly produce executable binaries by compiling the \agda code to \haskell and then using the \haskell compiler \ghc~\cite{ghc} to generate an executable. This process begins with enabling IO operations through \agda's builtin features. Then, \agda's \textsf{compile} command transforms the \agda code to \haskell. The generated \haskell code is then compiled into an executable binary using the \ghc. However, in terms of runtime performance, the generated executable may not be as efficient as the code written directly in \haskell.

\subsection{Input Interfaces} python side, task to pass to agda side, do signature verification
\subsection{Only RSA Signature verification}
\subsection{String Prep limitations (UTF8)}

\subsection{Supported Extensions}