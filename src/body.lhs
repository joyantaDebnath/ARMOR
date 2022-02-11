\section{Introduction}
\label{sec:introduction}

Some cool stuff!

%format eta = "\HV{\eta}"

\begin{myhs}
\begin{code}
fib :: Int -> Int
fib eta 
  | eta == 0 || eta == 1  = 1
  | otherwise             = fib (eta-1) + fib (eta-2)
\end{code}
\end{myhs}

\[
\mathit{fib} n = fib n
\]

\section{Conclusion}
\label{sec:conclusion}

Really cool conclusion!