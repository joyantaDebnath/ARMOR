\appendix

\section{Appendix}
  
\begin{table}[]
  % \captionsetup{font=footnotesize}
  \centering
  \sffamily\scriptsize
      \setlength\extrarowheight{1.5pt}
      \setlength{\tabcolsep}{1.5pt}
      \caption{Execution time analysis on \censys chains}
      \sffamily\scriptsize
      S.D. = Standard Deviation\enskip
      \vspace{0.5em}
      \label{comp}
      \sffamily\tiny
  \centering
  \begin{tabular}{c||cccccc||c||cccccc||}
  \cline{2-14}
  {\color[HTML]{000000} \textit{}}                              & \multicolumn{6}{c||}{{\color[HTML]{000000} \textbf{Accept}}}                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             & {\color[HTML]{000000} }                    & \multicolumn{6}{c||}{{\color[HTML]{000000} \textbf{Reject}}}                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \textbf{Library}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{Count}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ sec\end{tabular}}}} & {\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ sec\end{tabular}}} & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{Count}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ sec\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ sec\end{tabular}}}} & {\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ sec\end{tabular}}} \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \boringssl}}        & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.004}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1.119}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.029}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.029}}                                                         & {\color[HTML]{000000} 0.009}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.004}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.340}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.028}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.028}}                                                         & {\color[HTML]{000000} 0.006}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \gnutls}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.004}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.340}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.028}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.028}}                                                         & {\color[HTML]{000000} 0.006}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.001}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.952}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.015}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.014}}                                                         & {\color[HTML]{000000} 0.006}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \matrixssl}}        & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.257}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.011}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.011}}                                                         & {\color[HTML]{000000} 0.003}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.003}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.065}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                         & {\color[HTML]{000000} 0.004}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \mbedtls}}         & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.008}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.125}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                         & {\color[HTML]{000000} 0.002}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.007}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.129}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.008}}                                                         & {\color[HTML]{000000} 0.002}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \openssl}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.026}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1.014}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.051}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.050}}                                                         & {\color[HTML]{000000} 0.011}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.026}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.491}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.051}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.049}}                                                         & {\color[HTML]{000000} 0.011}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \wolfssl}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.006}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1.039}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                         & {\color[HTML]{000000} 0.006}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.007}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.072}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.009}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.008}}                                                         & {\color[HTML]{000000} 0.002}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \crypto}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.187}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.891}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.269}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.260}}                                                         & {\color[HTML]{000000} 0.101}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.006}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.484}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.194}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.246}}                                                         & {\color[HTML]{000000} 0.138}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \bouncycastle}}    & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.573}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.019}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.956}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.920}}                                                         & {\color[HTML]{000000} 0.382}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.251}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 5.714}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.709}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.627}}                                                         & {\color[HTML]{000000} 0.219}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \sun}}              & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.129}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.140}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.285}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.271}}                                                         & {\color[HTML]{000000} 0.085}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.147}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1.882}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.215}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.194}}                                                         & {\color[HTML]{000000} 0.075}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \certvalidator}}    & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,951}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.221}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.855}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.269}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.263}}                                                         & {\color[HTML]{000000} 0.060}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,049}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.143}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1.779}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.254}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.254}}                                                         & {\color[HTML]{000000} 0.061}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \ceres}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,801}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.033}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 5.735}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.755}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.821}}                                                         & {\color[HTML]{000000} 0.338}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,199}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.151}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 5.621}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.541}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.594}}                                                         & {\color[HTML]{000000} 0.263}                                                       \\ \cline{1-7} \cline{9-14} 
  \multicolumn{1}{||c||}{{\color[HTML]{000000} \armor}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,801}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.207}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.553}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.641}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.618}}                                                         & {\color[HTML]{000000} 0.118}                                                       & \multirow{-14}{*}{{\color[HTML]{000000} }} & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,199}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 0.053}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.665}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.518}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.544}}                                                         & {\color[HTML]{000000} 0.300}                                                       \\ \hline
  \end{tabular}
  \end{table}

  \begin{table}[]
    \centering
    \sffamily\scriptsize
        \setlength\extrarowheight{1.5pt}
        \setlength{\tabcolsep}{1.5pt}
        \caption{Memory consumption analysis on \censys chains}
        \sffamily\scriptsize
        S.D. = Standard Deviation\enskip
        \vspace{0.5em}
        \label{mem}
        \sffamily\tiny
    \centering
    \begin{tabular}{c||cccccc||c||cccccc||}
    \cline{2-14}
    {\color[HTML]{000000} \textit{\textbf{}}}                     & \multicolumn{6}{c||}{{\color[HTML]{000000} \textbf{Accept}}}                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        & {\color[HTML]{000000} }                    & \multicolumn{6}{c||}{{\color[HTML]{000000} \textbf{Reject}}}                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \textbf{Library}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{Count}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ mb\end{tabular}}}} & {\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ mb\end{tabular}}} & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{Count}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ mb\end{tabular}}}} & \multicolumn{1}{c||}{{\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ mb\end{tabular}}}} & {\color[HTML]{000000} \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ mb\end{tabular}}} \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \boringssl}}        & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.01}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.49}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.21}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.21}}                                                         & {\color[HTML]{000000} 0.06}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.62}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.36}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.13}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.17}}                                                         & {\color[HTML]{000000} 0.12}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \gnutls}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.18}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.82}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.51}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.52}}                                                         & {\color[HTML]{000000} 0.13}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.50}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.57}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 7.74}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.00}}                                                         & {\color[HTML]{000000} 0.91}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \matrixssl}}        & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.02}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.50}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.31}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.32}}                                                         & {\color[HTML]{000000} 0.08}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 2.34}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.49}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.17}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.29}}                                                         & {\color[HTML]{000000} 0.30}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \mbedtls}}         & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.82}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.20}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.99}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.98}}                                                         & {\color[HTML]{000000} 0.07}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 3.80}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.19}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.00}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 4.01}}                                                         & {\color[HTML]{000000} 0.07}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \openssl}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.72}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 7.51}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.90}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.89}}                                                         & {\color[HTML]{000000} 0.08}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.60}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 7.06}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.87}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 6.87}}                                                         & {\color[HTML]{000000} 0.08}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \wolfssl}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 7.86}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.61}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.35}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.41}}                                                         & {\color[HTML]{000000} 0.17}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.27}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.58}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.44}}                                                       & \multicolumn{1}{c||}{{\color[HTML]{000000} 8.46}}                                                         & {\color[HTML]{000000} 0.06}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \crypto}}           & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 59.59}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 68.30}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 64.41}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 62.89}}                                                        & {\color[HTML]{000000} 2.54}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 60.52}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 68.29}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 64.10}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 62.66}}                                                        & {\color[HTML]{000000} 2.53}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \bouncycastle}}    & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 84.34}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 130.99}}                                                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 105.79}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 101.91}}                                                       & {\color[HTML]{000000} 8.42}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 82.55}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 119.71}}                                                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 89.96}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 86.02}}                                                        & {\color[HTML]{000000} 6.44}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \sun}}              & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,956}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 47.50}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 62.83}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 53.60}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 53.19}}                                                        & {\color[HTML]{000000} 1.19}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,044}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 44.42}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 61.52}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 50.30}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 49.88}}                                                        & {\color[HTML]{000000} 1.86}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \certvalidator}}    & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,951}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 26.67}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 28.42}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 27.06}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 27.04}}                                                        & {\color[HTML]{000000} 0.14}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,049}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 23.90}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 27.30}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 26.62}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 26.79}}                                                        & {\color[HTML]{000000} 0.71}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \ceres}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,801}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 21.03}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 40.70}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 39.08}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 39.45}}                                                        & {\color[HTML]{000000} 2.24}                                                       & {\color[HTML]{000000} }                    & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,199}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 21.02}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 31.79}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 27.03}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 28.04}}                                                        & {\color[HTML]{000000} 3.23}                                                       \\ \cline{1-7} \cline{9-14} 
    \multicolumn{1}{||c||}{{\color[HTML]{000000} \armor}}            & \multicolumn{1}{c||}{{\color[HTML]{000000} 74,801}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 998}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 1187}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 1049}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1032}}                                                        & {\color[HTML]{000000} 61}                                                       & \multirow{-14}{*}{{\color[HTML]{000000} }} & \multicolumn{1}{c||}{{\color[HTML]{000000} 25,199}}          & \multicolumn{1}{c||}{{\color[HTML]{000000} 994}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 1185}}                                                     & \multicolumn{1}{c||}{{\color[HTML]{000000} 1069}}                                                      & \multicolumn{1}{c||}{{\color[HTML]{000000} 1075}}                                                        & {\color[HTML]{000000} 135}                                                      \\ \hline
  \end{tabular}
\end{table}


    % \begin{table}[h]
    % \setlength\extrarowheight{1.2pt}
    % \setlength{\tabcolsep}{1.5pt}
    % \centering
    % \sffamily\tiny
    % \caption{Features supported by different \xfon libraries}
    % BC = Basic Constraints \quad  KU = Key Usage \quad EKU = Extended Key Usage  \\ \quad SKI = Subject Key Identifier \quad AKI = Authority Key Identifier \\ \quad SAN = Subject Alternative Name \quad NC = Name Constraints \enskip \enskip
    % \vspace{2em}
    % \sffamily\tiny
    % \begin{tabular}{c||ccccc||}
    % \cline{2-6}
    %                                        & \multicolumn{5}{c||}{\textbf{Features}}                                                                                                                                                                                                                                                                                                                                                                                                                     \\ \hline
    % \multicolumn{1}{||c||}{\textbf{Library}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Hostname\\ Verification\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Revocation\\ Checking\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Policy\\ Checking\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Chain\\ Building\end{tabular}}} & \textbf{\begin{tabular}[c]{@@{}c@@{}}Extensions\\ Enforced\end{tabular}}    \\ \hline
    % \multicolumn{1}{||c||}{\boringssl}        & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & \begin{tabular}[c]{@@{}c@@{}}BC, KU, EKU, \\ SKI, AKI, SAN, NC\end{tabular} \\ \hline
    % \multicolumn{1}{||c||}{\gnutls}           & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\times$}                                                                 & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU, NC                                                           \\ \hline
    % \multicolumn{1}{||c||}{\matrixssl}           & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\times$}                                                                 & \multicolumn{1}{c||}{$\checkmark$}                                                               & \begin{tabular}[c]{@@{}c@@{}}BC, KU, EKU, \\ SKI, AKI, SAN\end{tabular}     \\ \hline
    % \multicolumn{1}{||c||}{\mbedtls}          & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU                                                               \\ \hline
    % \multicolumn{1}{||c||}{\openssl}          & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & \begin{tabular}[c]{@@{}c@@{}}BC, KU, EKU, \\ SKI, AKI, SAN, NC\end{tabular} \\ \hline
    % \multicolumn{1}{||c||}{\crypto}           & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\times$}                                                                     & \multicolumn{1}{c||}{$\times$}                                                                 & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU, NC                                                           \\ \hline
    % \multicolumn{1}{||c||}{\bouncycastle}           & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU, NC                                                           \\ \hline
    % \multicolumn{1}{||c||}{\sun}              & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU, NC                                                           \\ \hline
    % \multicolumn{1}{||c||}{\certvalidator}    & \multicolumn{1}{c||}{$\checkmark$}                                                                      & \multicolumn{1}{c||}{$\checkmark$}                                                                    & \multicolumn{1}{c||}{$\checkmark$}                                                                & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU                                                               \\ \hline
    % \multicolumn{1}{||c||}{\ceres}            & \multicolumn{1}{c||}{$\times$}                                                                       & \multicolumn{1}{c||}{$\times$}                                                                     & \multicolumn{1}{c||}{$\times$}                                                                 & \multicolumn{1}{c||}{$\checkmark$}                                                               & \begin{tabular}[c]{@@{}c@@{}}BC, KU, EKU, \\ SKI, AKI, SAN\end{tabular}     \\ \hline
    % \multicolumn{1}{||c||}{\armor}            & \multicolumn{1}{c||}{$\times$}                                                                       & \multicolumn{1}{c||}{$\times$}                                                                     & \multicolumn{1}{c||}{$\times$}                                                                 & \multicolumn{1}{c||}{$\checkmark$}                                                               & BC, KU, EKU, SAN                                                          \\ \hline
    % \end{tabular}
    % \label{table:features}
    % \end{table}


\begin{table*}[]
  \setlength\extrarowheight{1.2pt}
  \setlength{\tabcolsep}{1.5pt}
  \centering
  \sffamily\scriptsize
  \caption{Semantic restrictions enforced by \armor}
  \sffamily\scriptsize
  \begin{tabularx}{0.8\textwidth}{||c||X||}
  \hline
  \textbf{Name} & \textbf{Description}                                                                                                                                                                                              \\ \hline
  R1              & \texttt{SignatureAlgorithm} field MUST contain the same algorithm identifier as the \texttt{Signature} field in the sequence \texttt{TbsCertificate}.                                                                                                 \\ \hline
  R2              & \texttt{Extension} field MUST only appear if the \texttt{Version} is 3                                                                                                                                                                      . \\ \hline
  R3              & The \texttt{Serial} number MUST be a positive integer assigned by the CA to each certificate. Certificate users MUST be able to handle \texttt{Serial} number values up to 20 octets.                                                         \\ \hline
  R4              & The \texttt{Issuer} field MUST contain a non-empty distinguished name (DN).                                                                                                                                                         \\ \hline
  R5              & If the \texttt{Subject} is a CA (\eg, the \texttt{Basic Constraints} extension, is present and the value of \texttt{CA} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                      \\ \hline
  R6              & \texttt{Unique Identifiers} fields MUST only appear if the \texttt{Version} is 2 or 3. These fields MUST NOT appear if the \texttt{Version} is 1.                                                                                                     \\ \hline
  R7              & Where it appears, the \texttt{PathLenConstraint} field MUST be greater than or equal to zero.                                                                                                                                       \\ \hline
  R8              & If the \texttt{Subject} is a CRL issuer (\eg, the \texttt{Key Usage} extension, is present and the value of \texttt{CRLSign} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                 \\ \hline
  R9             & When the \texttt{Key Usage} extension appears in a certificate, at least one of the bits MUST be set to 1.                                                                                                                           \\ \hline
  R10             & If subject naming information is present only in the \texttt{Subject Alternative Name} extension , then the \texttt{Subject} name MUST be an empty sequence and the \texttt{Subject Alternative Name} extension MUST be critical.                                         \\ \hline
  R11             & If the \texttt{Subject Alternative Name} extension is present, the sequence MUST contain at least one entry.                                                                                                                                  \\ \hline
  R12             & If the \texttt{KeyCertSign} bit is asserted, then the \texttt{CA} bit in the \texttt{Basic Constraints} extension MUST also be asserted. If the \texttt{CA} boolean is not asserted, then the \texttt{KeyCertSign} bit in the \texttt{Key Usage} extension MUST NOT be asserted. \\ \hline
  R13             & A certificate MUST NOT include more than one instance of a particular \texttt{Extension}.                                                                                                                                           \\ \hline
  R14             & A certificate-using system MUST reject the certificate if it encounters a critical \texttt{Extension} it does not recognize or a critical \texttt{Extension} that contains information that it cannot process.                               \\ \hline
  R15             & A certificate policy OID MUST NOT appear more than once in a \texttt{Certificate Policies} extension.                                                                                                                               \\ \hline
  R16             & While each of these fields is optional, a \texttt{DistributionPoint} MUST NOT consist of only the \texttt{Reasons} field; either \texttt{distributionPoint} or  \texttt{CRLIssuer} MUST be present.                                                             \\ \hline
  R17             & The certificate \texttt{Validity} period includes the current time.                                                                                                                                                                 \\ \hline
                                                                                                                                                                                                                                     
  R18              & If a certificate contains both a \texttt{Key Usage} extension and an \texttt{Extended Key Usage} extension, then both extensions MUST be processed independently and the certificate MUST only be used for a purpose consistent with both extensions. If there is no purpose consistent with both extensions, then the certificate MUST NOT be used for any purpose. \\ \hline
  R19              & Conforming implementations may choose to reject all \texttt{Version} 1 and \texttt{Version} 2 intermediate CA certificates                                                                                                                                                                                                                                            . \\ \hline
  R20              & The \texttt{PathLenConstraint} field is meaningful only if the \texttt{CA} boolean is asserted and the \texttt{Key Usage} extension, if present, asserts the \texttt{KeyCertSign} bit. In this case, it gives the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.                                          \\ \hline
  R21              & For \texttt{DistributionPoint} field, if the certificate issuer is not the CRL issuer, then the \texttt{CRLIssuer} field MUST be present and contain the Name of the CRL issuer. If the certificate issuer is also the CRL issuer, then conforming CAs MUST omit the \texttt{CRLIssuer} field and MUST include the \texttt{distributionPoint} field.                                                                \\ \hline
  R22              & A certificate MUST NOT appear more than once in a prospective certification path.                                                                                                                                                                                                                                                                  \\ \hline
                                                                                                                                                                                                                                                                                                                                                                  
  R23              & Every non-leaf certificate in a chain must be a CA certificate.                                                                                                                                                                                                                                                                                                                       
  
                                                                                                                                                                                                                                                                                                                          \\ \hline     
  R24              & Certificate users MUST be prepared to process the \texttt{Issuer} distinguished name and \texttt{Subject} distinguished name fields to perform name chaining for certification path validation.                                                                                                                                                                      \\ \hline
  R25              & Validate whether the chain starts from a trusted CA.                                                                                                                                                                                                                                                                                         \\ \hline   
  R26              & Validate RSA signatures.                                                                                                                                                                                                                                                                                                                           \\ \hline
  R27              & Validate leaf certificate purpose against user's expected certificate purpose. \\ \hline                                                      
  \end{tabularx}
  \label{rules}
\end{table*}

\begin{table*}
  \setlength\extrarowheight{1.2pt}
  \setlength{\tabcolsep}{1.5pt}  
  \centering
  \sffamily\scriptsize
  \caption{Formal Guarantees}
  \sffamily\scriptsize
  \begin{tabularx}{0.8\textwidth}{||c||c||X||}
    \hline
    \textbf{Property}
    & \textbf{Proven For}
    & \textbf{Description}
    \\ \hline
    |Unambiguous|
    & PEM, \xsno DER, \xfon
    & One string cannot be the encoding of two distinct values.
    \\ \hline
    |NonMalleable|
    & \xsno DER, \xfon
    & Two distinct strings cannot be the encoding of the same value.
    \\ \hline
    |UniquePrefixes|
    & \xsno DER, \xfon (\tlv)
    & At most one prefix of a string is in the language.
    \\ \hline \hline
    Isomorphism
    & Base64 decoder
    & The Base64 decoder forms an isomorphism with a specificational encoder
    between the set of octet strings and the subset of sextet strings that are
    valid encodings.
    \\ \hline \hline
    |MaximalParser|
    & PEM
    & If the parser consumes a prefix, that prefix is the longest one in the language.
    \\ \hline
    |Sound| (parser)
    & PEM, \xsno DER, \xfon
    & If the parser accepts some prefix, that prefix is in the
    language.
    \\ \hline
    |Complete| (parser)
    & PEM, \xsno DER, \xfon
    & If the string is in the language, the parser accepts some prefix of it.
    \\ \hline
    |StronglyComplete|
    & PEM, \xfon
    & If a string is in the language and encodes value |v|, the parser consumes
    \emph{exactly} that string and produces |v|.
    \\ \hline \hline
    Valid chain
    & X.509
    & Our specification |Chain| for chains consisting of a sequence of \(n\)
    certificates satisfies the following properties by construction:
    \begin{enumerate}
    \item[(a)] for all \(x\in \{1 \ldots n-1\}\), the subject of certificate
      \(x\) is the issuer of certificate \(x+1\);
    \item[(b)] certificate \(1\) is issued by a trusted CA;
    \item[(c)] certificate \(n\) is the certificate to be validated
    \end{enumerate}

    \\ \hline
    Chain uniqueness
    & \xfon
    & Under the following assumptions, sequences of certificates satisfying our
    |Chain| specification have no duplicates.
    \begin{itemize}
    \item The input certificate sequence has no duplicates.
      
    \item The certificate to be validated is not in the trusted root store.
    \end{itemize}
    \\ \hline
    Sound chain builder
    & \xfon
    & By construction, the chain builder produces only chains satisfying the
    specification |Chain|.
    \\ \hline
    Complete chain builder
    & \xfon
    & The chain builder generates all certificate lists satisfying the
    specification |Chain|.
    \\ \hline \hline
    Sound semantic checker
    & \xfon
    & If a certificate or chain passes the semantic checker, it satisfies the
    semantic properties.
    \\ \hline
    Complete semantic checker
    & \xfon
    & If a certificate or chain satisfies the semantic properties, it passes the
    semantic checks.
    \\ \hline
  \end{tabularx}
  \label{tab:app-formal-guarantees}
\end{table*}
  
  
  % \begin{table*}[h]
  % \setlength\extrarowheight{1.2pt}
  % \setlength{\tabcolsep}{1.5pt}
  % \centering
  % \sffamily\scriptsize
  % \caption{Semantic properties for a chain of X.509 certificates. [TODO : Fix]}
  % CCP = Certificate Chain Property
  % \vspace{0.5em}
  % \sffamily\scriptsize
  % \begin{tabularx}{\textwidth}{||c||X||}
  % \hline
  % \textbf{Constraint} & \textbf{Description}                                                                                                                                                                                                                                                                                                                      \\ \hline
  % CCP1              & If a certificate contains both a \texttt{Key Usage} extension and an \texttt{Extended Key Usage} extension, then both extensions MUST be processed independently and the certificate MUST only be used for a purpose consistent with both extensions. If there is no purpose consistent with both extensions, then the certificate MUST NOT be used for any purpose. \\ \hline
  % CCP2              & Conforming implementations may choose to reject all \texttt{Version} 1 and \texttt{Version} 2 intermediate CA certificates                                                                                                                                                                                                                                            . \\ \hline
  % CCP3              & The \texttt{PathLenConstraint} field is meaningful only if the \texttt{CA} boolean is asserted and the \texttt{Key Usage} extension, if present, asserts the \texttt{KeyCertSign} bit. In this case, it gives the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.                                          \\ \hline
  % CCP4              & For \texttt{DistributionPoint} field, if the certificate issuer is not the CRL issuer, then the \texttt{CRLIssuer} field MUST be present and contain the Name of the CRL issuer. If the certificate issuer is also the CRL issuer, then conforming CAs MUST omit the \texttt{CRLIssuer} field and MUST include the \texttt{distributionPoint} field.                                                                \\ \hline
  % CCP5              & A certificate MUST NOT appear more than once in a prospective certification path.                                                                                                                                                                                                                                                                  \\ \hline
  % CCP6              & Certificate users MUST be prepared to process the \texttt{Issuer} distinguished name and \texttt{Subject} distinguished name fields to perform name chaining for certification path validation.                                                                                                                                                                      \\ \hline
  % CCP7              & Validate whether root CA certificate is trusted by system.                                                                                                                                                                                                                                                                                         \\ \hline
  % CCP8              & Validate RSA signatures.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % CCP9              & Validate leaf certificate purpose against user's expected certificate purpose.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % CCP10              & Every non-leaf certificate in a chain must be a CA certificate.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % \end{tabularx}
  % \label{ccp}
  % \end{table*}


% \subsection{Examples of inconsistency, ambiguity, and under-specification}
% \label{sect:bad-spec}

% Perhaps unsurprisingly, the specification documents considered 
% are all written in English, 
% which is a natural language that is prone to inconsistency, ambiguity and 
% misinterpretation, and we have indeed observed several instances of 
% problematic clauses in the RFC 5280. Here we give a few illustrative examples.

% Regarding the requirements on serial number, in Section 4.1.2.2, RFC 5280 says:

% \quoteRFC{The serial number MUST be a positive integer assigned by the CA to 
% each certificate...CAs MUST force the serial Number to be a non-negative 
% integer...Non-conforming CAs may issue certificates with serial numbers that 
% are negative or zero. Certificate users SHOULD be prepared to gracefully handle 
% such certificates.}

% The first sentence is inconsistent with the last sentence: one excludes zero, 
% while 
% the other allows it.
% An 
% errata 
% on this has been 
% filed~\footnote{\url{https://www.rfc-editor.org/errata/eid3200}} back in 2012
% but at the time of writing it this does not seem to be included in any RFC 
% updates or clarifications.
%
%has a status of ``held for document updated'' and 
%is 
%not ``verified''.

% We now give an example of requirements that we consider to be ambiguous. 
% Regarding the contents of the CRL distribution points extension, in Section 
% 4.2.1.13, RFC 5280 says:

% \quoteRFC{
% 	A DistributionPoint consists of three fields,
% 	each of which is optional: distributionPoint, reasons, and cRLIssuer.
% 	While each of these fields is optional, a DistributionPoint MUST NOT
% 	consist of only the reasons field; either distributionPoint or
% 	cRLIssuer MUST be present.  If the certificate issuer is not the CRL
% 	issuer, then the cRLIssuer field MUST be present and contain the 
% 	Name
% 	of the CRL issuer.  If the certificate issuer is also the CRL issuer,
% 	then conforming CAs MUST omit the cRLIssuer field and MUST 
% 	include
% 	the distributionPoint field.
% }

% However, it is not immediately clear whether the \emph{\footnotesize 
% \textsf{either ... or ... }}
% clause should be 
% interpreted as an \emph{exclusive or} ($\oplus$), or should it be represented 
% with a \emph{logical or} ($\lor$). If one assumes the \emph{exclusive or} 
% interpretation, 
% then the \emph{\footnotesize \textsf{MUST omit}} clause in the 
% last sentence 
% of the quote seems to be somewhat redundant, as it is already implied by the 
% later
% \emph{\footnotesize \textsf{MUST include}} clause of the same sentence. 
% However, if \emph{logical or} is 
% indeed the correct interpretation, 
% that is, it is acceptable for both \texttt{distributionPoint} 
% and \texttt{cRLIssuer} to be present,
% then the \emph{\footnotesize \textsf{either 
% 		... or ...}} could have been written as \emph{\footnotesize \textsf{at 
% 		least one 
% 		of ... and ...}} to make it less confusing. 
% 	Such interpretation matters 
% 		because it 
% outlines the correct combinations of the fields that constitute the CRL 
% distribution points extension,
% %(in this case the 
% %CRL distribution points), 
% and affects what should be deemed as syntactically correct by the parser.

% Additional, we argue that RFC 5280 also suffers from the problem of 
% under-specification. Many clauses concerning the choice of values and options 
% are stipulated as \emph{producer rules} (\eg, \emph{\footnotesize 
% 	\textsf{conforming CAs must ...}}), but it is not immediately apparent 
% 	whether some or all of these should also be enforced by the consumer. In 
% 	some cases, RFC 5280 mentioned that certificate user should 
% 	\emph{\footnotesize \textsf{gracefully handle}} certain non-conforming 
% 	inputs, without really defining what needs to happen. Does that mean the 
% 	validation should not crash? Should the non-conforming inputs be rejected 
% 	or processed as normal? RFC 5280 is not explicit on those questions. 
% 	Similarly, it also did not make clear on what should the certificate user 
% 	do 
% 	in cases where the certificate itself violates the DER.



  % \subsection{Examples on RFC 5280 rules}
  %  \label{rfcrulex}
  % \begin{table}[h]
  % \setlength\extrarowheight{1.2pt}
  % \setlength{\tabcolsep}{1.5pt}
  % \centering
  % \sffamily\tiny
  %   \caption{(todo: update table) Example of producer and consumer rules\label{tab:prodconex}}
  % \vspace{-1.5em}
  % \sffamily\tiny
  %   \begin{tabular}{c||l||l}
  %   \textbf{Field} &
  %     \textbf{Syntactic Requirement} &
  %     \textbf{Semantic Requirement} \\ \hline
  %   Version &
  %     Version  $::=$  INTEGER  \{  v1(0), v2(1), v3(2)  \} &
  %     \begin{tabular}[c]{@@{}l@@{}}When extensions are used,\\ as expected  in this profile,\\ Version MUST be 3 (value is 2).\end{tabular} \\ \hline
  %   \begin{tabular}[c]{@@{}l@@{}}KeyUsage\\ Extension\end{tabular} &
  %     \begin{tabular}[c]{@@{}l@@{}}KeyUsage $::=$ BIT STRING \{\\ digitalSignature (0), nonRepudiation (1),\\ keyEncipherment (2), dataEncipherment (3),\\ keyAgreement (4), keyCertSign (5), cRLSign (6),\\ encipherOnly (7), decipherOnly (8) \}\end{tabular} &
  %     \begin{tabular}[c]{@@{}l@@{}}When the KeyUsage extension\\ appears in a  certificate, at least\\ one of the bits MUST be set to 1.\end{tabular} \\
  %   \end{tabular}
  %   \vspace{-1.1em}
  %   \end{table}

  
% \begin{table}[h]
%   \setlength\extrarowheight{1.2pt}
%   \setlength{\tabcolsep}{1.5pt}
%   \centering
%   \sffamily\tiny
%     \caption{(todo: update table) Example of syntactic and semantic requirements\label{tab:synsemex}}
%   \vspace{-1.5em}
%   \sffamily\tiny
%     \begin{tabular}{c||l||l}
%     \textbf{Field} &
%       \textbf{Syntactic Requirement} &
%       \textbf{Semantic Requirement} \\ \hline
%     Version &
%       Version  $::=$  INTEGER  \{  v1(0), v2(1), v3(2)  \} &
%       \begin{tabular}[c]{@@{}l@@{}}When extensions are used,\\ as expected  in this profile,\\ Version MUST be 3 (value is 2).\end{tabular} \\ \hline
%     \begin{tabular}[c]{@@{}l@@{}}KeyUsage\\ Extension\end{tabular} &
%       \begin{tabular}[c]{@@{}l@@{}}KeyUsage $::=$ BIT STRING \{\\ digitalSignature (0), nonRepudiation (1),\\ keyEncipherment (2), dataEncipherment (3),\\ keyAgreement (4), keyCertSign (5), cRLSign (6),\\ encipherOnly (7), decipherOnly (8) \}\end{tabular} &
%       \begin{tabular}[c]{@@{}l@@{}}When the KeyUsage extension\\ appears in a  certificate, at least\\ one of the bits MUST be set to 1.\end{tabular} \\
%     \end{tabular}
%     \vspace{-1.1em}
%     \end{table}
