\section{Evaluation and Results}

\subsection{Runtime Evaluation}

\begin{table*}[]
    \centering
    \sffamily\footnotesize
        \setlength\extrarowheight{1.5pt}
        \setlength{\tabcolsep}{1.5pt}
        \caption{Runtime Analysis on 100000 Certificate Chains}
        \vspace{4pt}
        \label{t1}
        \tiny
        \sffamily\footnotesize
    \centering
    \begin{tabular}{cc||l||cccccc||c||cccccc||}
    \cline{3-16}
                                                                        &                   &                     & \multicolumn{6}{c||}{\textbf{Accepted}}                                                                                                                                                                                                                                                                                                                                                                                                        &                     & \multicolumn{6}{c||}{\textbf{Rejected}}                                                                                                                                                                                                                                                                                                                                                                                                        \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textbf{Library}}                              & \textbf{Language} &                     & \multicolumn{1}{c||}{\textbf{Count}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ sec\end{tabular}}} & \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ sec\end{tabular}} &                     & \multicolumn{1}{c||}{\textbf{Count}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ sec\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ sec\end{tabular}}} & \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ sec\end{tabular}} \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{BoringSSL}}                            & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{{\color[HTML]{333333} 0.004}}                               & \multicolumn{1}{c||}{1.119}                                                      & \multicolumn{1}{c||}{0.029}                                                       & \multicolumn{1}{c||}{0.029}                                                         & 0.009                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{0.004}                                                      & \multicolumn{1}{c||}{0.340}                                                      & \multicolumn{1}{c||}{0.028}                                                       & \multicolumn{1}{c||}{0.028}                                                         & 0.006                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{GnuTLS}}                               & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{{\color[HTML]{333333} 0.004}}                               & \multicolumn{1}{c||}{0.340}                                                      & \multicolumn{1}{c||}{0.028}                                                       & \multicolumn{1}{c||}{0.028}                                                         & 0.006                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{{\color[HTML]{333333} 0.001}}                               & \multicolumn{1}{c||}{0.952}                                                      & \multicolumn{1}{c||}{0.015}                                                       & \multicolumn{1}{c||}{0.014}                                                         & 0.006                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{036400} \textit{MatrixSSL}}}     & C/C++             &                     & \multicolumn{1}{c||}{74633}          & \multicolumn{1}{c||}{0.009}                                                      & \multicolumn{1}{c||}{0.257}                                                      & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.011}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.011}}                                  & 0.003                                                       &                     & \multicolumn{1}{c||}{25367}          & \multicolumn{1}{c||}{0.003}                                                      & \multicolumn{1}{c||}{{\color[HTML]{333333} 0.065}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                  & 0.004                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{036400} \textit{mbed TLS}}}      & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{0.008}                                                      & \multicolumn{1}{c||}{{\color[HTML]{333333} 0.125}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                  & 0.002                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{0.007}                                                      & \multicolumn{1}{c||}{0.129}                                                      & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.008}}                                  & 0.002                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{OpenSSL}}                              & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{0.026}                                                      & \multicolumn{1}{c||}{1.014}                                                      & \multicolumn{1}{c||}{0.051}                                                       & \multicolumn{1}{c||}{0.050}                                                         & 0.011                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{0.026}                                                      & \multicolumn{1}{c||}{0.491}                                                      & \multicolumn{1}{c||}{0.051}                                                       & \multicolumn{1}{c||}{0.049}                                                         & 0.011                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{036400} \textit{WolfSSL}}}       & C/C++             &                     & \multicolumn{1}{c||}{91480}          & \multicolumn{1}{c||}{0.006}                                                      & \multicolumn{1}{c||}{1.039}                                                      & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                  & 0.006                                                       &                     & \multicolumn{1}{c||}{8520}           & \multicolumn{1}{c||}{0.007}                                                      & \multicolumn{1}{c||}{0.072}                                                      & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.009}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 0.008}}                                  & 0.002                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{333333} \textit{Crypto}}}        & Go                &                     & \multicolumn{1}{c||}{68045}          & \multicolumn{1}{c||}{0.187}                                                      & \multicolumn{1}{c||}{{\color[HTML]{680100} 8.891}}                               & \multicolumn{1}{c||}{0.269}                                                       & \multicolumn{1}{c||}{0.260}                                                         & 0.101                                                       &                     & \multicolumn{1}{c||}{31955}          & \multicolumn{1}{c||}{0.006}                                                      & \multicolumn{1}{c||}{3.484}                                                      & \multicolumn{1}{c||}{0.194}                                                       & \multicolumn{1}{c||}{0.246}                                                         & 0.138                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{680100} \textit{Bouncy Castle}}} & Java              &                     & \multicolumn{1}{c||}{67888}          & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.573}}                               & \multicolumn{1}{c||}{{\color[HTML]{680100} 6.019}}                               & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.956}}                                & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.920}}                                  & 0.382                                                       &                     & \multicolumn{1}{c||}{32112}          & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.251}}                               & \multicolumn{1}{c||}{{\color[HTML]{680100} 5.714}}                               & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.709}}                                & \multicolumn{1}{c||}{{\color[HTML]{680100} 0.627}}                                  & 0.219                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{Sun}}                                  & Java              &                     & \multicolumn{1}{c||}{67888}          & \multicolumn{1}{c||}{0.129}                                                      & \multicolumn{1}{c||}{2.140}                                                      & \multicolumn{1}{c||}{0.285}                                                       & \multicolumn{1}{c||}{0.271}                                                         & 0.085                                                       &                     & \multicolumn{1}{c||}{32112}          & \multicolumn{1}{c||}{0.147}                                                      & \multicolumn{1}{c||}{1.882}                                                      & \multicolumn{1}{c||}{0.215}                                                       & \multicolumn{1}{c||}{0.194}                                                         & 0.075                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{Certvalidator}}                        & Python            &                     & \multicolumn{1}{c||}{74951}          & \multicolumn{1}{c||}{0.221}                                                      & \multicolumn{1}{c||}{2.855}                                                      & \multicolumn{1}{c||}{0.269}                                                       & \multicolumn{1}{c||}{0.263}                                                         & 0.060                                                       &                     & \multicolumn{1}{c||}{25049}          & \multicolumn{1}{c||}{0.143}                                                      & \multicolumn{1}{c||}{1.779}                                                      & \multicolumn{1}{c||}{0.254}                                                       & \multicolumn{1}{c||}{0.254}                                                         & 0.061                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{333333} \textit{CERES}}}         & Python            &                     & \multicolumn{1}{c||}{67991}          & \multicolumn{1}{c||}{0.033}                                                      & \multicolumn{1}{c||}{5.735}                                                      & \multicolumn{1}{c||}{0.755}                                                       & \multicolumn{1}{c||}{0.821}                                                         & 0.338                                                       &                     & \multicolumn{1}{c||}{32009}          & \multicolumn{1}{c||}{0.151}                                                      & \multicolumn{1}{c||}{5.621}                                                      & \multicolumn{1}{c||}{0.541}                                                       & \multicolumn{1}{c||}{0.594}                                                         & 0.263                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{00009B} \textit{AERES}}}         & Agda              &                     & \multicolumn{1}{c||}{67591}          & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.034}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 5.156}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.364}}                                & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.351}}                                  & 0.093                                                       & \multirow{-14}{*}{} & \multicolumn{1}{c||}{32409}          & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.038}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 1.977}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.192}}                                & \multicolumn{1}{c||}{{\color[HTML]{00009B} 0.180}}                                  & 0.093                                                       \\ \hline
    \end{tabular}
\end{table*}




\subsection{Memory Evaluation}

\begin{table*}[]
    \centering
    \sffamily\footnotesize
        \setlength\extrarowheight{1.5pt}
        \setlength{\tabcolsep}{1.5pt}
        \caption{Memory Analysis on 100000 Certificate Chains}
        \vspace{4pt}
        \label{t1}
        \tiny
        \sffamily\footnotesize
    \centering
    \begin{tabular}{cc||c||cccccc||c||cccccc||}
    \cline{3-16}
    \textbf{}                                                           & \textbf{}         &                     & \multicolumn{6}{c||}{\textbf{Accepted}}                                                                                                                                                                                                                                                                                                                                                                                                   &                     & \multicolumn{6}{c||}{\textbf{Rejected}}                                                                                                                                                                                                                                                                                                                                                                                                   \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textbf{Library}}                              & \textbf{Language} &                     & \multicolumn{1}{c||}{\textbf{Count}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ mb\end{tabular}}} & \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ mb\end{tabular}} &                     & \multicolumn{1}{c||}{\textbf{Count}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Min\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Max\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Mean\\ mb\end{tabular}}} & \multicolumn{1}{c||}{\textbf{\begin{tabular}[c]{@@{}c@@{}}Median\\ mb\end{tabular}}} & \textbf{\begin{tabular}[c]{@@{}c@@{}}S.D.\\ mb\end{tabular}} \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{BoringSSL}}                            & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{4.01}                                                      & \multicolumn{1}{c||}{4.49}                                                      & \multicolumn{1}{c||}{4.21}                                                       & \multicolumn{1}{c||}{4.21}                                                         & 0.06                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{3.62}                                                      & \multicolumn{1}{c||}{4.36}                                                      & \multicolumn{1}{c||}{4.13}                                                       & \multicolumn{1}{c||}{4.17}                                                         & 0.12                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{GnuTLS}}                               & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{8.18}                                                      & \multicolumn{1}{c||}{8.82}                                                      & \multicolumn{1}{c||}{8.51}                                                       & \multicolumn{1}{c||}{8.52}                                                         & 0.13                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{4.50}                                                      & \multicolumn{1}{c||}{8.57}                                                      & \multicolumn{1}{c||}{7.74}                                                       & \multicolumn{1}{c||}{8.00}                                                         & 0.91                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{036400} \textit{MatrixSSL}}}     & C/C++             &                     & \multicolumn{1}{c||}{74633}          & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.02}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.50}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.31}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.32}}                                  & 0.08                                                       &                     & \multicolumn{1}{c||}{25367}          & \multicolumn{1}{c||}{{\color[HTML]{036400} 2.34}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.49}}                               & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.17}}                                & \multicolumn{1}{c||}{{\color[HTML]{036400} 3.29}}                                  & 0.30                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{mbed TLS}}                             & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{3.82}                                                      & \multicolumn{1}{c||}{4.20}                                                      & \multicolumn{1}{c||}{3.99}                                                       & \multicolumn{1}{c||}{3.98}                                                         & 0.07                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{3.80}                                                      & \multicolumn{1}{c||}{4.19}                                                      & \multicolumn{1}{c||}{4.00}                                                       & \multicolumn{1}{c||}{4.01}                                                         & 0.07                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{OpenSSL}}                              & C/C++             &                     & \multicolumn{1}{c||}{74956}          & \multicolumn{1}{c||}{6.72}                                                      & \multicolumn{1}{c||}{7.51}                                                      & \multicolumn{1}{c||}{6.90}                                                       & \multicolumn{1}{c||}{6.89}                                                         & 0.08                                                       &                     & \multicolumn{1}{c||}{25044}          & \multicolumn{1}{c||}{6.60}                                                      & \multicolumn{1}{c||}{7.06}                                                      & \multicolumn{1}{c||}{6.87}                                                       & \multicolumn{1}{c||}{6.87}                                                         & 0.08                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{WolfSSL}}                              & C/C++             &                     & \multicolumn{1}{c||}{91480}          & \multicolumn{1}{c||}{7.86}                                                      & \multicolumn{1}{c||}{8.61}                                                      & \multicolumn{1}{c||}{8.35}                                                       & \multicolumn{1}{c||}{8.41}                                                         & 0.17                                                       &                     & \multicolumn{1}{c||}{8520}           & \multicolumn{1}{c||}{8.27}                                                      & \multicolumn{1}{c||}{8.58}                                                      & \multicolumn{1}{c||}{8.44}                                                       & \multicolumn{1}{c||}{8.46}                                                         & 0.06                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{Crypto}}                               & Go                &                     & \multicolumn{1}{c||}{68045}          & \multicolumn{1}{c||}{59.59}                                                     & \multicolumn{1}{c||}{68.30}                                                     & \multicolumn{1}{c||}{64.41}                                                      & \multicolumn{1}{c||}{62.89}                                                        & 2.54                                                       &                     & \multicolumn{1}{c||}{31955}          & \multicolumn{1}{c||}{60.52}                                                     & \multicolumn{1}{c||}{68.29}                                                     & \multicolumn{1}{c||}{64.10}                                                      & \multicolumn{1}{c||}{62.66}                                                        & 2.53                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{680100} \textit{Bouncy Castle}}} & Java              &                     & \multicolumn{1}{c||}{67888}          & \multicolumn{1}{c||}{{\color[HTML]{680100} 84.34}}                              & \multicolumn{1}{c||}{{\color[HTML]{680100} 130.99}}                             & \multicolumn{1}{c||}{{\color[HTML]{680100} 105.79}}                              & \multicolumn{1}{c||}{{\color[HTML]{680100} 101.91}}                                & 8.42                                                       &                     & \multicolumn{1}{c||}{32112}          & \multicolumn{1}{c||}{{\color[HTML]{680100} 82.55}}                              & \multicolumn{1}{c||}{{\color[HTML]{680100} 119.71}}                             & \multicolumn{1}{c||}{{\color[HTML]{680100} 89.96}}                               & \multicolumn{1}{c||}{{\color[HTML]{680100} 86.02}}                                 & 6.44                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{Sun}}                                  & Java              &                     & \multicolumn{1}{c||}{67888}          & \multicolumn{1}{c||}{47.50}                                                     & \multicolumn{1}{c||}{62.83}                                                     & \multicolumn{1}{c||}{53.60}                                                      & \multicolumn{1}{c||}{53.19}                                                        & 1.19                                                       &                     & \multicolumn{1}{c||}{32112}          & \multicolumn{1}{c||}{44.42}                                                     & \multicolumn{1}{c||}{61.52}                                                     & \multicolumn{1}{c||}{50.30}                                                      & \multicolumn{1}{c||}{49.88}                                                        & 1.86                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{Certvalidator}}                        & Python            &                     & \multicolumn{1}{c||}{74951}          & \multicolumn{1}{c||}{26.67}                                                     & \multicolumn{1}{c||}{28.42}                                                     & \multicolumn{1}{c||}{27.06}                                                      & \multicolumn{1}{c||}{27.04}                                                        & 0.14                                                       &                     & \multicolumn{1}{c||}{25049}          & \multicolumn{1}{c||}{23.90}                                                     & \multicolumn{1}{c||}{27.30}                                                     & \multicolumn{1}{c||}{26.62}                                                      & \multicolumn{1}{c||}{26.79}                                                        & 0.71                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{\textit{CERES}}                                & Python            &                     & \multicolumn{1}{c||}{67991}          & \multicolumn{1}{c||}{21.03}                                                     & \multicolumn{1}{c||}{40.70}                                                     & \multicolumn{1}{c||}{39.08}                                                      & \multicolumn{1}{c||}{39.45}                                                        & 2.24                                                       &                     & \multicolumn{1}{c||}{32009}          & \multicolumn{1}{c||}{21.02}                                                     & \multicolumn{1}{c||}{31.79}                                                     & \multicolumn{1}{c||}{27.03}                                                      & \multicolumn{1}{c||}{28.04}                                                        & 3.23                                                       \\ \cline{1-2} \cline{4-9} \cline{11-16} 
    \multicolumn{1}{||c||}{{\color[HTML]{00009B} \textit{AERES}}}         & Agda              &                     & \multicolumn{1}{c||}{67591}          & \multicolumn{1}{c||}{{\color[HTML]{00009B} 30.98}}                              & \multicolumn{1}{c||}{{\color[HTML]{00009B} 88.49}}                              & \multicolumn{1}{c||}{{\color[HTML]{00009B} 46.77}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 45.99}}                                 & 3.77                                                       & \multirow{-14}{*}{} & \multicolumn{1}{c||}{32409}          & \multicolumn{1}{c||}{{\color[HTML]{00009B} 17.95}}                              & \multicolumn{1}{c||}{{\color[HTML]{00009B} 63.00}}                              & \multicolumn{1}{c||}{{\color[HTML]{00009B} 32.81}}                               & \multicolumn{1}{c||}{{\color[HTML]{00009B} 24.35}}                                 & 12.95                                                      \\ \hline
    \end{tabular}
\end{table*}
