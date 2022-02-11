%% Logistic Stuff

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{chapter}.\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
{\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\victor}[2][nolabel]{%
{\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}}
\newcommand{\todo}[2][nolabel]{%
{\color{C1} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) TODO: } #2 \textbf{$]$}}}


%% LaTeX stuff


\renewcommand{\hscodestyle}{\small}

%% Make lhs2TeX put my own env around code blocks.
\makeatletter
\newenvironment{myownhscode}%
  {\hsnewpar\abovedisplayskip
   %\advance\leftskip\mathindent
   \hscodestyle
   \let\hspre\(\let\hspost\)%
   \pboxed}
  {\endpboxed%
   \hsnewpar\belowdisplayskip
   \ignorespacesafterend}
\newenvironment{myownhscodeFig}%
  {\vspace*{-5.7em}\hscodestyle
   \let\hspre\(\let\hspost\)%
   \pboxed}
  {\endpboxed\ignorespacesafterend}
\makeatother
\sethscode{myownhscode}


\newenvironment{myhs*}[1][0.95\textwidth]{%
\begin{minipage}{#1}%
}{%
\end{minipage}%
}

\newenvironment{myhsFig}[1][0.95\textwidth]{%
\sethscode{myownhscodeFig}%
\begin{myhs*}[#1]%
}{%
\end{myhs*}%
\sethscode{myownhscode}
}

\newenvironment{myhs}[1][0.95\textwidth]{%
\begin{myhs*}[#1]  
}{%
\end{myhs*}%
}

