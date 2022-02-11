\documentclass[11pt]{article}%

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%
%
% Our formatting rules and included packages.
%
%include polycode.fmt
%include src/stylish.lhs
%include src/definitions.lhs
%
% My emacs auctex mode uses this lhsinclude command to
% understand multioart documents.
%
\newcommand{\lhsinclude}[1]{}
%
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

\title{Your Title}
\author{You and your team}
\date{\today}

\begin{document}
\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%
%
% Body
%
%include src/body.lhs
\lhsinclude{body.lhs}
%
%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%

%% \bibliography{references}
\end{document}
