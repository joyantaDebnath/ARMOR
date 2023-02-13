\documentclass[conference,compsoc]{IEEEtran1.8b}
\usepackage{multirow}
\usepackage{graphicx}
\usepackage[normalem]{ulem}
\useunder{\uline}{\ul}{}
\usepackage[usenames, dvipsnames, table, xcdraw]{xcolor}
\usepackage{cite}
\usepackage{amsmath}
\usepackage{algorithmic}
\usepackage{listings}
\usepackage{alltt, amssymb, xspace, setspace,epsfig,multirow,array,color}
\usepackage[]{algorithm2e}
\usepackage{hhline}
\usepackage[draft]{hyperref}
\usepackage{longtable}
\usepackage{pifont}
\usepackage{longtable}
\usepackage{listings}
\definecolor{codegreen}{rgb}{0,0.6,0}
\definecolor{codegray}{rgb}{0.5,0.5,0.5}
\definecolor{codepurple}{rgb}{0.58,0,0.82}
\definecolor{backcolour}{rgb}{0.95,0.95,0.92}
\usepackage[T1]{fontenc}     
\usepackage{babel}

\usepackage{tabularx}



%\lstdefinestyle{mystyle}{
%    backgroundcolor=\color{backcolour},   
%    commentstyle=\color{codegreen},
%    keywordstyle=\color{magenta},
%    numberstyle=\footnotesize\color{codegray},
%    stringstyle=\color{codepurple},
%    basicstyle=\rmfamily\footnotesize,
%    breakatwhitespace=false,         
%    breaklines=true,                 
%    captionpos=b,                    
%    keepspaces=true,                 
%    numbers=left,                    
%    numbersep=5pt,                  
%    showspaces=false,                
%    showstringspaces=false,
%    showtabs=false,                  
%    tabsize=2
%}

\usepackage[threshold=0]{csquotes}

\newcommand{\quoteRFC}[1]{\blockquote{\textit{{\sffamily\scriptsize``#1''}}}}

\makeatletter
\def\textSq#1{%
\begingroup% make boxes and lengths local
\setlength{\fboxsep}{0.3ex}% SET ANY DESIRED PADDING HERE
\setbox1=\hbox{#1}% save the contents
\setlength{\@tempdima}{\maxof{\wd1}{\ht1+\dp1}}% size of the box
\setlength{\@tempdimb}{(\@tempdima-\ht1+\dp1)/2}% vertical raise
\raise-\@tempdimb\hbox{\fbox{\vbox to \@tempdima{%
  \vfil\hbox to \@tempdima{\hfil\copy1\hfil}\vfil}}}%
\endgroup%
}
\def\Sq#1{\textSq{\ensuremath{#1}}}%
\makeatother


\newcommand{\sbskip}{\vspace*{0.02in}}
\newcommand{\mbskip}{\vspace*{0.04in}}
%\newcommand{\nsubsubsection}[1]{\mbskip\subsubsection{#1}\sbskip}
\newcommand{\nsubsubsection}[1]{\subsubsection{#1}}

\usepackage[caption=false]{subfig}
\usepackage{graphicx}
\usepackage{float}
\usepackage{multicol} 
\usepackage{smartdiagram} 
\usepackage[shortlabels]{enumitem}
\usepackage{cleveref}

\usepackage[normalem]{ulem}

%%%%%%% General stuff
\newcommand{\etal}{\textit{et al.}\xspace}
\newcommand{\ie}{\textit{i.e.}\xspace}
\newcommand{\eg}{\textit{e.g.}\xspace}
\newcommand{\viz}{\textit{viz.}\xspace}
\newcommand{\etc}{\textit{etc.}\xspace}

\newcommand{\pred}[1]{\ensuremath{\mathsf{#1}}\xspace}

\newcommand{\XFiveOhNine}{X.509\xspace}
\newcommand{\XSixNineOh}{X.690\xspace}

\newcommand{\todo}[1]{\vspace*{0.05in}\noindent\textcolor{red}{\textbf{Todo}}\textcolor{blue}{:
		#1.}\xspace}

\newcommand{\says}[2]{\noindent\textcolor{orange}{\textbf{#1 says: 
		}}\textcolor{blue}{#2.}\xspace}
	
\newcommand{\cU}{\ensuremath{\mathcal{C}}\xspace}
\newcommand{\iproblem}{\pred{CVEq}}
\newcommand{\cproblem}{\pred{CVCor}}
\newcommand{\rimplementation}{\ensuremath{I_\pred{ref}}\xspace}
\newcommand{\idom}{\ensuremath{\mathcal{I}}\xspace}
\newcommand{\QFFOL}{\pred{QFFOL}}

\newcommand{\ceres}{\ensuremath{\mathsf{CERES}}\xspace}
% \newcommand{\says}[2]{\noindent\textcolor{red}{\textbf{#1 says: }}\textcolor{blue}{#2.}\xspace}

\newcommand{\censys}{\ensuremath{\mathsf{Censys}}\xspace}
\newcommand{\frankencert}{\ensuremath{\mathsf{Frankencert}}\xspace}
\newcommand{\mbedtls}{\ensuremath{\mathsf{mbedTLS}}\xspace}
\newcommand{\openssl}{\ensuremath{\mathsf{OpenSSL}}\xspace}
\newcommand{\gnutls}{\ensuremath{\mathsf{GnuTLS}}\xspace}

\newcommand{\parsec}{\ensuremath{\mathsf{Parsec}}\xspace}
\newcommand{\antlr}{\ensuremath{\mathsf{ANTLR}}\xspace}

\newcommand{\python}{\ensuremath{\mathsf{Python}}\xspace}
\newcommand{\haskell}{\ensuremath{\mathsf{Haskell}}\xspace}
\newcommand{\cvcfour}{\ensuremath{\mathsf{CVC4}}\xspace}
\newcommand{\lfsc}{\ensuremath{\mathsf{LFSC}}\xspace}
\newcommand{\stringprep}{\ensuremath{\mathsf{stringprep}}\xspace}

\newcommand{\parser}{\ensuremath{\mathsf{Parser}}\xspace}
\newcommand{\sem}{\ensuremath{\mathsf{Semantic\mhyphen checker}}\xspace}
\newcommand{\chain}{\ensuremath{\mathsf{Chain\mhyphen builder}}\xspace}
\newcommand{\driver}{\ensuremath{\mathsf{Driver}}\xspace}

\newcommand{\pysmt}{\ensuremath{\mathsf{PySMT}}\xspace}
\newcommand{\smtlib}{\ensuremath{\mathsf{SMT\mhyphen LIB}}\xspace}
\newcommand{\certchainres}{\ensuremath{\mathsf{cert\mhyphen chain \mhyphen resolver}}\xspace}

\mathchardef\mhyphen="2D % Define a "math hyphen"


% \newcommand{openssl}{OpenSSL\xspace}

%\newcommand{\pmodule}{\ensuremath{\mathsf{parser module}}\xspace}
%\newcommand{\smodule}{\ensuremath{\mathsf{semantic-checker module}}\xspace}
%\newcommand{\dmodule}{\ensuremath{\mathsf{driver module}}\xspace}
%\newcommand{\cmodule}{\ensuremath{\mathsf{chain-builder module}}\xspace}



%%% ===> Code listing style definitions
%\renewcommand{\lstlistingname}{\listingPrefix}
%\lstdefinestyle{customc}{
%	belowcaptionskip=1\baselineskip,
%	breaklines=true,
%	frame=single,
%	tabsize=1,
%	xleftmargin=\parindent,
%	showstringspaces=false,
%	basicstyle=\scriptsize\ttfamily,
%	keywordstyle=\color{purple!75!black}\slshape,
%	commentstyle=\itshape\color{orange!65!black}\mdseries,
%	identifierstyle=\color{blue!60!black},
%	stringstyle=\color{green!60!yellow!50!black},
%	language=Python, numbers=left, numberstyle=\scriptsize, numbersep=3pt, framexleftmargin=10pt, captionpos=b
%}

\lstdefinestyle{customc}{
	belowcaptionskip=0.5\baselineskip,
	breaklines=true,
	tabsize=2,
	xleftmargin=\parindent,
	language=Python,
	showstringspaces=false,
	basicstyle=\scriptsize\ttfamily\bfseries,
	keywordstyle=\color{purple!75!black}\slshape,
	commentstyle=\itshape\color{orange!65!black}\mdseries,
	identifierstyle=\color{blue!60!black},
	stringstyle=\color{green!60!yellow!50!black},
	numbers=left, numberstyle=\scriptsize, numbersep=3pt, framexleftmargin=10pt, captionpos=b
}

%%% <=== Code listing style definitions


\setcounter{secnumdepth}{3}

\pagestyle{plain}

\newcommand{\comment}[1]{}

\def\UrlBreaks{\do\/\do-}

\begin{document}
%
% paper title
% Titles are generally capitalized except for words such as a, an, and, as,
% at, but, by, for, in, nor, of, on, or, the, to and up, which are usually
% not capitalized unless they are the first or last word of the title.
% Linebreaks \\ can be used within to get better formatting as desired.
% Do not put math or special symbols in the title.
%\title{SymCert: A Principled Approach to identify problems in X.509 Certificate 
%Chain 
%Validation}

%\title{Exposing Noncompliance in Small Footprint Implementations of 
%\XFiveOhNine 
%Certificate Validation \\ 
%	{\Large Or, How to tell if your embedded SSL/TLS libraries are 
%	negligent with SymCerts}
%}

\title{
A Formally Verified X.509 Implementation: AERES and its Application in Differential Testing
}

% author names and affiliations
% use a multiple column layout for up to three different
% affiliations
%\author{
%paper \#231
%}

% conference papers do not typically use \thanks and this command
% is locked out in conference mode. If really needed, such as for
% the acknowledgment of grants, issue a \IEEEoverridecommandlockouts
% after \documentclass

% for over three affiliations, or if they all won't fit within the width
% of the page, use this alternative format:
% 
\author{
%\IEEEauthorblockN{
%	Name1\IEEEauthorrefmark{1}
%	Name2\IEEEauthorrefmark{2}
%}
%\IEEEauthorblockA{\texttt{email-addr}, affliation\IEEEauthorrefmark{1}}
}

% use for special paper notices
%\IEEEspecialpapernotice{(Invited Paper)}

% make the title area
\maketitle

%\begin{abstract} --
%\XFiveOhNine is important.
%\end{abstract}

\input{abstract}
\input{introduction} 
\input{background}
\input{overview}
\input{approach-details}
\input{implementation}
\input{evaluation}
\input{discussion}
\input{related-work}
\input{conclusion}



%\section*{Acknowledgment}

%\todo{finish this list}


% references section
%\bibliographystyle{abbrv}
\bibliographystyle{IEEEtran}
%\bibliography{ref}

\input{appendix}


% can use a bibliography generated by BibTeX as a .bbl file
% BibTeX documentation can be easily obtained at:
% http://mirror.ctan.org/biblio/bibtex/contrib/doc/
% The IEEEtran BibTeX style support page is at:
% http://www.michaelshell.org/tex/ieeetran/bibtex/
%\bibliographystyle{IEEEtran}
% argument is your BibTeX string definitions and bibliography database(s)
%\bibliography{IEEEabrv,../bib/paper}
%
% <OR> manually copy in the resultant .bbl file
% set second argument of \begin to the number of references
% (used to reserve space for the reference number labels box)
%\begin{thebibliography}{1}
%
%\bibitem{IEEEhowto:kopka}
%H.~Kopka and P.~W. Daly, \emph{A Guide to \LaTeX}, 3rd~ed.\hskip 1em plus
%  0.5em minus 0.4em\relax Harlow, England: Addison-Wesley, 1999.
%
%\end{thebibliography}


% that's all folks
\end{document}

\grid
