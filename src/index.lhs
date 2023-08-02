%% bare_conf_compsoc.tex
%% V1.4b
%% 2015/08/26
%% by Michael Shell
%% See:
%% http://www.michaelshell.org/
%% for current contact information.
%%
%% This is a skeleton file demonstrating the use of IEEEtran.cls
%% (requires IEEEtran.cls version 1.8b or later) with an IEEE Computer
%% Society conference paper.
%%
%% Support sites:
%% http://www.michaelshell.org/tex/ieeetran/
%% http://www.ctan.org/pkg/ieeetran
%% and
%% http://www.ieee.org/

%%*************************************************************************
%% Legal Notice:
%% This code is offered as-is without any warranty either expressed or
%% implied; without even the implied warranty of MERCHANTABILITY or
%% FITNESS FOR A PARTICULAR PURPOSE! 
%% User assumes all risk.
%% In no event shall the IEEE or any contributor to this code be liable for
%% any damages or losses, including, but not limited to, incidental,
%% consequential, or any other damages, resulting from the use or misuse
%% of any information contained here.
%%
%% All comments are the opinions of their respective authors and are not
%% necessarily endorsed by the IEEE.
%%
%% This work is distributed under the LaTeX Project Public License (LPPL)
%% ( http://www.latex-project.org/ ) version 1.3, and may be freely used,
%% distributed and modified. A copy of the LPPL, version 1.3, is included
%% in the base LaTeX documentation of all distributions of LaTeX released
%% 2003/12/01 or later.
%% Retain all contribution notices and credits.
%% ** Modified files should be clearly indicated as such, including  **
%% ** renaming them and changing author support contact information. **
%%*************************************************************************


% *** Authors should verify (and, if needed, correct) their LaTeX system  ***
% *** with the testflow diagnostic prior to trusting their LaTeX platform ***
% *** with production work. The IEEE's font choices and paper sizes can   ***
% *** trigger bugs that do not appear when using other class files.       ***                          ***
% The testflow support page is at:
% http://www.michaelshell.org/tex/testflow/



\documentclass[conference,compsoc]{IEEEtran}
%include polycode.fmt

\usepackage{multirow}
\usepackage[T1]{fontenc} 
\usepackage{graphicx}
\usepackage[british]{babel}
\usepackage{hyperref}
\usepackage[normalem]{ulem}
\useunder{\uline}{\ul}{}
\usepackage[usenames, dvipsnames, table, xcdraw]{xcolor}
% \usepackage{cite}
\usepackage{amsmath}
\usepackage{algorithmic}
\usepackage{listings}
\usepackage{alltt, amssymb, xspace, setspace,epsfig,multirow,array,color}
\usepackage[]{algorithm2e}
\usepackage{hhline}
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
\usepackage{caption}
\captionsetup[figure]{skip=0pt} % Adjust for your preferred distance

\usepackage{tabularx}

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
\usepackage{tabularx}

\usepackage[normalem]{ulem}

%%%%%%% General stuff
\newcommand{\etal}{\textit{et al.}\xspace}
\newcommand{\ie}{\textit{i.e.}\xspace}
\newcommand{\eg}{\textit{e.g.}\xspace}
\newcommand{\viz}{\textit{viz.}\xspace}
\newcommand{\etc}{\textit{etc.}\xspace}

\newcommand{\pred}[1]{\ensuremath{\mathsf{#1}}\xspace}

% \newcommand{\todo}[1]{\vspace*{0.05in}\noindent\textcolor{red}{\textbf{Todo}}\textcolor{blue}{:
% 		#1.}\xspace}

\newcommand{\says}[2]{\noindent\textcolor{orange}{\textbf{#1 says: 
		}}\textcolor{blue}{#2.}\xspace}
	


\newcommand{\iproblem}{\pred{CVEq}}
\newcommand{\cproblem}{\pred{CVCor}}
\newcommand{\rimplementation}{\ensuremath{I_\pred{ref}}\xspace}
\newcommand{\idom}{\ensuremath{\mathcal{I}}\xspace}
\newcommand{\QFFOL}{\pred{QFFOL}}

\newcommand{\xfon}{X.509\xspace}
\newcommand{\xsno}{X.690\xspace}
\newcommand{\der}{DER\xspace}
\newcommand{\pem}{PEM\xspace}
\newcommand{\ber}{BER\xspace}
\newcommand{\asnone}{ASN.1\xspace}
\newcommand{\basesf}{Base64\xspace}

\newcommand{\soundness}{\textit{Soundness}\xspace}
\newcommand{\completeness}{\textit{Completeness}\xspace}

\newcommand{\fuzzing}{\textit{fuzzing}\xspace}
\newcommand{\symex}{\textit{symbolic execution}\xspace}

\newcommand{\armor}{\ensuremath{\mathsf{ARMOR}}\xspace}
\newcommand{\ceres}{\ensuremath{\mathsf{CERES}}\xspace}
\newcommand{\mbedtls}{\ensuremath{\mathsf{Mbed\mspace{4mu} TLS}}\xspace}
\newcommand{\openssl}{\ensuremath{\mathsf{OpenSSL}}\xspace}
\newcommand{\gnutls}{\ensuremath{\mathsf{GnuTLS}}\xspace}
\newcommand{\boringssl}{\ensuremath{\mathsf{BoringSSL}}\xspace}
\newcommand{\matrixssl}{\ensuremath{\mathsf{MatrixSSL}}\xspace}
\newcommand{\wolfssl}{\ensuremath{\mathsf{WolfSSL}}\xspace}
\newcommand{\certvalidator}{\ensuremath{\mathsf{Certvalidator}}\xspace}
\newcommand{\sun}{\ensuremath{\mathsf{Sun}}\xspace}
\newcommand{\bouncycastle}{\ensuremath{\mathsf{BouncyCastle}}\xspace}
\newcommand{\crypto}{\ensuremath{\mathsf{Crypto}}\xspace}

\newcommand{\cryptography}{\ensuremath{\mathsf{Cryptography}}\xspace}


\newcommand{\censys}{\ensuremath{\mathsf{Censys}}\xspace}
\newcommand{\frankencert}{\ensuremath{\mathsf{Frankencert}}\xspace}
\newcommand{\morpheus}{\ensuremath{\mathsf{Morpheus}}\xspace}
\newcommand{\coq}{\ensuremath{\mathsf{Coq}}\xspace}
\newcommand{\ghc}{\ensuremath{\mathsf{GHC}}\xspace}

\newcommand{\stringprep}{\ensuremath{\mathsf{StringPrep}}\xspace}

\newcommand{\python}{\texttt{Python}\xspace}
\newcommand{\cpp}{\texttt{C\textbackslash C++}\xspace}
\newcommand{\haskell}{\texttt{Haskell}\xspace}
\newcommand{\agda}{\texttt{Agda}\xspace}

\newcommand{\parser}{\ensuremath{\mathsf{Parser}}\xspace}
\newcommand{\semantic}{\ensuremath{\mathsf{Semantic\mhyphen checker}}\xspace}
\newcommand{\chain}{\ensuremath{\mathsf{Chain\mhyphen builder}}\xspace}
\newcommand{\driver}{\ensuremath{\mathsf{Driver}}\xspace}
\newcommand{\stringtransformer}{\ensuremath{\mathsf{String\mhyphen transformer}}\xspace}

\newcommand{\smtlib}{\ensuremath{\mathsf{SMT\mhyphen LIB}}\xspace}
\newcommand{\smtsolver}{\ensuremath{\mathsf{SMT\mhyphen Solver}}\xspace}
\newcommand{\certchainres}{\ensuremath{\mathsf{cert\mhyphen chain \mhyphen resolver}}\xspace}

\mathchardef\mhyphen="2D % Define a "math hyphen"

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

% Some very useful LaTeX packages include:
% (uncomment the ones you want to load)


% *** MISC UTILITY PACKAGES ***
% 
% \usepackage{ifpdf}
% Heiko Oberdiek's ifpdf.sty is very useful if you need conditional
% compilation based on whether the output is pdf or dvi.
% usage:
% \ifpdf
%   % pdf code
% \else
%   % dvi code
% \fi
% The latest version of ifpdf.sty can be obtained from:
% http://www.ctan.org/pkg/ifpdf
% Also, note that IEEEtran.cls V1.7 and later provides a builtin
% \ifCLASSINFOpdf conditional that works the same way.
% When switching from latex to pdflatex and vice-versa, the compiler may
% have to be run twice to clear warning/error messages.


% *** CITATION PACKAGES ***
%
\ifCLASSOPTIONcompsoc
  % IEEE Computer Society needs nocompress option
  % requires cite.sty v4.0 or later (November 2003)
  \usepackage[nocompress]{cite}
\else
  % normal IEEE
  \usepackage{cite}
\fi
% cite.sty was written by Donald Arseneau
% V1.6 and later of IEEEtran pre-defines the format of the cite.sty package
% \cite{} output to follow that of the IEEE. Loading the cite package will
% result in citation numbers being automatically sorted and properly
% "compressed/ranged". e.g., [1], [9], [2], [7], [5], [6] without using
% cite.sty will become [1], [2], [5]--[7], [9] using cite.sty. cite.sty's
% \cite will automatically add leading space, if needed. Use cite.sty's
% noadjust option (cite.sty V3.8 and later) if you want to turn this off
% such as if a citation ever needs to be enclosed in parenthesis.
% cite.sty is already installed on most LaTeX systems. Be sure and use
% version 5.0 (2009-03-20) and later if using hyperref.sty.
% The latest version can be obtained at:
% http://www.ctan.org/pkg/cite
% The documentation is contained in the cite.sty file itself.
%
% Note that some packages require special options to format as the Computer
% Society requires. In particular, Computer Society  papers do not use
% compressed citation ranges as is done in typical IEEE papers
% (e.g., [1]-[4]). Instead, they list every citation separately in order
% (e.g., [1], [2], [3], [4]). To get the latter we need to load the cite
% package with the nocompress option which is supported by cite.sty v4.0
% and later.

% *** GRAPHICS RELATED PACKAGES ***
%
\ifCLASSINFOpdf
  % \usepackage[pdftex]{graphicx}
  % declare the path(s) where your graphic files are
  % \graphicspath{{../pdf/}{../jpeg/}}
  % and their extensions so you won't have to specify these with
  % every instance of \includegraphics
  % \DeclareGraphicsExtensions{.pdf,.jpeg,.png}
\else
  % or other class option (dvipsone, dvipdf, if not using dvips). graphicx
  % will default to the driver specified in the system graphics.cfg if no
  % driver is specified.
  % \usepackage[dvips]{graphicx}
  % declare the path(s) where your graphic files are
  % \graphicspath{{../eps/}}
  % and their extensions so you won't have to specify these with
  % every instance of \includegraphics
  % \DeclareGraphicsExtensions{.eps}
\fi
% graphicx was written by David Carlisle and Sebastian Rahtz. It is
% required if you want graphics, photos, etc. graphicx.sty is already
% installed on most LaTeX systems. The latest version and documentation
% can be obtained at: 
% http://www.ctan.org/pkg/graphicx
% Another good source of documentation is "Using Imported Graphics in
% LaTeX2e" by Keith Reckdahl which can be found at:
% http://www.ctan.org/pkg/epslatex
%
% latex, and pdflatex in dvi mode, support graphics in encapsulated
% postscript (.eps) format. pdflatex in pdf mode supports graphics
% in .pdf, .jpeg, .png and .mps (metapost) formats. Users should ensure
% that all non-photo figures use a vector format (.eps, .pdf, .mps) and
% not a bitmapped formats (.jpeg, .png). The IEEE frowns on bitmapped formats
% which can result in "jaggedy"/blurry rendering of lines and letters as
% well as large increases in file sizes.
%
% You can find documentation about the pdfTeX application at:
% http://www.tug.org/applications/pdftex





% *** MATH PACKAGES ***
%
%\usepackage{amsmath}
% A popular package from the American Mathematical Society that provides
% many useful and powerful commands for dealing with mathematics.
%
% Note that the amsmath package sets \interdisplaylinepenalty to 10000
% thus preventing page breaks from occurring within multiline equations. Use:
%\interdisplaylinepenalty=2500
% after loading amsmath to restore such page breaks as IEEEtran.cls normally
% does. amsmath.sty is already installed on most LaTeX systems. The latest
% version and documentation can be obtained at:
% http://www.ctan.org/pkg/amsmath





% *** SPECIALIZED LIST PACKAGES ***
%
%\usepackage{algorithmic}
% algorithmic.sty was written by Peter Williams and Rogerio Brito.
% This package provides an algorithmic environment fo describing algorithms.
% You can use the algorithmic environment in-text or within a figure
% environment to provide for a floating algorithm. Do NOT use the algorithm
% floating environment provided by algorithm.sty (by the same authors) or
% algorithm2e.sty (by Christophe Fiorio) as the IEEE does not use dedicated
% algorithm float types and packages that provide these will not provide
% correct IEEE style captions. The latest version and documentation of
% algorithmic.sty can be obtained at:
% http://www.ctan.org/pkg/algorithms
% Also of interest may be the (relatively newer and more customizable)
% algorithmicx.sty package by Szasz Janos:
% http://www.ctan.org/pkg/algorithmicx




% *** ALIGNMENT PACKAGES ***
%
%\usepackage{array}
% Frank Mittelbach's and David Carlisle's array.sty patches and improves
% the standard LaTeX2e array and tabular environments to provide better
% appearance and additional user controls. As the default LaTeX2e table
% generation code is lacking to the point of almost being broken with
% respect to the quality of the end results, all users are strongly
% advised to use an enhanced (at the very least that provided by array.sty)
% set of table tools. array.sty is already installed on most systems. The
% latest version and documentation can be obtained at:
% http://www.ctan.org/pkg/array


% IEEEtran contains the IEEEeqnarray family of commands that can be used to
% generate multiline equations as well as matrices, tables, etc., of high
% quality.




% *** SUBFIGURE PACKAGES ***
%\ifCLASSOPTIONcompsoc
%  \usepackage[caption=false,font=footnotesize,labelfont=sf,textfont=sf]{subfig}
%\else
%  \usepackage[caption=false,font=footnotesize]{subfig}
%\fi
% subfig.sty, written by Steven Douglas Cochran, is the modern replacement
% for subfigure.sty, the latter of which is no longer maintained and is
% incompatible with some LaTeX packages including fixltx2e. However,
% subfig.sty requires and automatically loads Axel Sommerfeldt's caption.sty
% which will override IEEEtran.cls' handling of captions and this will result
% in non-IEEE style figure/table captions. To prevent this problem, be sure
% and invoke subfig.sty's "caption=false" package option (available since
% subfig.sty version 1.3, 2005/06/28) as this is will preserve IEEEtran.cls
% handling of captions.
% Note that the Computer Society format requires a sans serif font rather
% than the serif font used in traditional IEEE formatting and thus the need
% to invoke different subfig.sty package options depending on whether
% compsoc mode has been enabled.
%
% The latest version and documentation of subfig.sty can be obtained at:
% http://www.ctan.org/pkg/subfig




% *** FLOAT PACKAGES ***
%
%\usepackage{fixltx2e}
% fixltx2e, the successor to the earlier fix2col.sty, was written by
% Frank Mittelbach and David Carlisle. This package corrects a few problems
% in the LaTeX2e kernel, the most notable of which is that in current
% LaTeX2e releases, the ordering of single and double column floats is not
% guaranteed to be preserved. Thus, an unpatched LaTeX2e can allow a
% single column figure to be placed prior to an earlier double column
% figure.
% Be aware that LaTeX2e kernels dated 2015 and later have fixltx2e.sty's
% corrections already built into the system in which case a warning will
% be issued if an attempt is made to load fixltx2e.sty as it is no longer
% needed.
% The latest version and documentation can be found at:
% http://www.ctan.org/pkg/fixltx2e


%\usepackage{stfloats}
% stfloats.sty was written by Sigitas Tolusis. This package gives LaTeX2e
% the ability to do double column floats at the bottom of the page as well
% as the top. (e.g., "\begin{figure*}[!b]" is not normally possible in
% LaTeX2e). It also provides a command:
%\fnbelowfloat
% to enable the placement of footnotes below bottom floats (the standard
% LaTeX2e kernel puts them above bottom floats). This is an invasive package
% which rewrites many portions of the LaTeX2e float routines. It may not work
% with other packages that modify the LaTeX2e float routines. The latest
% version and documentation can be obtained at:
% http://www.ctan.org/pkg/stfloats
% Do not use the stfloats baselinefloat ability as the IEEE does not allow
% \baselineskip to stretch. Authors submitting work to the IEEE should note
% that the IEEE rarely uses double column equations and that authors should try
% to avoid such use. Do not be tempted to use the cuted.sty or midfloat.sty
% packages (also by Sigitas Tolusis) as the IEEE does not format its papers in
% such ways.
% Do not attempt to use stfloats with fixltx2e as they are incompatible.
% Instead, use Morten Hogholm'a dblfloatfix which combines the features
% of both fixltx2e and stfloats:
%
% \usepackage{dblfloatfix}
% The latest version can be found at:
% http://www.ctan.org/pkg/dblfloatfix




% *** PDF, URL AND HYPERLINK PACKAGES ***
%
%\usepackage{url}
% url.sty was written by Donald Arseneau. It provides better support for
% handling and breaking URLs. url.sty is already installed on most LaTeX
% systems. The latest version and documentation can be obtained at:
% http://www.ctan.org/pkg/url
% Basically, \url{my_url_here}.




% *** Do not adjust lengths that control margins, column widths, etc. ***
% *** Do not use packages that alter fonts (such as pslatex).         ***
% There should be no need to do such things with IEEEtran.cls V1.6 and later.
% (Unless specifically asked to do so by the journal or conference you plan
% to submit to, of course. )


% correct bad hyphenation here
\hyphenation{op-tical net-works semi-conduc-tor}

% \usepackage[utf8x]{inputenc}
% \usepackage[T1]{fontenc}
% \usepackage{graphicx}
% \usepackage{grffile}
% \usepackage{longtable}
% \usepackage{wrapfig}
% \usepackage{rotating}
% \usepackage[normalem]{ulem}
% \usepackage{amsmath}
% \usepackage{textcomp}
% \usepackage{amssymb}
% \usepackage{capt-of}
% \usepackage{hyperref}
% \usepackage{bbm}
% \usepackage[greek, english]{babel}
% \usepackage{latex/agda}
\DeclareUnicodeCharacter{7522}{\ensuremath { _i}}
\DeclareUnicodeCharacter{8337}{\ensuremath { _e}}
\DeclareUnicodeCharacter{8346}{\ensuremath { _p}}
\DeclareUnicodeCharacter{7523}{\ensuremath { _r}}
\DeclareUnicodeCharacter{8321}{\ensuremath { _1}}
\DeclareUnicodeCharacter{8322}{\ensuremath { _2}}
\DeclareUnicodeCharacter{955}{\ensuremath{\lambda}}
\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{737}{\ensuremath { ^l}}
\DeclareUnicodeCharacter{8799}{\ensuremath { \overset{?}{=}}}
\DeclareUnicodeCharacter{8252}{\ensuremath { !!}}
\DeclareUnicodeCharacter{8779}{\ensuremath { \cong}}


\begin{document}

\title{ARMOR: A Verified Implementation of X.509 Certificate Chain Validation}
% author names and affiliations
% use a multiple column layout for up to three different
% affiliations
% \author{\IEEEauthorblockN{Michael Shell}
%   \IEEEauthorblockA{School of Electrical and\\Computer Engineering\\
%     Georgia Institute of Technology\\
%     Atlanta, Georgia 30332--0250\\
%     Email: http://www.michaelshell.org/contact.html}
%   \and
%   \IEEEauthorblockN{Homer Simpson}
%   \IEEEauthorblockA{Twentieth Century Fox\\
%     Springfield, USA\\
%     Email: homer@@thesimpsons.com}
%   \and
%   \IEEEauthorblockN{James Kirk\\ and Montgomery Scott}
%   \IEEEauthorblockA{Starfleet Academy\\
%     San Francisco, California 96678-2391\\
%     Telephone: (800) 555--1212\\
%     Fax: (888) 555--1212}}

% conference papers do not typically use \thanks and this command
% is locked out in conference mode. If really needed, such as for
% the acknowledgment of grants, issue a \IEEEoverridecommandlockouts
% after \documentclass

% for over three affiliations, or if they all won't fit within the width
% of the page (and note that there is less available width in this regard for
% compsoc conferences compared to traditional conferences), use this
% alternative format:
% 
%\author{\IEEEauthorblockN{Michael Shell\IEEEauthorrefmark{1},
%Homer Simpson\IEEEauthorrefmark{2},
%James Kirk\IEEEauthorrefmark{3}, 
%Montgomery Scott\IEEEauthorrefmark{3} and
%Eldon Tyrell\IEEEauthorrefmark{4}}
%\IEEEauthorblockA{\IEEEauthorrefmark{1}School of Electrical and Computer Engineering\\
%Georgia Institute of Technology,
%Atlanta, Georgia 30332--0250\\ Email: see http://www.michaelshell.org/contact.html}
%\IEEEauthorblockA{\IEEEauthorrefmark{2}Twentieth Century Fox, Springfield, USA\\
%Email: homer@@thesimpsons.com}
%\IEEEauthorblockA{\IEEEauthorrefmark{3}Starfleet Academy, San Francisco, California 96678-2391\\
%Telephone: (800) 555--1212, Fax: (888) 555--1212}
%\IEEEauthorblockA{\IEEEauthorrefmark{4}Tyrell Inc., 123 Replicant Street, Los Angeles, California 90210--4321}}

% use for special paper notices
% \IEEEspecialpapernotice{(Invited Paper)}

\maketitle

% As a general rule, do not put math, special symbols or citations
% in the abstract


% no keywords

% For peer review papers, you can put extra information on the cover
% page as needed:
% \ifCLASSOPTIONpeerreview
% \begin{center} \bfseries EDICS Category: 3-BBND \end{center}
% \fi
% 
% For peerreview papers, this IEEEtran command inserts a page break and
% creates the second title. It will be ignored for other modes.
\IEEEpeerreviewmaketitle


%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%
%
% Body
%
%include src/abstract.lhs
\lhsinclude{abstract}
%include src/introduction.lhs
\lhsinclude{introduction} 
%include src/background.lhs
\lhsinclude{background}
%include src/architecture.lhs
\lhsinclude{architecture}
%include src/verification.lhs
\lhsinclude{verification}
%include src/evaluation.lhs
\lhsinclude{evaluation}
%include src/discussion.lhs
\lhsinclude{discussion}
%include src/related-work.lhs
\lhsinclude{related-work}
%include src/conclusion.lhs
\lhsinclude{conclusion}

%
%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{IEEEtran}
\bibliography{references}

%include src/appendix.lhs
\lhsinclude{appendix}

\end{document}
