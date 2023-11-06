%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% Haskell Styling
%%
%% TODO: Figure out spacing!
\usepackage{xcolor}

%% Colors (from duo-tone light syntax)
\definecolor{hsgold2}{RGB/cmyk}{177,149,90/0,0.16,0.49,0.3}
\definecolor{hsgold3}{RGB/cmyk}{190,106,13/0,0.44,0.93,0.25}
\definecolor{hsblue3}{RGB/cmyk}{0,33,132/1,0.65,0,0.35}
\definecolor{hsblue4}{RGB/cmyk}{97,108,132/0.26,0.18,0,0.48}
\definecolor{hsblue5}{RGB/cmyk}{34,50,68/0.5,0.26,0,0.73}
\definecolor{hsred2}{RGB/cmyk}{191,121,103/0,0.4,0.49,0.23}
\definecolor{hsred3}{RGB/cmyk}{171,72,46/0,0.58,0.73,0.33}

% TODO: make all color names upercase so it
%       all wors in headings too!
\colorlet{HSBLUE3}{hsblue3}

%% LaTeX Kerning nastiness. By using curly braces to delimit color group,
%% it breaks spacing. The following seems to work:
%%
%% https://tex.stackexchange.com/questions/85033/colored-symbols/85035#85035
%%
% \renewcommand*{\mathcolor}{}
\def\mathcolor#1#{\mathcoloraux{#1}}
\newcommand*{\mathcoloraux}[3]{%
  \protect\leavevmode
  \begingroup
    \color#1{#2}#3%
  \endgroup
}


\newcommand{\HSKeyword}[1]{\mathcolor{hsgold3}{\textbf{#1}}}
\newcommand{\HSNumeral}[1]{\mathcolor{hsred3}{#1}}
\newcommand{\HSChar}[1]{\mathcolor{hsred2}{#1}}
\newcommand{\HSString}[1]{\mathcolor{hsred2}{\textit{#1}}}
\newcommand{\HSSpecial}[1]{\mathcolor{hsblue4}{#1}}
\newcommand{\HSSym}[1]{\mathcolor{hsblue4}{\textit{\ensuremath{#1}}}}
\newcommand{\HSCon}[1]{\mathcolor{hsblue3}{\mathit{\ensuremath{#1}}}}
\newcommand{\HSVar}[1]{\mathcolor{hsblue5}{\mathit{\ensuremath{#1}}}}
\newcommand{\HSVarNI}[1]{\mathcolor{hsblue5}{\ensuremath{#1}}}
\newcommand{\HSConNI}[1]{\mathcolor{hsblue3}{\ensuremath{#1}}}
\newcommand{\HSComment}[1]{\mathcolor{hsgold2}{\textit{#1}}}

% Easy to typeset Haskell types using the \HSCon
% command from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

% We need to use the \HVNI version to make sure we shall not
% put \mathit around whatver we give to \HV. In case of single
% greek characters, we don't have the font for it.
\newcommand{\HVNI}[1]{\ifdefined\HSVarNI\HSVarNI{#1}\else#1\fi}
\newcommand{\HTNI}[1]{\ifdefined\HSConNI\HSConNI{#1}\else#1\fi}

% Finally, HSCustom can use any other color for whatever purpose we choose.
\newcommand{\HSCustom}[2]{\mathcolor{#1}{\ensuremath{#2}}}
% HSCustomNC disables nested calls to mathcolor
\newcommand{\mathnocolor}[2]{#2}
\newcommand{\HSCustomNC}[2]{%
\mathcolor{#1}{\let\mathcolor\mathnocolor%
\ensuremath{#2}}}

%subst keyword a = "\HSKeyword{" a "}"
%subst conid a   = "\HSCon{" a "}"
%subst varid a   = "\HSVar{" a "}"
%subst varsym a  = "\HSSym{" a "}"
%subst consym a  = "\HSSym{" a "}"
%subst numeral a = "\HSNumeral{" a "}"
%subst char a    = "\HSChar{''" a "''}"
%subst string a  = "\HSString{``" a "\char34 }"
%subst special a = "\HSSpecial{" a "}"
%subst comment a = "\HSComment{ -\! -" a "}"

%format family     = "\HSKeyword{family}"
%format record     = "\HSKeyword{record}"
%format constructor = "\HSKeyword{constructor}"
%format field      = "\HSKeyword{field}"
%format pattern    = "\HSKeyword{pattern}"
%format with       = "\HSKeyword{with}"
%format forall     = "\HSSym{\forall}"

%%% A Handy placeholder symbol to have
%format SQ         = "\HSVar{\square}"


%format (P (a)) = "\HSSym{''}" a
%format Pcons   = "\mathrel{\HSSym{''\!\!:}}"

%%% lhs2TeX parser does not recognize '*'
%%% in kind annotations, it thinks it is a multiplication.
%format Star       = "\HSCon{*}"

%format Top        = "\HSSym{\top}"
%format Bot        = "\HSSym{\bot}"
%format ::         = "\mathrel{\HSSym{::}}"
%format !!         = "\mathrel{\HSSym{!!}}"
%format ->         = "\mathrel{\HSSym{\to}} "
%format =>         = "\mathrel{\HSSym{\Rightarrow}} "
%format =          = "\mathrel{\HSSym{=}}"
%format ~          = "\mathrel{\HSSym{\sim}} "
%format ==         = "\mathrel{\HSSym{\equiv}} "
%format /=         = "\mathrel{\HSSym{\not\equiv}} "
%format =?         = "\stackrel{?}{=} "
%format <=         = "\mathrel{\HSSym{\leq}} "
%format >=         = "\mathrel{\HSSym{\geq}} "

%format :          = "\mathbin{\HSCon{:}}"
%format ++-        = "\mathbin{\HSSym{++-}}"
%format ++         = "\mathbin{\HSSym{++}}"
%format +          = "\mathbin{\HSSym{+}}"
%format -          = "\mathbin{\HSSym{-}}"
%format *          = "\mathbin{\HSSym{*}}"
%format ,          = "\mathbin{\HSSym{,}}"
%format nil        = "\HSCon{[]}"

%format _          = "\mathbin{\HSSym{\anonymous}} "
%format <-         = "\mathbin{\HSSym{\leftarrow}} "
%format \          = "\mathbin{\HSSym{\lambda}} "
%format |          = "\mathbin{\HSSym{\mid}} "
%format {          = "\HSSym{\{\mskip1.5mu} "
%format }          = "\HSSym{\mskip1.5mu\}}"
%format [          = "\HSSym{[\mskip1.5mu} "
%format ]          = "\HSSym{\mskip1.5mu]}"
%format ..         = "\HSSym{\mathinner{\ldotp\ldotp}}"
%format @          = "\mathord{\HSSym{@}}"
%format .          = "\mathbin{\HSSym{\circ}}"
%format !!         = "\mathbin{\HSSym{!!}}"
%format ^          = "\mathbin{\HSSym{\uparrow}}"
%format ^^         = "\mathbin{\HSSym{\uparrow\uparrow}}"
%format **         = "\mathbin{\HSSym{**}}"
%format /          = "\mathbin{\HSSym{/}}"
%format `quot`     = "\mathbin{\HSSym{`quot`}}"
%format `rem`      = "\mathbin{\HSSym{`rem`}}"
%format `div`      = "\mathbin{\HSSym{`div`}}"
%format `mod`      = "\mathbin{\HSSym{`mod`}}"
%format :%         = "\mathbin{\HSSym{:\%}}"
%format %          = "\mathbin{\HSSym{\%}}"
%format `elem`     = "\mathbin{\HSSym{\in}} "
%format `notElem`  = "\mathbin{\HSSym{\notin}} "
%format &&         = "\mathbin{\HSSym{\mathrel{\wedge}}}"
%format ||         = "\mathbin{\HSSym{\mathrel{\vee}}}"
%format >>         = "\mathbin{\HSSym{\sequ}} "
%format >>=        = "\mathbin{\HSSym{\bind}} "
%format =<<        = "\mathbin{\HSSym{\rbind}} "
%format $          = "\mathbin{\HSSym{\$}}"
%format `seq`      = "\mathbin{\HSSym{`seq`}}"
%format !          = "\mathbin{\HSSym{!}}"
%format //         = "\mathbin{\HSSym{//}}"
%format bot  = "\HSSym{\bot} "
%format not	   = "\HSSym{\neg} "
%format >>>        = "\mathbin{\HSSym{\ggg}}"
%format >=>        = "\mathbin{\HSSym{> \! = \! >}}"
%format dots       = "\mathbin{\HSSym{\dots}}"
%format dot        = "\mathrel{\HSSym{.}}"
%format :>:        = "\mathbin{\HSCon{\triangleright}}"
%format :*:        = "\mathbin{\HSCon{:\!\!*\!\!:}}"
%format :**:       = "\mathbin{\HSCon{:\!\!*\!\!:}}"
%format :~:        = "\mathbin{\HSCon{:\!\sim\!:}}"
%format :@:        = "\mathbin{\HSCon{:\!\!@\!\!:}}"
%format <$$>       = "\mathbin{\HSSym{<\!\!\$\!\!>}}"
%format <$>        = "\mathbin{\HSSym{<\!\!\$\!\!>}}"
%format <|>        = "\mathbin{\HSSym{<\mid>}}"
%format $$         = "\mathbin{\HSSym{\$}}"
%format <*>        = "\mathbin{\HSSym{<\!\!*\!\!>}}"
%format  *>        = "\mathbin{\HSSym{*\!\!>}}"
%format <*         = "\mathbin{\HSSym{<\!\!*}}"
%format ?          = "\HSVar{?}\,"

%% Formatting single letters and subscripts by
%% default.

%format a0         = "\HSVar{\mathit{a}_{0}}"
%format a1         = "\HSVar{\mathit{a}_{1}}"
%format a2         = "\HSVar{\mathit{a}_{2}}"
%format a3         = "\HSVar{\mathit{a}_{3}}"
%format b0         = "\HSVar{\mathit{b}_{0}}"
%format b1         = "\HSVar{\mathit{b}_{1}}"
%format b2         = "\HSVar{\mathit{b}_{2}}"
%format b3         = "\HSVar{\mathit{b}_{3}}"
%format c0         = "\HSVar{\mathit{c}_{0}}"
%format c1         = "\HSVar{\mathit{c}_{1}}"
%format c2         = "\HSVar{\mathit{c}_{2}}"
%format c3         = "\HSVar{\mathit{c}_{3}}"
%format d0         = "\HSVar{\mathit{d}_{0}}"
%format d1         = "\HSVar{\mathit{d}_{1}}"
%format d2         = "\HSVar{\mathit{d}_{2}}"
%format d3         = "\HSVar{\mathit{d}_{3}}"
%format e0         = "\HSVar{\mathit{e}_{0}}"
%format e1         = "\HSVar{\mathit{e}_{1}}"
%format e2         = "\HSVar{\mathit{e}_{2}}"
%format e3         = "\HSVar{\mathit{e}_{3}}"
%format f0         = "\HSVar{\mathit{f}_{0}}"
%format f1         = "\HSVar{\mathit{f}_{1}}"
%format f2         = "\HSVar{\mathit{f}_{2}}"
%format f3         = "\HSVar{\mathit{f}_{3}}"
%format g0         = "\HSVar{\mathit{g}_{0}}"
%format g1         = "\HSVar{\mathit{g}_{1}}"
%format g2         = "\HSVar{\mathit{g}_{2}}"
%format g3         = "\HSVar{\mathit{g}_{3}}"
%format h0         = "\HSVar{\mathit{h}_{0}}"
%format h1         = "\HSVar{\mathit{h}_{1}}"
%format h2         = "\HSVar{\mathit{h}_{2}}"
%format h3         = "\HSVar{\mathit{h}_{3}}"
%format i0         = "\HSVar{\mathit{i}_{0}}"
%format i1         = "\HSVar{\mathit{i}_{1}}"
%format i2         = "\HSVar{\mathit{i}_{2}}"
%format i3         = "\HSVar{\mathit{i}_{3}}"
%format j0         = "\HSVar{\mathit{j}_{0}}"
%format j1         = "\HSVar{\mathit{j}_{1}}"
%format j2         = "\HSVar{\mathit{j}_{2}}"
%format j3         = "\HSVar{\mathit{j}_{3}}"
%format k0         = "\HSVar{\mathit{k}_{0}}"
%format k1         = "\HSVar{\mathit{k}_{1}}"
%format k2         = "\HSVar{\mathit{k}_{2}}"
%format k3         = "\HSVar{\mathit{k}_{3}}"
%format l0         = "\HSVar{\mathit{l}_{0}}"
%format l1         = "\HSVar{\mathit{l}_{1}}"
%format l2         = "\HSVar{\mathit{l}_{2}}"
%format l3         = "\HSVar{\mathit{l}_{3}}"
%format m0         = "\HSVar{\mathit{m}_{0}}"
%format m1         = "\HSVar{\mathit{m}_{1}}"
%format m2         = "\HSVar{\mathit{m}_{2}}"
%format m3         = "\HSVar{\mathit{m}_{3}}"
%format n0         = "\HSVar{\mathit{n}_{0}}"
%format n1         = "\HSVar{\mathit{n}_{1}}"
%format n2         = "\HSVar{\mathit{n}_{2}}"
%format n3         = "\HSVar{\mathit{n}_{3}}"
%format o0         = "\HSVar{\mathit{o}_{0}}"
%format o1         = "\HSVar{\mathit{o}_{1}}"
%format o2         = "\HSVar{\mathit{o}_{2}}"
%format o3         = "\HSVar{\mathit{o}_{3}}"
%format p0         = "\HSVar{\mathit{p}_{0}}"
%format p1         = "\HSVar{\mathit{p}_{1}}"
%format p2         = "\HSVar{\mathit{p}_{2}}"
%format p3         = "\HSVar{\mathit{p}_{3}}"
%format q0         = "\HSVar{\mathit{q}_{0}}"
%format q1         = "\HSVar{\mathit{q}_{1}}"
%format q2         = "\HSVar{\mathit{q}_{2}}"
%format q3         = "\HSVar{\mathit{q}_{3}}"
%format r0         = "\HSVar{\mathit{r}_{0}}"
%format r1         = "\HSVar{\mathit{r}_{1}}"
%format r2         = "\HSVar{\mathit{r}_{2}}"
%format r3         = "\HSVar{\mathit{r}_{3}}"
%format s0         = "\HSVar{\mathit{s}_{0}}"
%format s1         = "\HSVar{\mathit{s}_{1}}"
%format s2         = "\HSVar{\mathit{s}_{2}}"
%format s3         = "\HSVar{\mathit{s}_{3}}"
%format t0         = "\HSVar{\mathit{t}_{0}}"
%format t1         = "\HSVar{\mathit{t}_{1}}"
%format t2         = "\HSVar{\mathit{t}_{2}}"
%format t3         = "\HSVar{\mathit{t}_{3}}"
%format u0         = "\HSVar{\mathit{u}_{0}}"
%format u1         = "\HSVar{\mathit{u}_{1}}"
%format u2         = "\HSVar{\mathit{u}_{2}}"
%format u3         = "\HSVar{\mathit{u}_{3}}"
%format v0         = "\HSVar{\mathit{v}_{0}}"
%format v1         = "\HSVar{\mathit{v}_{1}}"
%format v2         = "\HSVar{\mathit{v}_{2}}"
%format v3         = "\HSVar{\mathit{v}_{3}}"
%format w0         = "\HSVar{\mathit{w}_{0}}"
%format w1         = "\HSVar{\mathit{w}_{1}}"
%format w2         = "\HSVar{\mathit{w}_{2}}"
%format w3         = "\HSVar{\mathit{w}_{3}}"
%format x0         = "\HSVar{\mathit{x}_{0}}"
%format x1         = "\HSVar{\mathit{x}_{1}}"
%format x2         = "\HSVar{\mathit{x}_{2}}"
%format x3         = "\HSVar{\mathit{x}_{3}}"
%format y0         = "\HSVar{\mathit{y}_{0}}"
%format y1         = "\HSVar{\mathit{y}_{1}}"
%format y2         = "\HSVar{\mathit{y}_{2}}"
%format y3         = "\HSVar{\mathit{y}_{3}}"
%format z0         = "\HSVar{\mathit{z}_{0}}"
%format z1         = "\HSVar{\mathit{z}_{1}}"
%format z2         = "\HSVar{\mathit{z}_{2}}"
%format z3         = "\HSVar{\mathit{z}_{3}}"

%format falser         = "\HSVar{\mathit{false}_{r}}"
%format truer         = "\HSVar{\mathit{true}_{r}}"
%format vr         = "\HSVar{\mathit{v}_{r}}"
%format fromN         = "\HSVar{\mathit{from}\mathbb{N}}"
%format IntZ       = "\HSSym{\mathbb{Z}}"

%format injectivel         = "\HSVar{\mathit{injective}^{l}}"
%format conicall         = "\HSVar{\mathit{conical}^{l}}"
%format cancell         = "\HSVar{\mathit{cancel==}^{l}}"

%format xs1         = "\HSVar{\mathit{xs}_{1}}"
%format xs2         = "\HSVar{\mathit{xs}_{2}}"
%format ys1         = "\HSVar{\mathit{ys}_{1}}"
%format ys2         = "\HSVar{\mathit{ys}_{2}}"
%format p1         = "\HSVar{\mathit{p}_{1}}"
%format p2         = "\HSVar{\mathit{p}_{2}}"
%format a1         = "\HSVar{\mathit{a}_{1}}"
%format a2         = "\HSVar{\mathit{a}_{2}}"
%format proj2         = "\HSVar{\mathit{proj}_{2}}"
%format bseq         = "\HSVar{\mathit{bs}_{eq}}"
%format valeq         = "\HSVar{\mathit{val}_{eq}}"
%format readeq         = "\HSVar{\mathit{read}_{eq}}"
%format pseq         = "\HSVar{\mathit{ps}_{eq}}"
%format eqrefl         = "\HSVar{\mathit{eq}_{refl}}"
