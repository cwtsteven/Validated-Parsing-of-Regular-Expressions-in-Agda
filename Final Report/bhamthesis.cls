% Thesis class definition. Modified by Benjamin Nickolls
% (msc47bgn@bham.ac.uk) for Birmingham Univesity's guidelines from:

% University of Birmingham Thesis LaTex2e Class definition.
% Written by Benjamin Nickolls 2007, based on
% the thesis.sty written at UofT by fpitt.
% (bernecky@acm.org)

\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{bhamthesis}[1997/07/15 University of Birmingham Thesis class
definition] 
\RequirePackage{setspace,graphicx}
 
% This is the first LaTeX class definition I have written, so if something
% looks wrong, it probably IS wrong. 

% The following options are what you get if you do not specify ANY options.
% E.g., \documentclass{utthesis}
% Basically, it is your camera copy.
\ExecuteOptions{a4paper,oneside,12pt,onecolumn,final,openany}

% If you want a cheap-and-cheerful draft copy, try options such
%% \documentclass[draft,twoside,11pt]{utthesis} 

% Set up handling of "draft" option. 
\DeclareOption{draft}{%
 \PassOptionsToPackage{all}{draftcopy}% 
 \PassOptionsToClass{draft}{report}% 
 \AtEndOfClass{%
   \RequirePackage{draftcopy}%
   % I wanted to print timestamp of each file, but I don't see
   % how to do that...
   \draftcopyName{DRAFT: \today}{60 } % text for overprinting if in "draft" mode
   }%
}

% Pass ALL options to report.cls.
\DeclareOption*{%
 \PassOptionsToClass{\CurrentOption}{report}
}

\ProcessOptions


% \LoadClass{report} changed by Steven
\LoadClass{article} 
% Set up environments for thesis sections.

% clearemptydoublepage from page 92 of The LaTeX Companion 1993. 
% \newcommand{\clearemptydoublepage}{\newpage{\pagestyle{empty}\cleardoublepage}} commented out by Steven


\renewenvironment{abstract}%
%{\clearemptydoublepage changed by Steven
{\newpage
\thispagestyle{plain}
\begin{center}
  \section*{Abstract}
    \textbf{\@title}\\
\@author
 \end{center}
 \hrule
\vspace{4mm} % {3mm} changed by Steven
 \begingroup
}{\newpage\endgroup}

\newenvironment{acknowledgments}%
%{\clearemptydoublepage
{\newpage
\thispagestyle{plain}
 \begin{center}
  \section*{Acknowledgments}
 \end{center}
 \hrule
 \vspace{4mm} % {2mm}
 \begingroup
}{\newpage\endgroup}

\newenvironment{dedication}%
{\clearemptydoublepage 
\thispagestyle{plain}
 \begin{center}
  \section*{Dedication}
 \end{center}
 \hrule
 \vspace{2mm}
 \begingroup
}{
\newpage\endgroup}

\newenvironment{repository}%
%{\clearemptydoublepage
{\newpage
\thispagestyle{plain}
 %\begin{center}
  \section*{}
 %\end{center}
 %\hrule
 \vspace{2mm}
 \begingroup
 
}{\newpage\endgroup}
\newcommand{\declaration}[1]%
{
\clearemptydoublepage 
\thispagestyle{plain}
\begin{center}
\section*{Declaration}
\end{center}
The material contained within this thesis has not previously been
submitted for a degree at the University of Birmingham or any other university.
The research reported within this thesis has been conducted by the author
unless indicated otherwise.\\


Signed .......................................................................................................................
\vfill
}
\newenvironment{preliminary}%
{\pagestyle{plain}\pagenumbering{roman}}%
{\pagenumbering{arabic}}

% Default values for title page.

%% To produce output with the desired line spacing, the argument of
%% \spacing should be multiplied by 5/6 = 0.8333, so that 1 1/2 spaced
%% corresponds to \spacing{1.5} and double spaced is \spacing{1.66}.
\def\normalspacing{1.25} % default line spacing

\newcommand{\department}[1]{\ifx\empty#1\else\gdef\@department{#1}\fi}
\newcommand{\degree}[1]{\ifx\empty#1\else\gdef\@degree{#1}\fi}
\renewcommand{\author}[1]{\ifx\empty#1\else\gdef\@author{#1}\fi}
\newcommand{\studentid}[1]{\ifx\empty#1\else\gdef\@studentid{#1}\fi}
\newcommand{\supervisor}[1]{\ifx\empty#1\else\gdef\@supervisor{#1}\fi}
\renewcommand{\title}[1]{\ifx\empty#1\else\gdef\@title{#1}\fi}
\newcommand{\gyear}[1]{\ifx\empty#1\else\gdef\@gyear{#1}\fi}

\global\def\@department{\mbox{}}
\global\def\@degree{\mbox{}}
\global\def\@author{\mbox{}}
\global\def\@studentid{\mbox{}}
\global\def\@supervisor{\mbox{}}
\global\def\@title{\mbox{}}
\global\def\@gyear{\number\year} % Default year is current year


%% Change \maketitle to follow the SGS guidelines.
\renewcommand{\maketitle}
{\begin{titlepage}
   %% Set the line spacing to 1 for the title page.
   \begin{spacing}{1} 
   \begin{large}
   \begin{center}
      \mbox{}
      \vfill
      \begin{sc}
      {\@title}\\
      \end{sc}
      \vfill
      {\@author}\\
      Student ID: {\@studentid}\\
      Supervisor: {\@supervisor}\\
      \vspace*{4mm}
      \includegraphics[width=30mm,height=30mm]{images/crest.png}\\
      Submitted in conformity with the requirements\\
      for the degree of {\@degree}\\
      School of {\@department}\\
      University of Birmingham\\
      \vfill
      Copyright {\copyright} {\@gyear} School of {\@department}, University of Birmingham\\
      \vspace*{.2in}
   \end{center}
   \end{large}
   \end{spacing}
   \end{titlepage}
}%\maketitle


%% Footnotes are always single-spaced.
%%\let\@@footnotetext=\@footnotetext
%%\def\@footnotetext{\begin{spacing}{1}\@@footnotetext\end{spacing}}

%% Define the "thesis" page style.
\if@twoside % If two-sided printing.
\def\ps@thesis{\let\@mkboth\markboth
   \def\@oddfoot{}
   \let\@evenfoot\@oddfoot
   \def\@oddhead{
      {\sc\rightmark} \hfil \rm\thepage
      }
   \def\@evenhead{
      \rm\thepage \hfil {\sc\leftmark}
      }
   \def\chaptermark##1{\markboth{\ifnum \c@secnumdepth >\m@ne
      \@chapapp\ \thechapter. \ \fi ##1}{}}
   \def\sectionmark##1{\markright{\ifnum \c@secnumdepth >\z@
      \thesection. \ \fi ##1}}}
\else % If one-sided printing.
\def\ps@thesis{\let\@mkboth\markboth
   \def\@oddfoot{}
   \def\@oddhead{
      {\sc\rightmark} \hfil \rm\thepage
      }
   \def\chaptermark##1{\markright{\ifnum \c@secnumdepth >\m@ne
      \@chapapp\ \thechapter. \ \fi ##1}}}
\fi

\pagestyle{thesis}
% Set up page layout.
%\setlength{\textheight}{21cm} % Height of the main body of the text
%\setlength{\topmargin}{0cm} % 1'' margin on top of page
%\setlength{\headsep}{1.5cm}  % space between header and top of body
%\addtolength{\headsep}{-\headheight} % See The LaTeX Companion, p 85
%\setlength{\footskip}{1cm}  % space between footer and bottom of body
%\setlength{\textwidth}{14cm} % width of the body of the text
%\setlength{\oddsidemargin}{2cm} % 2cm margin on the left for odd pages
%\setlength{\evensidemargin}{-1cm} % 2cm margin on the right for even pages

% 1.5 line spacing (ick!)
\linespread{1.25}

% Marginal notes
\setlength{\marginparwidth}{.75in} % width of marginal notes
\setlength{\marginparsep}{.125in} % space between marginal notes and text

% Make each page fill up the entire page. comment this out if you
% prefer. 
\flushbottom

\setcounter{tocdepth}{2} % Number the subsubsections 
