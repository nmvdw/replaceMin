%options ghci

\documentclass{amsart}

%include polycode.fmt

\title{Eliminating Traversels in Agda}

\usepackage{agda}

% The following packages are needed because unicode
% is translated (using the next set of packages) to
% latex commands. You may need more packages if you
% use more unicode characters:

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}

% This handles the translation of unicode to latex:

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{autofe}

% Some characters that are not automatically defined
% (you figure out by the latex compilation errors you get),
% and you need to define:

\DeclareUnicodeCharacter{931}{$\Sigma$}
\DeclareUnicodeCharacter{948}{$\delta$}
\DeclareUnicodeCharacter{957}{$\nu$}
\DeclareUnicodeCharacter{8718}{$\blacksquare$}
\DeclareUnicodeCharacter{8759}{::}
\DeclareUnicodeCharacter{9659}{$\vartriangleright$}

% Add more as you need them (shouldn't happen often).

\newcommand{\AD}[1]{\AgdaDatatype{#1}}
\newcommand{\AIC}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\AF}[1]{\AgdaFunction{#1}}
\newcommand{\AFi}[1]{\AgdaField{#1}}
\newcommand{\AB}[1]{\AgdaBound{#1}}
\newcommand{\AgdaUnderscore}{$\_$}

\newcommand{\remove}[1]{}
\usepackage{tikz}
\usetikzlibrary{trees}

\begin{document}
\maketitle

\section{Introduction}
\input{Introduction}

\section{The Haskell Implementation}
Bird's original solution is the following Haskell program \cite{bird1984}.

\begin{code}
data Tree = Leaf Int | Node Tree Tree

replaceMin :: Tree -> Tree
replaceMin t = let (r, m) = rmb (t, m) in r 
  where
    rmb :: (Tree, Int) -> (Tree, Int)
    rmb (Leaf x, y) = (Leaf y, x)
    rmb (Node l r, y) =
      let (l',ml) = rmb (l, y)
          (r',mr) = rmb (r, y)
      in (Node l' r', min ml mr)
\end{code}

A peculiar feature of this program, is the call of |rmb|.
Rather than defining |m| via structural recursion, it is defined via the fixed point of |rmb t|.
As a consequence, systems such as Coq and Agda cannot automatically guarantee this function actually terminates \cite{barras1997,norell2008y}.
Beside that, showing correctness becomes more difficult since we cannot use just structural induction anymore.

Due to this, the termination of this program crucially depends on lazy evaluation.
If |rmb t m| would be calculated eagerly, then before unfolding |rmb|, the value |m| has to be known.
However, this requires |rmb t m| to be computed already and hence, it does not terminate.

All in all, to make this all work in a total programming language, we need a mechanism to allow general recursion, which produces productive functions.
In addition, since the termination of general recursive functions requires lazy evaluation, we also need a way to annotate that an argument of a function is evaluated lazily.
This is the exact opposite from Haskell where by default arguments are evaluated lazily and strictness is annotated.

\section{Sized Types}
\input{SizedCombinators/SizedTypes}

\section{Eliminating Traversals}
\input{ReplaceMin/replaceMin}

\section{Proving with Sized Types}
\input{SizedCombinators/SizedPredicates}

\section{Functional Correctness}
\input{ReplaceMin/correctness}

\bibliographystyle{plain}
\bibliography{literature}
\end{document}