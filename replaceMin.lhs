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

\newcommand{\remove}[1]{}
\usepackage{tikz}
\usetikzlibrary{trees}

\begin{document}
\maketitle

\section{Introduction}
Let us consider the following problem:

\quad \emph{Given a binary tree $t$ with integer values in the leaves.}

\quad \emph{Replace every value in $t$ by the minimum.}
\end{displaycode}

The most obvious way to solve this, would be by first traversing the tree to calculate the minimum and then traversing the tree to replace all values by that.
Note that it is simple to prove the termination and we go twice through the tree.

However, there is a more efficient solution to this problem \cite{bird1984}.
By using a \emph{cyclic} program, he described a program for which only one traversal is needed.
Normally, one defines functions on algebraic data types by using structural recursion and then proof assistants, such as Coq and Agda \cite{barras1997,norell2008y}, can automatically check the termination.
Cyclic programs, on the other hand, are \emph{not} structurally recursive and they do \emph{not} necessarily terminate.
One can show this particular one terminates using clocked type theory \cite{atkey2013}, but this has not been implemented in a proof assistant yet.
Hence, this solution is more efficient, but the price we pay, is that proving termination becomes more difficult.

In addition, showing correctness requires different techniques.
For structurally recursive functions, one can use structural induction.
For cyclic programs, that technique is not available and thus broader techniques are needed.

This pearl describes an Agda implementation of this program together with a proof that it is terminating and a correctness proof \cite{norell2008y}.
Our solution is based on the work by Atkey and McBride \cite{atkey2013} and the approach shows similarities to clocked type theory \cite{bahr2017clocks}.
We start by giving an Haskell implementation to demonstrate the issues we have to tackle.
After that we discuss the main tool for checking termination in Agda, namely \emph{sized types}.
Types are assigned sizes and if those decrease in recursive calls, then the program is productive.
We then give the solution, which is terminating since Agda accepts it.
Lastly, we demonstrate how to do proofs with sized types and we finish by proving correctness via equational reasoning. 

\section{The Haskell Implementation}
Bird's original solution is the following Haskell program \cite{bird1984}.

\begin{code}
data Tree = Leaf Int | Node Tree Tree

replaceMin :: Tree -> Tree
replaceMin t = let (r, m) = rmb t m in r 
  where
    rmb :: Tree -> Int -> (Tree, Int)
    rmb (Leaf x) y = (Leaf y, x)
    rmb (Node l r) y =
      let (l',ml) = rmb l y
          (r',mr) = rmb r y
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

\input{replaceMin}

\bibliographystyle{plain}
\bibliography{literature}
\end{document}