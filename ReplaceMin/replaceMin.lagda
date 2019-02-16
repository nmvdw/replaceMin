\AgdaHide{
\begin{code}
module ReplaceMin.replaceMin where

open import Preamble
open import SizedCombinators
\end{code}
}

We start by with the usual definition of binary trees.

\begin{code}
data Tree : Set where
  Leaf : ℕ → Tree
  Node : Tree → Tree → Tree
\end{code}

Next we define lazy versions of the constructors \AIC{Leaf} and \AIC{Node}.
To do so, we use that \AF{▻} is an applicative functor.

\begin{code}
▻Leaf : □(▻(c ℕ) ⇒ ▻ (c Tree))
▻Leaf n = pure Leaf ⊛ n

▻Node : □(▻(c Tree) ⇒ ▻(c Tree) ⇒ ▻(c Tree))
▻Node t₁ t₂ = pure Node ⊛ t₁ ⊛ t₂
\end{code}

The function \AD{rmb} takes a tree \AB{t} and lazily evaluated natural number \AB{n} and it returns a pair.
The first coordinate of that pair is a lazily evaluated tree, which is \AB{t} with each value replaced by \AB{n}.
The second coordinate is the minimum of \AB{t}.

\begin{code}
rmb : □(c Tree ⊗ ▻(c ℕ) ⇒ (▻(c Tree)) ⊗ c ℕ)
rmb (Leaf x , n) = (▻Leaf n , x)
rmb (Node l r , n) =
  let (l' , ml) = rmb (l , n)
      (r' , mr) = rmb (r , n)
  in (▻Node l' r' , ml ⊓ mr)
\end{code}

Now we define the actual program.

\begin{code}
gconst₁  : {N T TN : SizedSet}
  → (f : □(T ⊗ ▻ N ⇒ TN))
  → (t : □ T)
  → □(▻(▻ T ⊗ N) ⇒ TN)
gconst₁ f t = const₁ (curry f t)
\end{code}

\begin{code}
replaceMin : Tree → Tree
replaceMin t =
\end{code}

We first give the equation of which we take the fixpoint.
\AgdaAlign{
\begin{code}
  let  f : □(▻(▻ (c Tree) ⊗ c ℕ) ⇒ ▻ (c Tree) ⊗ c ℕ)
       f = gconst₁ rmb t
\end{code}

\begin{code}
       fixpoint : □(▻ (c Tree) ⊗ c ℕ)
       fixpoint = fix f
\end{code}

\begin{code}
  in   force (proj₁ fixpoint) ∞
\end{code}
}
