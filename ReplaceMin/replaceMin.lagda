\AgdaHide{
\begin{code}
module ReplaceMin.replaceMin where

open import Data.Product
open import Data.Nat
open import SizedCombinators
\end{code}
}

\begin{code}
data Tree : Set where
  Leaf : ℕ → Tree
  Node : Tree → Tree → Tree
\end{code}

\begin{code}
▻Leaf : □(▻(c ℕ) ⇒ ▻ (c Tree))
▻Leaf n = pure Leaf ⊛ n

▻Node : □(▻(c Tree) ⇒ ▻(c Tree) ⇒ ▻(c Tree))
▻Node t₁ t₂ = pure Node ⊛ t₁ ⊛ t₂
\end{code}

\begin{code}
fb-h : {T N : SizedSet} → □(▻ N ⇒ ▻ T ⊗ N) → □(▻(▻ T ⊗ N) ⇒ ▻ T ⊗ N)
fb-h f x = f (pure proj₂ ⊛ x)

feedback : {T N : SizedSet} → □(T ⊗ ▻ N ⇒ ▻ T ⊗ N) → □ T → □(▻ T ⊗ N)
feedback f t = fix (fb-h (λ n → f (t , n)))
\end{code}

\begin{code}
rmb : □(c Tree ⊗ ▻(c ℕ) ⇒ (▻(c Tree)) ⊗ c ℕ)
rmb (Leaf x , n) = (▻Leaf n , x)
rmb (Node l r , n) =
  let (l' , ml) = rmb (l , n)
      (r' , mr) = rmb (r , n)
  in (▻Node l' r' , ml ⊓ mr)

replaceMin : Tree → Tree
replaceMin t = force (proj₁(feedback rmb t))
\end{code}
