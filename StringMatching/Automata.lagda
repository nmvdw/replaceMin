\AgdaHide{
\begin{code}
module StringMatching.Automata where

open import Size
open import Data.Bool
open import Data.List
open import SizedCombinators
open import StringMatching.DecEq
\end{code}
}

\begin{code}
data Auto (Σ : Set) (i : Size) : Set where
  Done  :  Auto Σ i                     → Auto Σ i
  Skip  :  ▻ (Auto Σ) i                 → Auto Σ i
  If    :  Σ → ▻ (Auto Σ) i → Auto Σ i  → Auto Σ i
\end{code}

\AgdaHide{
\begin{code}
module _ {Σ : Set} where
\end{code}
}

\begin{code}
  infinite-skip : □ (Auto Σ)
  infinite-skip = fix Skip
\end{code}

\begin{code}
  loop-help : Σ → □(Auto Σ) → □(▻ (Auto Σ) ⇒ Auto Σ)
  loop-help a q₁ q₂ = If a q₂ q₁ 
\end{code}

\begin{code}
  loop : Σ → □ (Auto Σ) → □ (Auto Σ)
  loop a q = fix (loop-help a q)
\end{code}

\begin{code}
  accepting : □ (Auto Σ ⇒ c Bool)
  accepting (Done _)    = true
  accepting (Skip _)    = false
  accepting (If _ _ _)  = false
\end{code}

\begin{code}
  move : {{eq_Σ : dec-eq Σ}} → □ (Auto Σ ⇒ c Σ ⇒ ▻ (Auto Σ))
  move (Done q) x = move q x
  move (Skip q) x = q
  move (If a q₁ q₂) x with a == x
  ... | true            = q₁
  ... | false           = move q₂ x
\end{code}

\begin{code}
  move∞ : {{eq_Σ : dec-eq Σ}} → Auto Σ ∞ → Σ → Auto Σ ∞
  move∞ q x = force (move q x)
\end{code}

\begin{code}
  accept : {{eq_Σ : dec-eq Σ}} → (w : List Σ) → Auto Σ ∞ → Bool
  accept = foldr (λ x f q → f (move∞ q x)) accepting
\end{code}
