\AgdaHide{
\begin{code}
module Automata where

open import Function
open import Size
open import Data.Bool
open import Data.Bool.Properties
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Product renaming (map to prod_map)
open import Data.Sum renaming (map to sum_map)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import replaceMin
open import DecEq
\end{code}
}

\begin{code}
data Auto (Σ : Set) (i : Size) : Set where
  Done  :  Auto Σ i                     → Auto Σ i
  Skip  :  ▻ (Auto Σ) i                 → Auto Σ i
  If    :  Σ → ▻ (Auto Σ) i → Auto Σ i  → Auto Σ i
\end{code}

\begin{code}
module _ {Σ : Set} where
  infinite-skip : □ (Auto Σ)
  infinite-skip = fix Skip

  loop-help : Σ → □(Auto Σ) → □(▻ (Auto Σ) ⇒ Auto Σ)
  loop-help a q₁ q₂ = If a q₂ q₁ 

  loop : Σ → □ (Auto Σ) → □ (Auto Σ)
  loop a q = fix (loop-help a q)

  accepting : □ (Auto Σ ⇒ c Bool)
  accepting (Done _)    = true
  accepting (Skip _)    = false
  accepting (If _ _ _)  = false

  move : {{eq_Σ : dec-eq Σ}} → □ (Auto Σ ⇒ c Σ ⇒ ▻ (Auto Σ))
  move (Done q) x = move q x
  move (Skip q) x = q
  move (If a q₁ q₂) x with a == x
  ... | true            = q₁
  ... | false           = move q₂ x

  move∞ : {{eq_Σ : dec-eq Σ}} → Auto Σ ∞ → Σ → Auto Σ ∞
  move∞ q x = force (move q x) ∞

  accept : {{eq_Σ : dec-eq Σ}} → (w : List Σ) → Auto Σ ∞ → Bool
  accept = foldr (λ x f q → f (move∞ q x)) accepting
\end{code}
