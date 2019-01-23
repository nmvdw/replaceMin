\AgdaHide{
\begin{code}
module StringMatching where

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
open import Automata
open import DecEq
\end{code}
}

\begin{code}
zip-int-help : {A : Set} → List A → ℕ → List (ℕ × A)
zip-int-help []        _  = []
zip-int-help (x ∷ xs)  i  = (i , x) ∷ zip-int-help xs (i + 1)

zip-int : {A : Set} → List A → List (ℕ × A)
zip-int l = zip-int-help l 0

module _ {Σ : Set} {{eq_Σ : dec-eq Σ}} where
  improve : □(Auto Σ ⇒ c Σ ⇒ Auto Σ)
  improve (If a q₁ q₂) x with a == x
  ... | true              = q₂
  ... | false             = If a q₁ q₂
  improve q            x  = q

  kmp-alt : List Σ → □(Auto Σ ⇒ Auto Σ)
  kmp-alt []        q  = Done q
  kmp-alt (a ∷ as)  q  = If a
                            (pure (kmp-alt as) ⊛ move q a)
                            (improve q a)

  kmp-auto-help : List Σ → □(▻ (Auto Σ) ⇒ Auto Σ)
  kmp-auto-help w q = kmp-alt w (Skip q)

  kmp-auto : List Σ → □(Auto Σ)
  kmp-auto w = fix (kmp-auto-help w)

  substring : Auto Σ ∞ → List Σ → Bool
  substring lang txt = or (map accepting (scanl move∞ lang txt))

  matches : Auto Σ ∞ → List Σ → List ℕ
  matches lang txt = map proj₁
                         (boolFilter (accepting ∘ proj₂)
                                     (zip-int (scanl move∞ lang txt)))

  match-substring : List Σ → List Σ → Bool
  match-substring ptrn txt  = substring (kmp-auto ptrn) txt

  match-indices : List Σ → List Σ → List ℕ
  match-indices ptrn txt = matches (kmp-auto ptrn) txt
\end{code}
