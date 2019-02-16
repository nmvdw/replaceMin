\AgdaHide{
\begin{code}
module SizedCombinators.SizedTypes where

open import Size
open import Data.Nat
open import Data.Product

infixl 30 _⊛_
infixr 30 _⇒_
infixr 50 _⊗_
\end{code}
}

\begin{code}
SizedSet = Size → Set
\end{code}

\begin{code}
_⇒_ : SizedSet → SizedSet → SizedSet
(A ⇒ B) i = A i → B i

_⊗_ : SizedSet → SizedSet → SizedSet
(A ⊗ B) i = A i × B i

c : Set → SizedSet
c A i = A
\end{code}

\begin{code}
□ : SizedSet → Set
□ A = {i : Size} → A i
\end{code}

\begin{code}
record ▻ (A : SizedSet) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → A j
\end{code}

\AgdaHide{
\begin{code}
open ▻ public
\end{code}
}

\begin{code}
pure : {A : SizedSet} → □ A → □(▻ A)
force (pure x) = x

_⊛_ : {A B : SizedSet} → □(▻(A ⇒ B) ⇒ ▻ A ⇒ ▻ B)
force (f ⊛ x) = force f (force x)
\end{code}

\begin{code}
fix : {A : SizedSet} → □(▻ A ⇒ A) → □ A
▻fix : {A : SizedSet} → □(▻ A ⇒ A) → □ (▻ A)
fix f {i} = f (▻fix f {i})
force (▻fix f {i}) {j} = fix f {j}
\end{code}

\begin{code}
_ : ℕ × ℕ
_ = force (proj₁ equation) , proj₂ equation
  where
    equation-h : □(▻(c ℕ) ⇒ ▻(c ℕ) ⊗ c ℕ) → □(▻(▻(c ℕ) ⊗ c ℕ) ⇒ ▻(c ℕ) ⊗ c ℕ)
    equation-h f x = f (pure proj₂ ⊛ x)
    equation : □(▻(c ℕ) ⊗ c ℕ)
    equation = fix (equation-h (λ x → x , 1))
\end{code}
