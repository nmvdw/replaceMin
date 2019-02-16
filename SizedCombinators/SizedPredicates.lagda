\AgdaHide{
\begin{code}
module SizedCombinators.SizedPredicates where

open import Size
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import SizedCombinators.SizedTypes
\end{code}
}

\begin{code}
SizedPredicate : SizedSet → Set₁
SizedPredicate A = {i : Size} → A i → Set

SizedRelation : SizedSet → SizedSet → Set₁
SizedRelation A B = {i : Size} → A i → B i → Set
\end{code}

\begin{code}
all : (A : SizedSet) → SizedPredicate A → SizedSet
all A B i = (x : A i) → B x

syntax all A (λ x → B) = ∏[ x ∈ A ] B
\end{code}

\begin{code}
eq : (A : SizedSet) → SizedRelation A A
eq A x y = x ≡ y

syntax eq A x y = x ≡[ A ]≡ y
\end{code}

\begin{code}
Size<Set : SizedSet
Size<Set i = Size< i
\end{code}
