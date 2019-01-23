\begin{code}
module DecEq where

open import Agda.Builtin.Unit
open import Data.Bool
open import Data.Bool.Properties
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open ≡-Reasoning

record dec-eq (X : Set) : Set where
  field
    dec : Decidable {A = X} _≡_
open dec-eq {{...}} public

_==_ : {X : Set} → {{eq_X : dec-eq X}} → X → X → Bool
x == y with dec x y
... | yes p = true
... | no p = false
\end{code}

\begin{code}
instance
  nat-dec-eq : dec-eq ℕ
  dec {{nat-dec-eq}} = Data.Nat._≟_
\end{code}
