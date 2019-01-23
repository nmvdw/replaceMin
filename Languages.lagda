\AgdaHide{
\begin{code}
module Languages where

open import Function
open import Size
open import Data.Bool
open import Data.Bool.Properties
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Product renaming (map to prod_map)
open import Data.Sum renaming (map to sum_map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import SizedTypes
open import Automata
open import StringMatching
open import DecEq
\end{code}
}

\begin{code}
record Lang (Σ : Set) (i : Size)  : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → Σ → Lang Σ j
open Lang

_∈_ : ∀ {Σ} → List Σ → Lang Σ ∞ → Bool
[] ∈ L = ν L
(a ∷ as) ∈ L = as ∈ δ L a

∅ : ∀ {i Σ} → Lang Σ i
ν ∅ = false
δ ∅ x = ∅

w∉∅ : ∀ {Σ} → (w : List Σ) → w ∈ ∅ ≡ false
w∉∅ [] = refl
w∉∅ (x ∷ w) = w∉∅ w

accept-all : ∀ {i} → (Σ : Set) → Lang Σ i
accept-all Σ .ν = true
accept-all Σ .δ x = accept-all Σ

w∈Σ* : ∀ {Σ} → (w : List Σ) → w ∈ accept-all Σ ≡ true
w∈Σ* [] = refl
w∈Σ* (x ∷ xs) = w∈Σ* xs

ε : ∀ {i} → {Σ : Set} → Lang Σ i
ν ε = true
δ ε x = ∅

w∈ε : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (w : List Σ) → w ∈ ε ≡ w == []
w∈ε [] = refl
w∈ε (x ∷ xs) = w∉∅ xs

acceptΣ : ∀ {i Σ} → Lang Σ i
ν acceptΣ = false
δ acceptΣ x = ε

w∈acceptΣ : ∀ {Σ} → (w : List Σ) → w ∈ acceptΣ ≡ length w == 1
w∈acceptΣ [] = refl
w∈acceptΣ (x₁ ∷ []) = refl
w∈acceptΣ (x₁ ∷ x₂ ∷ xs) = w∉∅ xs

accept-a : ∀ {i} → {Σ : Set} {{dec_Σ : dec-eq Σ}} → Σ → Lang Σ i
ν (accept-a a) = false
δ (accept-a a) x = if x == a then ε else ∅

w∈accept-a : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (a : Σ) (w : List Σ) → w ∈ accept-a a ≡ w == (a ∷ [])
w∈accept-a a [] = refl
w∈accept-a a (x₁ ∷ []) with dec x₁ a
... | yes p rewrite p = refl
... | no p = refl
w∈accept-a a (x₁ ∷ x₂ ∷ xs) with dec x₁ a
... | yes p = w∉∅ xs
... | no p = w∉∅ xs

_∪_ : ∀ {i Σ} → Lang Σ i → Lang Σ i → Lang Σ i
(a ∪ b) .ν = ν a ∨ ν b
(a ∪ b) .δ x = δ a x ∪ δ b x

∪∨ : ∀ {Σ} → (L₁ L₂ : Lang Σ ∞) (w : List Σ) → (w ∈ (L₁ ∪ L₂)) ≡ (w ∈ L₁ ∨ w ∈ L₂)
∪∨ L₁ L₂ [] = refl
∪∨ L₁ L₂ (x ∷ xs) = ∪∨ (δ L₁ x) (δ L₂ x) xs

∪l : ∀ {Σ} → (L₁ L₂ : Lang Σ ∞) (w : List Σ) → (w ∈ L₁ ≡ true) → (w ∈ (L₁ ∪ L₂) ≡ true)
∪l L₁ L₂ w H =
  begin
    w ∈ (L₁ ∪ L₂)
  ≡⟨ ∪∨ L₁ L₂ w ⟩
    (w ∈ L₁) ∨ (w ∈ L₂)
  ≡⟨ cong (λ a → a ∨ (w ∈ L₂)) H ⟩
    true ∨ (w ∈ L₂)
  ≡⟨ refl ⟩
    true ∎

∪r : ∀ {Σ} → (L₁ L₂ : Lang Σ ∞) (w : List Σ) → (w ∈ L₂ ≡ true) → (w ∈ (L₁ ∪ L₂) ≡ true)
∪r L₁ L₂ w H rewrite ∪∨ L₁ L₂ w | H with w ∈ L₁
... | true = refl
... | false = refl

∅∪L : ∀ {Σ} → (L : Lang Σ ∞) (w : List Σ) → w ∈ (∅ ∪ L) ≡ w ∈ L
∅∪L L w =
  begin
    w ∈ (∅ ∪ L)
  ≡⟨ ∪∨ ∅ L w ⟩
    w ∈ ∅ ∨ w ∈ L
  ≡⟨ cong (λ z → z ∨ w ∈ L) (w∉∅ w) ⟩
    w ∈ L ∎

_·c_ : ∀ {i Σ} → Lang Σ i → Lang Σ i → Lang Σ i
ν (a ·c b) = ν a ∧ ν b
δ (a ·c b) x = if ν a then δ a x ·c b ∪ δ b x else δ a x ·c b

infixl 20 _·c_
infixl 10 _∪_

·append : ∀ {Σ} → (L₁ L₂ : Lang Σ ∞) → (w₁ w₂ : List Σ) → w₁ ∈ L₁ ≡ true → w₂ ∈ L₂ ≡ true → ((w₁ ++ w₂) ∈ (L₁ ·c L₂)) ≡ true
·append L₁ L₂ [] [] H₁ H₂ =
  begin
    ν L₁ ∧ ν L₂
  ≡⟨ cong (λ z → z ∧ ν L₂) H₁ ⟩
    true ∧ ν L₂
  ≡⟨ cong (λ z → true ∧ z) H₂ ⟩
    true ∧ true
  ≡⟨ refl ⟩
    true ∎
·append L₁ L₂ [] (x ∷ w₂) H₁ H₂ =
  begin
    w₂ ∈ (if ν L₁ then δ L₁ x ·c L₂ ∪ δ L₂ x else δ L₁ x ·c L₂)
  ≡⟨ cong (λ z → w₂ ∈ (if z then δ L₁ x ·c L₂ ∪ δ L₂ x else δ L₁ x ·c L₂)) H₁ ⟩
    w₂ ∈ (δ L₁ x ·c L₂ ∪ δ L₂ x)
  ≡⟨ ∪r (δ L₁ x ·c L₂) (δ L₂ x) w₂ H₂ ⟩
    true ∎
·append L₁ L₂ (x ∷ xs) ys H₁ H₂ with (ν L₁)
... | true = ∪l (δ L₁ x ·c L₂) (δ L₂ x) (xs ++ ys) (·append (δ L₁ x) L₂ xs ys H₁ H₂)
... | false = ·append (δ L₁ x) L₂ xs ys H₁ H₂

w∉∅·c : ∀ {Σ} → (L : Lang Σ ∞) (w : List Σ) → (w ∈ (∅ ·c L)) ≡ false
w∉∅·c L [] = refl
w∉∅·c L (x ∷ xs) = w∉∅·c L xs

w∈ε·c : ∀ {Σ} → (L : Lang Σ ∞) (w : List Σ) → (w ∈ (ε ·c L)) ≡ w ∈ L
w∈ε·c L [] = refl
w∈ε·c L (x ∷ xs) =
  begin
    (x ∷ xs) ∈ (ε ·c L)
  ≡⟨ ∪∨ (∅ ·c L) (δ L x) xs ⟩
    xs ∈ (∅ ·c L) ∨ xs ∈ δ L x
  ≡⟨ cong (λ z → z ∨ xs ∈ δ L x) (w∉∅·c L xs)  ⟩
    false ∨ xs ∈ δ L x
  ≡⟨ refl ⟩
    xs ∈ δ L x
  ≡⟨ refl ⟩
    (x ∷ xs) ∈ L ∎

w∈·cε : ∀ {Σ} → (L : Lang Σ ∞) (w : List Σ) → (w ∈ (L ·c ε)) ≡ w ∈ L
w∈·cε L [] with ν L
... | true = refl
... | false = refl
w∈·cε L (x ∷ xs) with ν L
... | true =
      begin
        xs ∈ (δ L x ·c ε ∪ ∅)
      ≡⟨ ∪∨ (δ L x ·c ε) ∅ xs ⟩
        xs ∈ (δ L x ·c ε) ∨ xs ∈ ∅
      ≡⟨ cong (λ z → xs ∈ (δ L x ·c ε) ∨ z) (w∉∅ xs) ⟩
        xs ∈ (δ L x ·c ε) ∨ false
      ≡⟨ ∨-identityʳ (xs ∈ (δ L x ·c ε)) ⟩
        xs ∈ (δ L x ·c ε)
      ≡⟨ w∈·cε (δ L x) xs ⟩
        xs ∈ δ L x
      ≡⟨ refl ⟩
        (x ∷ xs) ∈ L ∎
... | false =
      begin
        (xs ∈ (δ L x ·c ε))
      ≡⟨ w∈·cε (δ L x) xs ⟩
        (xs ∈ δ L x)
      ≡⟨ refl ⟩
        (x ∷ xs) ∈ L ∎

accept-w : ∀ {i} → {Σ : Set} {{dec_Σ : dec-eq Σ}} → List Σ → Lang Σ i
accept-w [] = ε
accept-w (x ∷ xs) = accept-a x ·c accept-w xs

v∈accept-w : {Σ : Set} {{dec_Σ : dec-eq Σ}} → (v w : List Σ) → v ∈ accept-w w ≡ v == w
v∈accept-w [] [] = refl
v∈accept-w [] (y ∷ ys) = refl
v∈accept-w (x ∷ xs) [] = w∉∅ xs
v∈accept-w (x ∷ xs) (y ∷ ys) rewrite l-== x y xs ys with dec x y
... | yes p =
      begin
        xs ∈ (ε ·c accept-w ys)
      ≡⟨ w∈ε·c (accept-w ys) xs ⟩
        xs ∈ accept-w ys
      ≡⟨ v∈accept-w xs ys ⟩
        xs == ys ∎
... | no p = w∉∅·c (accept-w ys) xs

w∈accept-w : {Σ : Set} {{dec_Σ : dec-eq Σ}} → (w : List Σ) → w ∈ accept-w w ≡ true
w∈accept-w w =
  begin
    w ∈ accept-w w
  ≡⟨ v∈accept-w w w ⟩
    w == w
  ≡⟨ ==-refl w ⟩
    true ∎

end-w : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (w : List Σ) → Lang Σ ∞
end-w {Σ} w = (accept-all Σ) ·c accept-w w

postfix : {A : Set} → {{dec_A : dec-eq A}} → (l₁ l₂ : List A) → Bool
postfix [] [] = true
postfix [] (y ∷ ys) = false
postfix (x ∷ xs) [] = true
postfix (x ∷ xs) (y ∷ ys) = ((x ∷ xs) == (y ∷ ys)) ∨ postfix xs (y ∷ ys)

end-w-postfix : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (w w-end : List Σ) → w ∈ end-w w-end ≡ postfix w w-end
end-w-postfix [] [] = refl
end-w-postfix [] (y ∷ ys) = refl
end-w-postfix {Σ} (x ∷ xs) [] =
  begin
    xs ∈ δ (end-w []) x
  ≡⟨ ∪∨ (accept-all Σ ·c ε) ∅ xs ⟩
    (xs ∈ (accept-all Σ ·c ε)) ∨ (xs ∈ ∅)
  ≡⟨ cong (λ z → (xs ∈ (accept-all Σ ·c ε)) ∨ z) (w∉∅ xs) ⟩
    xs ∈ (accept-all Σ ·c ε) ∨ false
  ≡⟨ ∨-identityʳ (xs ∈ (accept-all Σ ·c ε)) ⟩
    xs ∈ (accept-all Σ ·c ε)
  ≡⟨ w∈·cε (accept-all Σ) xs ⟩
    (xs ∈ accept-all Σ)
  ≡⟨ w∈Σ* xs ⟩
    true ∎
end-w-postfix {Σ} (x ∷ xs) (y ∷ ys) rewrite l-== x y xs ys with dec x y
... | yes p rewrite p =
      begin
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys) ∪ ε ·c accept-w ys)
      ≡⟨ ∪∨ (accept-all Σ ·c (accept-a y ·c accept-w ys)) (ε ·c accept-w ys) xs ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ (xs ∈ (ε ·c accept-w ys))
      ≡⟨ cong (λ z → (xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ z)) (w∈ε·c (accept-w ys) xs) ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ xs ∈ accept-w ys
      ≡⟨ cong (λ z → (xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ z)) (v∈accept-w xs ys) ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ xs == ys
      ≡⟨ cong (λ z → z ∨ xs == ys) (end-w-postfix xs (y ∷ ys)) ⟩
        postfix xs (y ∷ ys) ∨ xs == ys
      ≡⟨ ∨-comm (postfix xs (y ∷ ys)) (xs == ys) ⟩
        xs == ys ∨ postfix xs (y ∷ ys) ∎
... | no p =
      begin
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys) ∪ ∅ ·c accept-w ys)
      ≡⟨ ∪∨ (accept-all Σ ·c (accept-a y ·c accept-w ys)) (∅ ·c accept-w ys) xs ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ (xs ∈ (∅ ·c accept-w ys))
      ≡⟨ cong (λ z → xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ z) (w∉∅·c (accept-w ys) xs) ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys)) ∨ false
      ≡⟨ ∨-identityʳ (xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys))) ⟩
        xs ∈ (accept-all Σ ·c (accept-a y ·c accept-w ys))
      ≡⟨ end-w-postfix xs (y ∷ ys) ⟩
        postfix xs (y ∷ ys) ∎

[[_]]' : ∀ {i} {Σ} → {{dec_Σ : dec-eq Σ}} → Auto Σ i → Lang Σ i
[[ Done q ]]' = ε ∪ [[ q ]]'
ν [[ Skip q ]]' = false
δ [[ Skip q ]]' x = [[ force q ]]'
ν [[ If a q₁ q₂ ]]' = ν [[ q₂ ]]'
δ [[ If a q₁ q₂ ]]' x with x == a
... | true = [[ force q₁ ]]' ∪ δ [[ q₂ ]]' x
... | false = δ [[ q₂ ]]' x

[[_]] : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → Auto Σ ∞ → Lang Σ ∞
[[ Done q ]] = ε ∪ [[ q ]]
[[ Skip q ]] = acceptΣ ·c [[ force q ]]
[[ If a q₁ q₂ ]] = (accept-a a ·c [[ force q₁ ]]) ∪ [[ q₂ ]]

νkek : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) → ν [[ q ]]' ≡ ν [[ q ]]
νkek (Done q) = refl
νkek (Skip q) = refl
νkek (If a q₁ q₂) = νkek q₂

δkek : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) (x : Σ) (w : List Σ) → w ∈ (δ [[ q ]]' x) ≡ w ∈ (δ [[ q ]] x)
kek : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) (w : List Σ) → w ∈ [[ q ]]' ≡ w ∈ [[ q ]]
δkek (Done q) x w rewrite ∅∪L (δ [[ q ]]' x) w | ∅∪L (δ [[ q ]] x) w | δkek q x w = refl
δkek (Skip q) x w rewrite kek (force q) w | w∈ε·c [[ force q ]] w = refl
δkek (If a q₁ q₂) x w with x == a
... | true rewrite ∪∨ [[ force q₁ ]]' (δ [[ q₂ ]]' x) w
                 | ∪∨ (ε ·c [[ force q₁ ]]) (δ [[ q₂ ]] x) w
                 | w∈ε·c [[ force q₁ ]] w
                 | kek (force q₁) w
                 | δkek q₂ x w = {!!}
... | false rewrite ∪∨ (∅ ·c [[ force q₁ ]]) (δ [[ q₂ ]] x) w
           | w∉∅·c [[ force q₁ ]] w = δkek q₂ x w
kek (Done q) w =
  begin
    w ∈ (ε ∪ [[ q ]]')
  ≡⟨ ∪∨ ε [[ q ]]' w ⟩
    w ∈ ε ∨ w ∈ [[ q ]]'
  ≡⟨ cong (λ z → w ∈ ε ∨ z) (kek q w) ⟩
    w ∈ ε ∨ w ∈ [[ q ]]
  ≡⟨ sym(∪∨ ε [[ q ]] w) ⟩
    w ∈ (ε ∪ [[ q ]]) ∎
kek (Skip q) [] = refl
kek (Skip q) (x ∷ xs) =
  begin
    xs ∈ [[ force q ]]'
  ≡⟨ kek (force q) xs ⟩
    xs ∈ [[ force q ]]
  ≡⟨ sym (w∈ε·c [[ force q ]] xs) ⟩
    xs ∈ (ε ·c [[ force q ]]) ∎
kek (If a q₁ q₂) [] = νkek q₂
kek (If a q₁ q₂) (x ∷ xs) with x == a
... | true =
      begin
        xs ∈ ([[ force q₁ ]]' ∪ δ [[ q₂ ]]' x)
      ≡⟨ ∪∨ [[ force q₁ ]]' (δ [[ q₂ ]]' x) xs ⟩
        xs ∈ [[ force q₁ ]]' ∨ xs ∈ δ [[ q₂ ]]' x
      ≡⟨ cong (λ z → z ∨ xs ∈ δ [[ q₂ ]]' x) (kek (force q₁) xs) ⟩
        xs ∈ [[ force q₁ ]] ∨ xs ∈ δ [[ q₂ ]]' x
      ≡⟨ {!!} ⟩
        (xs ∈ (ε ·c [[ force q₁ ]] ∪ δ [[ q₂ ]] x)) ∎
... | false = {!!}

data invariant {Σ} {{dec_Σ : dec-eq Σ}} : Auto Σ ∞ → Set where
  done-invariant : (q : Auto Σ ∞) → ν [[ q ]] ≡ false → invariant q → invariant (Done q)
  skip-invariant : (q : Thunk (Auto Σ) ∞) → invariant (force q) → invariant (Skip q)
  if-invariant : (a : Σ) (q₁ : Thunk (Auto Σ) ∞) (q₂ : Auto Σ ∞)
                   → invariant (force q₁) → invariant q₂
                   → ν [[ q₂ ]] ≡ false
                   → ((w : List Σ) (x : Σ) → x == a ≡ true → (x ∷ w) ∈ [[ q₂ ]] ≡ true → (w ∈ [[ force q₁ ]]) ≡ true)
                   → invariant (If a q₁ q₂)

move-invariant : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) → invariant q → (a : Σ) → invariant (move∞ q a)
move-invariant .(Done q) (done-invariant q x H) a = move-invariant q H a
move-invariant .(Skip q) (skip-invariant q H) a = H
move-invariant .(If a q₁ q₂) (if-invariant a q₁ q₂ Hl Hr Hq₁ Hq₂) x with a == x
... | true = Hl
... | false = move-invariant q₂ Hr x

inv-accept : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) → invariant q → accepting q ≡ ν [[ q ]]
inv-accept .(Done q) (done-invariant q νf H) = refl
inv-accept .(Skip q) (skip-invariant q H) = refl
inv-accept .(If a q₁ q₂) (if-invariant a q₁ q₂ Hq₁ Hq₂ H₁ H₂) = sym H₁

∨max : {b₁ b₂ : Bool} → (b₁ ≡ true → b₂ ≡ true) → b₂ ≡ b₂ ∨ b₁
∨max {false} {b₂} H = sym (∨-identityʳ b₂)
∨max {true} {false} H = H refl
∨max {true} {true} H = refl

inv-move : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (q : Auto Σ ∞) → invariant q → (a : Σ) (w : List Σ) → (w ∈ [[ move∞ q a ]]) ≡ w ∈ δ [[ q ]] a
inv-move .(Done q) (done-invariant q νf H) a w rewrite inv-move q H a w | ∪∨ ∅ (δ [[ q ]] a) w | w∉∅ w = refl
inv-move .(Skip q) (skip-invariant q H) a w rewrite w∈ε·c [[ force q ]] w = refl
inv-move .(If a q₁ q₂) (if-invariant a q₁ q₂ Hq₁ Hq₂ H₁ H₂) x w rewrite ==-sym a x with x == a Data.Bool.≟ true
... | yes p rewrite p | ∪∨ (ε ·c [[ force q₁ ]]) (δ [[ q₂ ]] x) w | w∈ε·c [[ force q₁ ]] w = ∨max (H₂ w x p)
... | no p rewrite ¬-not p | ∪∨ (∅ ·c [[ force q₁ ]]) (δ [[ q₂ ]] x) w | w∉∅·c [[ force q₁ ]] w = inv-move q₂ Hq₂ x w

spec : ∀ {Σ} → {{dec_Σ : dec-eq Σ}} → (w : List Σ) → (q : Auto Σ ∞) → invariant q → accept w q ≡ w ∈ [[ q ]]
spec [] = inv-accept
spec (x ∷ xs) q H rewrite sym (inv-move q H x xs) = spec xs (move∞ q x) (move-invariant q H x)

double-if : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (a : Σ) (q₁ q₂ : Thunk (Auto Σ) ∞) (q₃ : Auto Σ ∞) → (w : List Σ)
             → accept w (If a q₁ (If a q₂ q₃)) ≡ accept w (If a q₁ q₃)
double-if a q₁ q₂ q₃ [] = refl
double-if a q₁ q₂ q₃ (x ∷ xs) with a == x Data.Bool.≟ true
... | yes p rewrite p = refl
... | no p rewrite ¬-not p | ¬-not p  = refl

wtf : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (a : Σ) (q₁ q₂ : Thunk (Auto Σ) ∞) (q₃ : Auto Σ ∞) → (w : List Σ)
             → w ∈ [[ If a q₁ q₃ ]] ≡ w ∈ [[ If a q₁ (If a q₂ q₃) ]]
wtf a q₁ q₂ q₃ w =
  begin
    w ∈ [[ If a q₁ q₃ ]]
  ≡⟨ sym(spec w (If a q₁ q₃) {!!}) ⟩
    accept w (If a q₁ q₃)
  ≡⟨ sym(double-if a q₁ q₂ q₃ w) ⟩
    accept w (If a q₁ (If a q₂ q₃))
  ≡⟨ spec w (If a q₁ (If a q₂ q₃)) {!!} ⟩
    w ∈ [[ If a q₁ (If a q₂ q₃) ]] ∎

improve-spec : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (q : Thunk (Auto Σ) ∞) (r : Auto Σ ∞) → (a : Σ) → (w : List Σ) → w ∈ [[ If a q (improve r a) ]] ≡ w ∈ [[ If a q r ]]
improve-spec q (Done r) a w = refl
improve-spec q (Skip r) a w = refl
improve-spec q (If b r₁ r₂) a w with dec b a
... | yes p rewrite p =
      begin
        w ∈ [[ If a q r₂ ]]
      ≡⟨ wtf a q r₁ r₂ w ⟩
        w ∈ [[ If a q (If a r₁ r₂) ]] ∎
... | no p = refl

improve-invariant : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (q : Auto Σ ∞) → invariant q → (a : Σ) → invariant (improve q a)
improve-invariant .(Done q) (done-invariant q H₁ H₂) x = done-invariant q H₁ H₂
improve-invariant .(Skip q) (skip-invariant q H) x = skip-invariant q H
improve-invariant .(If a q₁ q₂) (if-invariant a q₁ q₂ H₁ H₂ Hq₁ Hq₂) x with a == x
... | true = H₂
... | false = if-invariant a q₁ q₂ H₁ H₂ Hq₁ Hq₂

alt-spec : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (w v : List Σ) (q : Auto Σ ∞) → v ∈ [[ kmp-alt w q ]] ≡ v ∈ (accept-w w ∪ [[ q ]])
alt-spec [] v q = refl
alt-spec (x ∷ xs) v q =
  begin
    v ∈ [[ kmp-alt (x ∷ xs) q ]]
  ≡⟨ refl ⟩
    v ∈ [[ If x (λ where .force → kmp-alt xs (move∞ q x)) (improve q x) ]]
  ≡⟨ improve-spec (λ where .force → kmp-alt xs (move∞ q x)) q x v ⟩
    v ∈ [[ If x (λ where .force → kmp-alt xs (move∞ q x)) q ]]
  ≡⟨ {!!} ⟩
    v ∈ (accept-w (x ∷ xs) ∪ [[ q ]]) ∎

alt-invariant : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (w : List Σ) (q : Auto Σ ∞) → ν [[ q ]] ≡ false → invariant q → invariant (kmp-alt w q)
alt-invariant [] q H₁ H₂ = done-invariant q H₁ H₂
alt-invariant (x ∷ xs) q H₁ H₂ = if-invariant x {!!} (improve q x) (alt-invariant xs (move∞ q x) {!!} {!!}) {!!} {!!} {!!}

kmp-auto-spec : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (v w : List Σ) → v ∈ [[ kmp-auto w ]] ≡ v ∈ (accept-w w ∪ acceptΣ ·c [[ kmp-auto w ]])
kmp-auto-spec {Σ} v w = alt-spec w v (Skip {!!})

kmp-auto-invariant : ∀ {Σ} → {{eq_Σ : dec-eq Σ}} → (w : List Σ) → invariant (kmp-auto w)
kmp-auto-invariant w = alt-invariant w (Skip {!!}) refl (skip-invariant {!!} {!!})
\end{code}
