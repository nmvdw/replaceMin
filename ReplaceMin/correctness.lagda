\AgdaHide{
\begin{code}
module ReplaceMin.correctness where

open import Size
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import SizedCombinators
open import ReplaceMin.replaceMin
\end{code}
}

\begin{code}
replace : Tree → ℕ → Tree
replace (Leaf x) n = Leaf n
replace (Node l r) n = Node (replace l n) (replace r n)

min-tree : Tree → ℕ
min-tree (Leaf x) = x
min-tree (Node l r) = min-tree l ⊓ min-tree r

replaceMin-spec : Tree → Tree
replaceMin-spec t = replace t (min-tree t)
\end{code}

\begin{code}
rmb₁ : □(∏[ p ∈ Size<Set ⊗ (c Tree ⊗ ▻(c ℕ)) ]
            let (j , t , n) = p in
            (force (proj₁ (rmb (t , n))) {j} ≡ replace t (force n {j})))
rmb₁ (j , Leaf x , n) = refl
rmb₁ (j , Node l r , n) =
  begin
    force (▻Node (proj₁ (rmb (l , n))) (proj₁ (rmb (r , n))))
  ≡⟨⟩
    Node (force (proj₁ (rmb (l , n)))) (force (proj₁ (rmb (r , n))))
  ≡⟨ cong (λ z → Node z (force (proj₁ (rmb (r , n))))) (rmb₁ (j , l , n)) ⟩
    Node (replace l (force n)) (force (proj₁ (rmb (r , n))))
  ≡⟨ cong (λ z → Node (replace l (force n)) z) (rmb₁ (j , r , n)) ⟩
    Node (replace l (force n)) (replace r (force n))
  ∎

rmb₂ : □(∏[ p ∈ c Tree ⊗ ▻(c ℕ) ]
            let (t , n) = p in
            (proj₂ (rmb (t , n)) ≡[ c ℕ ]≡ min-tree t))
rmb₂ (Leaf x , n) = refl
rmb₂ (Node l r , n) =
  begin
    proj₂ (rmb (l , n)) ⊓ proj₂ (rmb (r , n))
  ≡⟨ cong (λ z → z ⊓ proj₂ (rmb (r , n))) (rmb₂ (l , n)) ⟩
    min-tree l ⊓ proj₂ (rmb (r , n))
  ≡⟨ cong (λ z → min-tree l ⊓ z) (rmb₂ (r , n)) ⟩
    min-tree l ⊓ min-tree r
  ∎

rm-correct : (t : Tree) → replaceMin t ≡ replaceMin-spec t
rm-correct t =
  begin
    replaceMin t
  ≡⟨⟩
    force (proj₁ (rmb (t , pure proj₂ ⊛ ▻fix (fb-h (λ n → rmb (t , n))))))
  ≡⟨ rmb₁ (∞ , t , pure proj₂ ⊛ ▻fix (fb-h (λ x → rmb (t , x)))) ⟩
    replace t (proj₂ (fix (fb-h (λ x → rmb (t , x)))))
  ≡⟨⟩
    replace t (proj₂ (rmb (t , pure proj₂ ⊛ ▻fix (fb-h (λ x → rmb (t , x))))))
  ≡⟨ cong (replace t) (rmb₂ (t , pure proj₂ ⊛ ▻fix (fb-h (λ x → rmb (t , x))))) ⟩
    replace t (min-tree t)
  ∎
\end{code}
