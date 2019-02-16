\AgdaHide{
\begin{code}
module ReplaceMin.correctness where

open import Preamble
open import SizedCombinators
open import ReplaceMin.replaceMin
\end{code}
}

\begin{code}
replace : Tree → ℕ → Tree
replace (Leaf x) n = Leaf n
replace (Node l r) n = Node (replace l n) (replace r n)

min : Tree → ℕ
min (Leaf x) = x
min (Node l r) = min l ⊓ min r

replaceMin-spec : Tree → Tree
replaceMin-spec t = replace t (min t)
\end{code}

The proof of functional correctness goes in three step.
We start by computing \AF{rmb} and for that, we compute its first and second coordinate.
Since the first projection of \AF{rmb} is computed lazily, we need to force it.

\begin{code}
rmb₁ : □(∏[ p ∈ Size<Set ⊗ c Tree ⊗ ▻(c ℕ) ]
            let (j , t , n) = p
            in force (proj₁ (rmb (t , n))) j
               ≡
               replace t (force n j))
rmb₁ (j , Leaf x , n) = refl
rmb₁ (j , Node l r , n) =
  begin
    force (▻Node
            (proj₁ (rmb (l , n)))
            (proj₁ (rmb (r , n))))
          j
  ≡⟨⟩
    Node
      (force (proj₁ (rmb (l , n))) j)
      (force (proj₁ (rmb (r , n))) j)
  ≡⟨ cong (λ z → Node z _) (rmb₁ (j , l , n)) ⟩
    Node
      (replace l (force n j))
      (force (proj₁ (rmb (r , n))) j)
  ≡⟨ cong (λ z → Node _ z) (rmb₁ (j , r , n)) ⟩
    Node
      (replace l (force n j))
      (replace r (force n j))
  ∎
\end{code}

The second projection is easier.

\begin{code}
rmb₂ : □(∏[ p ∈ c Tree ⊗ ▻(c ℕ) ]
            let (t , n) = p
            in proj₂ (rmb (t , n))
               ≡
               min t)
rmb₂ (Leaf x , n) = refl
rmb₂ (Node l r , n) =
  begin
    proj₂ (rmb (l , n)) ⊓ proj₂ (rmb (r , n))
  ≡⟨ cong (λ z → z ⊓ _) (rmb₂ (l , n)) ⟩
    min l ⊓ proj₂ (rmb (r , n))
  ≡⟨ cong (λ z → _ ⊓ z) (rmb₂ (r , n)) ⟩
    min l ⊓ min r
  ∎
\end{code}

Now we use them both to compute \AF{replaceMin}.

\begin{code}
rm-correct : (t : Tree)
  → replaceMin t ≡ replaceMin-spec t
rm-correct t =
  begin
    replaceMin t
  ≡⟨⟩
    force (proj₁ (rmb (t , pure proj₂ ⊛ ▻fix (gconst₁ rmb t)))) ∞
  ≡⟨ rmb₁ (∞ , t , pure proj₂ ⊛ ▻fix (gconst₁ rmb t)) ⟩
    replace t (proj₂ (fix (gconst₁ rmb t)))
  ≡⟨⟩
    replace t (proj₂ (rmb (t , _)))
  ≡⟨ cong (replace t) (rmb₂ (t , _)) ⟩
    replace t (min t)
  ∎
\end{code}
