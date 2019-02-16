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

A sized type is a family indexed by sizes.
Formally, we define it as follows.

\begin{code}
SizedSet = Size → Set
\end{code}

To work with sized types, we define several combinators.
These come in two flavors.
Firstly, we have combinators to construct sized types.
The first two of these are analogs of the function type and product type.

\begin{code}
_⇒_ : SizedSet → SizedSet → SizedSet
(A ⇒ B) i = A i → B i

_⊗_ : SizedSet → SizedSet → SizedSet
(A ⊗ B) i = A i × B i
\end{code}

As usual, \AD{_⊗_} binds stronger than \AD{_⇒_}.
Beside those, two combinators, which relate types and sized types.
Types can be transformed into sized types by taking the constant family.

\begin{code}
c : Set → SizedSet
c A i = A
\end{code}

Conversly, we can turn sized types into types by taking the product.
This operation is called the \emph{box modality}, and we denote it by \AF{□}.

\begin{code}
□ : SizedSet → Set
□ A = {i : Size} → A i
\end{code}

The last construction we need, represents delayed computations.

\begin{code}
record ▻ (A : SizedSet) (i : Size) : Set where
  coinductive
  field force : (j : Size< i) → A j
\end{code}

\AgdaHide{
\begin{code}
open ▻ public
\end{code}
}

Secondly, we define combinators to define terms of sized types.
We start by giving \AF{▻} the structure of an applicative functor.

\begin{code}
pure : {A : SizedSet} → □ A → □(▻ A)
force (pure x) i = x

_⊛_ : {A B : SizedSet} → □(▻(A ⇒ B) ⇒ ▻ A ⇒ ▻ B)
force (f ⊛ x) i = force f i (force x i)
\end{code}

Lastly, we have a fixpoint combinator, which takes the fixpoint of productive function.

\begin{code}
fix : {A : SizedSet} → □(▻ A ⇒ A) → □ A
▻fix : {A : SizedSet} → □(▻ A ⇒ A) → □ (▻ A)
fix f {i} = f (▻fix f {i})
force (▻fix f {i}) j = fix f {j}
\end{code}

Now let us see all of this in action via a simple example.
Our goal is to compute the fixpoint of $f(x,y) = (1,x)$.

\begin{code}
const₁ : {N L P : SizedSet}
  → □(▻ N ⇒ P)
  → □(▻(L ⊗ N) ⇒ P)
const₁ f x = f (pure proj₂ ⊛ x)
\end{code}

Note that $f(x,y) = (1,x)$ is constant in the second coordinate.
We define it as follows.

\AgdaHide{
\begin{code}
private
\end{code}
}

\AgdaAlign{
\begin{code}
  solution : ℕ × ℕ
  solution =
\end{code}

\begin{code}
    let  f : □(▻(▻(c ℕ) ⊗ c ℕ)
             ⇒ ▻(c ℕ) ⊗ c ℕ)
         f = const₁ (λ x → x , 1)
\end{code}

\begin{code}
         fixpoint : □(▻(c ℕ) ⊗ c ℕ)
         fixpoint = fix f
\end{code}

\begin{code}
         (n , m) = fixpoint
    in   force n ∞ , m
\end{code}
}
