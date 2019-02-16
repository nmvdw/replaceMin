\AgdaHide{
\begin{code}
module SizedCombinators.SizedPredicates where

open import Preamble
open import SizedCombinators.SizedTypes
\end{code}
}

\begin{code}
SizedPredicate : SizedSet → Set₁
SizedPredicate A = {i : Size} → A i → Set
\end{code}

For sized predicates, we only need one combinator, which represents universal quantification.
We define it pointwise using the dependent product of types.

\begin{code}
all : (A : SizedSet) → SizedPredicate A → SizedSet
all A B i = (x : A i) → B x

syntax all A (λ x → B) = ∏[ x ∈ A ] B
\end{code}

If we want to prove an equation involving \AFi{force}, we need to give it all required arguments.
One of those arguments, is a size smaller than \AB{i}.
For this reason, we define the following sized type.

\begin{code}
Size<Set : SizedSet
Size<Set i = Size< i
\end{code}
