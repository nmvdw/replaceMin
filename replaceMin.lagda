\AgdaHide{
\begin{code}
module replaceMin where

open import Size
open import Data.Nat renaming (zero to ℕzero; suc to ℕsuc; _⊔_ to max)
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixl 30 _⊛_
infixr 30 _⇒_
infixr 40 _⊕_
infixr 50 _⊗_
\end{code}
}

\section{Programming with Sized Types}
Our goal is to define a function \AF{fix}, which gives general recursion, and a data type \AF{⊳} representing delayed computations.
Since lazy evaluation is about delaying computations and forcing them when needed, the type \AF{⊳} can be used to evaluate arguments lazily.
To guarantee everything remains productive, we need broader termination checks and that is where \emph{sized types} come into play \cite{abel2004}.

\subsection{Sized Types}
Instead of just structural recursion, this allows general recursion and lazy evaluation.
The main idea is that types are annotated with a size, which, intuitively, is an ordinal number.
To check the termination of a not necessarily structural-recursive function, the sizes must decrease in every call.

More concretely, there is a type \AF{Size} and \emph{sized type} is a type indexed by \AF{Size}.

\begin{code}
SizedSet = Size → Set
\end{code}

On these sets, we need several operations.
Some of them, like exponentials, sums, products, and constant families, are defined pointwise.

\begin{code}
_⇒_ : SizedSet → SizedSet → SizedSet
A ⇒ B = λ i → A i → B i

_⊕_ : SizedSet → SizedSet → SizedSet
A ⊕ B = λ i → A i ⊎ B i

_⊗_ : SizedSet → SizedSet → SizedSet
A ⊗ B = λ i → A i × B i

c : Set → SizedSet
c A = λ _ → A
\end{code}

A less intuitive operation, realizes sized types as actual types.
Suppose, we have some sized type \AB{A} and let us call its realization \AF{\&} \AB{A}.
Then inhabitants of \AB{A} are the same as functions assining to each size \AB{i} an element of \AB{A i}.
Hence, \AF{\&} \AB{A} is just a type of dependent functions.

\begin{code}
& : SizedSet → Set
& A = {i : Size} → A i
\end{code}

\subsection{Delayed Computations}
The main ingredient in the machinery is a data type representing delayed computations.
Lazy evaluation requires delaying calculations as some must only be done when they are forced.
For example, elements in a lazy list are only computed when they are needed by some other function.

Since Agda is a total language, everything should remain productive and this is where sizes come into play.
Productivity is guaranteed if the sizes decrease in each recursive call.
Concretely, this means that whenever we have some delayed computation of size \AB{i}, we can only force it with a size smaller than \AB{i}.

The type \AF{Size<} \AB{i} represents those sizes smaller than \AB{i}.
Now we can define a sized type \AF{⊳} \AB{A} as follows.

\begin{code}
record ⊳ (A : SizedSet) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → A j
open ⊳ public
\end{code}

Note that this is a coinductive record meaning that we can use \emph{copatterns} to define values \cite{abel2013copatterns}.
Instead of saying how elements are constructed, it says how elements are destructed or, intuitively, how to make observations on elements.
Taking this point of view, we can say that the function \AFi{force} makes an observation on a delayed computation.

To get a feeling how this all works, we look at the lazy natural numbers.
This also explains why this mechanism allows lazy evaluation.
We define the lazy natural numbers similar to the usual natural numbers, but the argument of the successor is delayed.

\begin{code}
data LNat (i : Size) : Set where
  LZ : LNat i
  LS : ⊳ LNat i → LNat i
\end{code}

A simple function we can define with these, computes the number infinity.
On \AF{ℕ}, the natural numbers defined inductively, we cannot define that, because it is not structurally recursive.
The calculation does not terminate.
However, if we evaluate the argument of the successor lazily, then this is no problem.

We define infinity with mutual recursion.
The first function computes infinity as a lazy natural number and the second gives a delayed version of it.

\begin{code}
infinity : & LNat
⊳infinity : &(⊳ LNat)
\end{code}

For \AF{infinity}, we repeatedly need to apply \AIC{LS}.
However, its argument is delayed, so we use \AF{⊳infinity} for it.
We define \AF{⊳infinity} with copatterns meaning that we only need to give the value of \AFi{force} \AF{⊳infinity}.

\begin{code}
infinity {i} = LS (⊳infinity {i})
force (⊳infinity {i}) {j} = infinity {j}
\end{code}

Note that the sizes in each call decrease since \AB{j} has type \AF{Size<} \AB{i}.
It is actually unnecessary to write down all the sizes since Agda can determine them itself.

This type actually corresponds with the natural numbers in Haskell, because Haskell evaluates lazily.
Due to lazy evaluation, 

In the remainder, we shall need that \AF{⊳} is an applicative functor \cite{mcbride2008applicative}.
This means we need to define functions \AF{pure} and \AF{\_⊛\_}.
Both are defined using copatterns.

\begin{code}
pure : {A : SizedSet} → & A → &(⊳ A)
force (pure x) = x

_⊛_ : {A : SizedSet} {B : SizedSet} → &(⊳(A ⇒ B) ⇒ ⊳ A ⇒ ⊳ B)
force (f ⊛ x) = force f (force x)
\end{code}

Now that we got lazy evaluation, we can move our attention to general recursion.
For that we use an operation, called \AF{fix}, which gives the fixpoint of maps between sized types.
It is computed by repeatedly applying the given function.
To guarantee that the sizes decrease in every call, only functions of type \AF{\&}(\AF{⊳} \AB{A} \AF{⇒} \AB{A}) are accepted.
Concretely, this means that the function must evaluate its argument lazily.
We define \AF{fix} in a similar fashion to \AF{repeat}.

\begin{code}
fix : {A : SizedSet} → &(⊳ A ⇒ A) → & A
⊳fix : {A : SizedSet} → &(⊳ A ⇒ A) → & (⊳ A)
fix f {i} = f {i} (⊳fix f {i})
force (⊳fix f {i}) {j} = fix f {j}

infinity-alt : & LNat
infinity-alt = fix LS
\end{code}

Again we write down the sizes explicitly, even though it is not necessary, to make clear this function is productive.

\section{Eliminating Traversals}
\subsection{The Setting}
With all the theory in place, we can give the required data types and basic functions.
The values in the leafs all are natural numbers and we shall need a sized type of natural numbers.
This is the same one as \AF{CNat}, but now we define it in a more concise way.
Beside that, we need the minimum of numbers.

\begin{code}
SizedNat : SizedSet
SizedNat = c ℕ

min : &(SizedNat ⇒ SizedNat ⇒ SizedNat)
min n m = n ⊓ m
\end{code}

Next we define a sized type of trees where the leafs are labelled with sized natural numbers.
As usual, we have two constructors: \AIC{Leaf} and \AIC{Node}.
We let both constructors preserve the size.

\begin{code}
data Tree (i : Size) : Set where -- this way we can access the recursion principle via patter matching
  Leaf : SizedNat i → Tree i
  Node : Tree i → Tree i → Tree i
\end{code}

In the examples \AF{repeat} and \AF{fix} we discussed before, the definition required two steps.
We needed an actual version, \AF{repeat} and \AF{fix}, and a delayed version, \AF{⊳repeat} and \AF{⊳fix}.
For \AF{Leaf} and \AF{Node} we also need a delayed version.
We define them using copatterns and the applicative structure of \AF{⊳}.

\begin{code}
⊳Leaf : &(⊳ SizedNat ⇒ ⊳ Tree)
force (⊳Leaf n) = Leaf (force n)

⊳Node : &(⊳ Tree ⇒ ⊳ Tree ⇒ ⊳ Tree)
⊳Node t₁ t₂ = pure Node ⊛ t₁ ⊛ t₂
\end{code}

\subsection{The Algorithm}
Now we translate the Haskell program given in the introduction to Agda.
Note that in the third line of the original program, we compute a fixpoint of the function \AB{rmb t}.
So, to describe the algorithm, we first need to say how to compute that fixpoint.
For that, we use the function \AF{feedback}.

\begin{code}
fb-h : {T N : SizedSet} → &(⊳ N ⇒ T ⊗ N) → &(⊳(T ⊗ N) ⇒ T ⊗ N)
fb-h f x = f (pure proj₂ ⊛ x)

feedback : {T N : SizedSet} → &(⊳ N ⇒ T ⊗ N) → & T
feedback f = proj₁ (fix (fb-h f))
\end{code}

Now we want to define the help function \AF{rmb}, which will be the argument for \AF{feedback}.
We take \AF{⊳ Tree} for \AB{B} and \AF{SizedNat} for \AB{U}.
Note that we must use \AF{⊳ Tree}, because otherwise we would not be able to apply \AIC{Node} or \AF{⊳Node}.

\begin{code}
rmb : &(Tree ⇒ ⊳ SizedNat ⇒ (⊳ Tree) ⊗ SizedNat)
rmb (Leaf x) n = (⊳Leaf n , x)
rmb (Node l r) n =
  let (l' , ml) = rmb l n
      (r' , mr) = rmb r n
  in (⊳Node l' r' , min ml mr)

replaceMin : &(Tree ⇒ Tree)
replaceMin t = force (feedback (rmb t))
\end{code}

Since \AF{feedback} (\AF{rmb} \AB{t}) has the type \AF{⊳ Tree}, we must apply \AFi{force}.

\section{Proving with Sized Types}
Our next goal is to prove functional correctness of \AF{replaceMin}.
To formulate the specification, we need predicates and relations on sized types, universal quantification, and equality types

A predicate on \AB{A} is a function giving a type for each \AB{a} : \AB{A}.
A relation between \AB{A} and \AB{B} is a function giving a type for each \AB{a} : \AB{A} and \AB{b} : \AB{B}.
To make it sized, we let it depend on sizes.

\begin{code}
SizedPredicate : SizedSet → Set₁
SizedPredicate A = {i : Size} → A i → Set

SizedRelation : SizedSet → SizedSet → Set₁
SizedRelation A B = {i : Size} → A i → B i → Set
\end{code}

Next we define universal quantification and for that we use dependent products.
Given a sized type \AB{A} and a predicate on \AB{A}, we get another sized type.

\begin{code}
∏ : (A : SizedSet) → SizedPredicate A → SizedSet
∏ A B i = (x : A i) → B x
\end{code}

Furthermore, for each sized type \AB{A}, we have a relation on \AB{A} representing equality.
For this we use propositional equality in Agda.

\begin{code}
eq : (A : SizedSet) → SizedRelation A A
eq A x y = x ≡ y
\end{code}

Note that for \AF{∏} and \AF{eq} we use the Agda implementations of the dependent product and equality respectively.
This means that we can use all previously defined functions for them and in paticular, we can use Agda's usual notation for equational reasoning.

The last relation we need, might seem a bit unexpected.
It is another equality type, but for delayed computations.
Rather than saying that elements are propositionally equal, it says that all observations on them are equal.
More specifically, if applying \AFi{force} on them gives the same result, then they are equal.

When using this predicate, the elements might use \AFi{force} meaning that they depend on some size.
Hence, we first define a sized set which for every size \AB{i} gives the sizes smaller than \AB{i}.

\begin{code}
_~_ : {A : SizedSet} → &(⊳ A) → &(⊳ A) → Set
x ~ y = {i : Size} {j : Size< i} → force x {j} ≡ force y

pure-force : {A : SizedSet} → (x : &(⊳ A)) → pure (force x) ~ x 
pure-force x = refl

force-pure : {A : SizedSet} → (x : & A) → force (pure x) ≡ x 
force-pure x = refl

identity : {A : SizedSet} (x : &(⊳ A)) → pure (λ z → z) ⊛ x ~ x
identity x = refl

composition : {A B C : SizedSet}
              (g : &(⊳(B ⇒ C))) (f : &(⊳(A ⇒ B)))
              (x : &(⊳ A))
              → pure (λ h₁ h₂ z → h₁(h₂ z)) ⊛ g ⊛ f ⊛ x ~ g ⊛ (f ⊛ x)
composition g f x = refl

homomorphism : {A B : SizedSet} (f : &(A ⇒ B)) (x : & A) → pure f ⊛ pure x ~ pure (f x)
homomorphism f x = refl

interchange : {A B : SizedSet} (f : &(⊳(A ⇒ B))) (x : & A) → f ⊛ (pure x) ~ pure (λ z → z x) ⊛ f
interchange f x = refl

Size<Set : SizedSet
Size<Set i = Size< i

⊳eq : (A : SizedSet) → SizedRelation (Size<Set ⇒ ⊳ A) (Size<Set ⇒ ⊳ A)
⊳eq A {i} x y = {j : Size< i} → force (x j) {j} ≡ force (y j)
\end{code}

\section{Correctness}
To write down the specification we first give the inefficient implementation of the algorithm.
The specification says they are equal on every input.
We need two help functions, which are the first and second projection of \AF{rmb}.

The first function, which replace all values in a tree by some other value, might seem not straightforward.
One could define it without any delayed computation, but actually the value by which we replace everything, is delayed.
This also means that the resulting tree is delayed as well.
The reason for this, is that the number given to \AF{rmb} is delayed.

\begin{code}
replace : &(Tree ⇒ ⊳ SizedNat ⇒ ⊳ Tree)
replace (Leaf x) n = ⊳Leaf n
replace (Node l r) n = ⊳Node (replace l n) (replace r n)
\end{code}

The second function, which takes the minimum of a tree, is straightforward.

\begin{code}
min-tree : &(Tree ⇒ SizedNat)
min-tree (Leaf x) = x
min-tree (Node l r) = min (min-tree l) (min-tree r)
\end{code}

All in all, we get the following inefficient implementation and specification.

\begin{code}
replaceMin-spec : &(Tree ⇒ Tree)
replaceMin-spec t = force (replace t (pure (min-tree t)))

valid : &(Tree ⇒ Tree) → Set
valid f = &(∏ Tree (λ t → eq Tree (f t) (replaceMin-spec t)))
\end{code}

In the remainder of this section, we prove that \AF{replaceMin} satisfies the specification.
We do this in three steps.
First, we compute the first and second projection of \AF{rmb}.
These are given by \AF{replace} and \AF{min-tree} respectively.
Second, we prove a lemma \AF{replace}.
Briefly, it says we can always make the second argument, of type \AF{⊳ SizedNat}, of the form \AF{pure} \AB{x}.
Third, we put it all together to prove the correctness theorem.
\AgdaAlign{
\begin{code}
rmb₁ : &(∏ Tree (λ t →
         &(∏ (⊳ SizedNat) (λ n →
           eq (⊳ Tree) (proj₁ (rmb t n)) (replace t n)))))
rmb₁ (Leaf x) n = refl
rmb₁ (Node l r) n =
  begin
    proj₁ (rmb (Node l r) n)
\end{code}
\quad \AF{≡⟨} unfold \AF{rmb} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold rmb
\end{code}
  }
\begin{code}
    ⊳Node (proj₁ (rmb l n)) (proj₁ (rmb r n))
\end{code}
\quad \AF{≡⟨} induction hypothesis, \AF{rmb₁} \AB{l} \AB{n} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ cong (λ x → ⊳Node x (proj₁ (rmb r n))) (rmb₁ l n) ⟩
\end{code}}
\begin{code}
    ⊳Node (replace l n) (proj₁ (rmb r n))
\end{code}
\quad \AF{≡⟨} induction hypothesis, \AF{rmb₁} \AB{r} \AB{n} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ cong (⊳Node (replace l n)) (rmb₁ r n) ⟩
\end{code}}
\begin{code}
    ⊳Node (replace l n) (replace r n)
\end{code}
\quad \AF{≡⟨} fold \AF{replace} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold replace
\end{code}}
\begin{code}
    replace (Node l r) n
  ∎
\end{code}
}
\AgdaAlign{
\begin{code}
rmb₂ : &(∏ Tree (λ t →
         &(∏ (⊳ SizedNat) (λ n →
           eq SizedNat (proj₂ (rmb t n)) (min-tree t))))
        )
rmb₂ (Leaf x) n = refl
rmb₂ (Node l r) n =
  begin
    proj₂ (rmb (Node l r) n)
\end{code}
\quad \AF{≡⟨} unfold \AF{rmb} \AF{⟩} 
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold rmb
\end{code}}
\begin{code}
    min (proj₂ (rmb l n)) (proj₂ (rmb r n))
\end{code}
\quad \AF{≡⟨} induction hypothesis, \AF{rmb₂} \AB{r} \AB{n} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ cong (min (proj₂ (rmb l n))) (rmb₂ r n) ⟩
\end{code}}
\begin{code}
    min (proj₂ (rmb l n)) (min-tree r)
\end{code}
\quad \AF{≡⟨} induction hypothesis, \AF{rmb₂} \AB{l} \AB{n} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ cong (λ x → min x (min-tree r)) (rmb₂ l n) ⟩
\end{code}}
\begin{code}
    min (min-tree l) (min-tree r)
  ∎
\end{code}
}

For the correctness theorem, we need one lemma which gives the value of \AFi{force} (\AF{replace} t n).

\begin{code}
replace< : &(Tree ⇒ ⊳ SizedNat ⇒ Size<Set ⇒ ⊳ Tree)
replace< t n _ = replace t n

replace-pure : &(Tree ⇒ ⊳ SizedNat ⇒ Size<Set ⇒ ⊳ Tree)
replace-pure t n j = replace t (pure (force n))
\end{code}

\AgdaAlign{
\begin{code}
⊳replace : &(∏ Tree (λ t →
             &(∏ (⊳ SizedNat) (λ n →
               ⊳eq Tree (replace< t n) (replace-pure t n))))
            )
⊳replace (Leaf x) n = refl
⊳replace (Node l r) n =
  begin
    force (replace (Node l r) n)
  ≡⟨ refl ⟩
    force (⊳Node (replace l n) (replace r n))
  ≡⟨ refl ⟩
    force (pure Node ⊛ (replace l n) ⊛ (replace r n))
  ≡⟨ refl ⟩
    force (pure Node) (force (replace l n)) (force (replace r n))
  ≡⟨ cong (λ z → force (pure Node) z (force (replace r n))) (⊳replace l n) ⟩
    force (pure Node) (force (replace l (pure (force n)))) (force (replace r n))
  ≡⟨ cong (λ z → force (pure Node) (force (replace l (pure (force n)))) z) (⊳replace r n) ⟩
    force (replace (Node l r) (pure (force n)))
  ∎
\end{code}}

\AgdaAlign{
\begin{code}
rm-correct : valid replaceMin
rm-correct t =
  begin
    replaceMin t
\end{code}
\quad \AF{≡⟨} unfold \AF{replaceMin}, \AF{feedback} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold replaceMin, feedback
\end{code}}
\begin{code}
    force (proj₁ (fix (λ x → rmb t (pure proj₂ ⊛ x))))
\end{code}
\quad \AF{≡⟨} unfold \AF{fix} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold fix
\end{code}}
\begin{code}
    force (proj₁ (rmb t (pure proj₂ ⊛ ⊳fix (fb-h (rmb t)))))
\end{code}
\quad \AF{≡⟨} rewrite \AF{rmb₁} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ cong (λ x → force x)
          (rmb₁ t ((pure proj₂ ⊛ ⊳fix (fb-h (rmb t))))) ⟩
\end{code}}
\begin{code}
    force (replace t (pure proj₂ ⊛ ⊳fix (fb-h (rmb t))))
\end{code}
\quad \AF{≡⟨} rewrite \AF{⊳replace} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ ⊳replace t (pure proj₂ ⊛ ⊳fix (fb-h (rmb t))) ⟩
\end{code}}
\begin{code}
    force (replace t (pure (force (pure proj₂ ⊛ ⊳fix (fb-h (rmb t))))))
\end{code}
\quad \AF{≡⟨} unfold \AF{pure} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold pure
\end{code}}
\begin{code}
    force (replace t (pure (proj₂ (fix (fb-h (rmb t))))))
\end{code}
\quad \AF{≡⟨} unfold \AF{fix} \AF{⟩}
\AgdaHide{
\begin{code}
  ≡⟨ refl ⟩ -- unfold fix
\end{code}}
\begin{code}
    force (replace t (pure (proj₂ (rmb t ((pure proj₂ ⊛ ⊳fix (fb-h (rmb t))))))))
\end{code}
\quad \AF{≡⟨} rewrite \AF{rmb₂} \AF{⟩}}
\AgdaHide{
\begin{code}
  ≡⟨ cong (λ x → force (replace t (pure x)))
          (rmb₂ t ((pure proj₂ ⊛ ⊳fix (fb-h (rmb t))))) ⟩
\end{code}}
\begin{code}
    force (replace t (pure (min-tree t)))
  ∎
\end{code}
}


