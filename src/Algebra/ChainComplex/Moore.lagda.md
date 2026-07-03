<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.ChainComplex
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Instances.Simplex
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Fin using (Fin ; fzero ; fsuc ; weaken ; _≤_)
open import Data.Nat using (0≤x)

open make-abelian-group
open Chain-complex
open Functor
```
-->

```agda
module Algebra.ChainComplex.Moore {ℓ} (A : Functor (Δ ^op) (Ab ℓ)) where
```

<!--
```agda
private
  module A = Functor A
  module G (n : Nat) = Abelian-group-on (A.₀ n .snd)
```
-->

# The Moore complex {defines="moore-complex normalized-chain-complex simplicial-abelian-group"}

A **simplicial abelian group** — a presheaf of abelian groups on the
[[simplex category]] — has an underlying [[chain complex]], its
**Moore complex** of *normalized chains*: in degree $n$ it consists
of the $n$-simplices all of whose faces vanish except possibly the
zeroth, and the boundary is that remaining face. This is the
complex through which the Dold–Kan correspondence identifies
simplicial abelian groups with chain complexes, and the reason the
paper's BRST complexes present *simplicial* — that is, higher
groupoidal — data.

The miracle of normalization is that $\partial \circ \partial = 0$
is a *single* [[simplicial identity]]: for a normalized simplex,
$d_0 d_0 = d_0 d_1$ by the identity $d_i d_j = d_{j-1} d_i$ ($i <
j$), and $d_1$ already vanishes. No alternating sums are needed.

First, the face maps and their exchange law, transported through the
functor $A$ from `δ-comm`{.Agda}.

```agda
private
  d : ∀ {n} (i : Fin (suc (suc n))) → ⌞ A.₀ (suc n) ⌟ → ⌞ A.₀ n ⌟
  d i = A.₁ (δ i) .∫Hom.fst

  d-hom : ∀ {n} (i : Fin (suc (suc n))) → is-group-hom
    (Abelian→Group-on (A.₀ (suc n) .snd))
    (Abelian→Group-on (A.₀ n .snd))
    (d i)
  d-hom i = A.₁ (δ i) .∫Hom.snd

  exchange
    : ∀ {n} (i j : Fin (suc (suc n))) → i ≤ j
    → (a : ⌞ A.₀ (suc (suc n)) ⌟)
    → d j (d (weaken i) a) ≡ d i (d (fsuc j) a)
  exchange i j le a = happly
    (ap ∫Hom.fst
      (  sym (A.F-∘ (δ j) (δ (weaken i)))
      ∙∙ ap A.₁ (δ-comm i j le)
      ∙∙ A.F-∘ (δ i) (δ (fsuc j))))
    a
```

An $n$-simplex is **normal** when all its faces except the zeroth
are the unit. Normality is a proposition, preserved by the group
operations because the faces are homomorphisms, so the normal chains
form a subgroup.

```agda
norm : ∀ n → ⌞ A.₀ n ⌟ → Type ℓ
norm zero    a = Lift ℓ ⊤
norm (suc n) a = ∀ (i : Fin (suc n)) → d (fsuc i) a ≡ G.1g n

norm-is-prop : ∀ n a → is-prop (norm n a)
norm-is-prop zero    a = hlevel 1
norm-is-prop (suc n) a = Π-is-hlevel 1 λ i → G.has-is-set n _ _

N : Nat → Abelian-group ℓ
N n = to-ab mk where
  mk : make-abelian-group (Σ ⌞ A.₀ n ⌟ (norm n))
  mk .ab-is-set = Σ-is-hlevel 2 (G.has-is-set n) λ a →
    is-prop→is-set (norm-is-prop n a)
  mk .1g = G.1g n , norm-unit n where
    norm-unit : ∀ n → norm n (G.1g n)
    norm-unit zero    = lift tt
    norm-unit (suc n) = λ i → is-group-hom.pres-id (d-hom (fsuc i))
  mk .mul (a , p) (b , q) = G._*_ n a b , norm-mul n a b p q where
    norm-mul : ∀ n a b → norm n a → norm n b → norm n (G._*_ n a b)
    norm-mul zero    a b p q = lift tt
    norm-mul (suc n) a b p q = λ i →
        d-hom (fsuc i) .is-group-hom.pres-⋆ a b
      ∙ ap₂ (G._*_ n) (p i) (q i)
      ∙ G.idl n
  mk .inv (a , p) = G._⁻¹ n a , norm-inv n a p where
    norm-inv : ∀ n a → norm n a → norm n (G._⁻¹ n a)
    norm-inv zero    a p = lift tt
    norm-inv (suc n) a p = λ i →
        is-group-hom.pres-inv (d-hom (fsuc i))
      ∙ ap (G._⁻¹ n) (p i)
      ∙ G.inv-unit n
  mk .idl (a , p) = Σ-prop-path (norm-is-prop n) (G.idl n)
  mk .assoc (a , p) (b , q) (c , r) =
    Σ-prop-path (norm-is-prop n) (G.associative n)
  mk .invl (a , p) = Σ-prop-path (norm-is-prop n) (G.inversel n)
  mk .comm (a , p) (b , q) = Σ-prop-path (norm-is-prop n) (G.commutes n)
```

The boundary is the zeroth face. It preserves normality by the
exchange law — pushing $d_0$ past a higher face turns it into a face
that already vanishes — and squares to zero by the same law applied
at the bottom index.

```agda
∂-norm : ∀ n (a : ⌞ A.₀ (suc n) ⌟) → norm (suc n) a → norm n (d fzero a)
∂-norm zero    a p = lift tt
∂-norm (suc n) a p = λ i →
    exchange fzero (fsuc i) 0≤x a
  ∙ ap (d fzero) (p (fsuc i))
  ∙ is-group-hom.pres-id (d-hom fzero)

Moore : Chain-complex ℓ
Moore .ob = N
Moore .∂ᶜ n .∫Hom.fst (a , p) = d fzero a , ∂-norm n a p
Moore .∂ᶜ n .∫Hom.snd .is-group-hom.pres-⋆ (a , p) (b , q) =
  Σ-prop-path (norm-is-prop n) (d-hom fzero .is-group-hom.pres-⋆ a b)
Moore .∂ᶜ-∂ᶜ n (a , p) = Σ-prop-path (norm-is-prop n)
  (  exchange fzero fzero 0≤x a
  ∙∙ ap (d fzero) (p fzero)
  ∙∙ is-group-hom.pres-id (d-hom fzero) )
```

The full Dold–Kan correspondence — that $N$ extends to an
*equivalence* between simplicial abelian groups and non-negatively
graded chain complexes — requires reassembling a simplicial group
from its normalized chains degeneracy by degeneracy, and remains
future work.
