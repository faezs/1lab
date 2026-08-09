<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group.Cat.Base

open import Cat.Displayed.Total
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Algebra.ChainComplex where
```

<!--
```agda
private variable
  ℓ : Level

private
  module AbC {ℓ} = Cat.Reasoning (Ab ℓ)
```
-->

# Chain complexes {defines="chain-complex chain-map"}

A **chain complex** (in non-negative degrees) is a sequence of
[[abelian groups]] connected by *boundary* homomorphisms, each of
which annihilates the image of the previous: the algebraic skeleton
of "boundaries of boundaries are empty", and the classical linear
container for homological information. In physics, complexes of
gauge fields, gauge transformations, and higher gauge transformations
appear as the infinitesimal (BRST) approximation to the higher
groupoids of gauge theory, and the Dold–Kan correspondence exchanges
them with simplicial abelian groups.

```agda
record Chain-complex (ℓ : Level) : Type (lsuc ℓ) where
  no-eta-equality
  field
    ob : Nat → Abelian-group ℓ
    ∂ᶜ : ∀ n → Ab ℓ .Precategory.Hom (ob (suc n)) (ob n)
    ∂ᶜ-∂ᶜ
      : ∀ n (x : ⌞ ob (suc (suc n)) ⌟)
      → ∂ᶜ n .∫Hom.fst (∂ᶜ (suc n) .∫Hom.fst x)
      ≡ Abelian-group-on.1g (ob n .snd)
```

A **chain map** is a degreewise homomorphism commuting with the
boundaries; chain complexes and chain maps form a precategory.

```agda
record Chain-map (A B : Chain-complex ℓ) : Type ℓ where
  no-eta-equality
  private
    module A = Chain-complex A
    module B = Chain-complex B
  field
    map : ∀ n → Ab _ .Precategory.Hom (A.ob n) (B.ob n)
    comm
      : ∀ n (x : ⌞ A.ob (suc n) ⌟)
      → map n .∫Hom.fst (A.∂ᶜ n .∫Hom.fst x)
      ≡ B.∂ᶜ n .∫Hom.fst (map (suc n) .∫Hom.fst x)
```

<!--
```agda
open Chain-map

private unquoteDecl eqv = declare-record-iso eqv (quote Chain-map)

Chain-map-path
  : ∀ {ℓ} {A B : Chain-complex ℓ} {f g : Chain-map A B}
  → (∀ n → f .map n ≡ g .map n)
  → f ≡ g
Chain-map-path {A = A} {B} {f} {g} p i .map n = p n i
Chain-map-path {A = A} {B} {f} {g} p i .comm n x =
  is-prop→pathp
    (λ i → B .Chain-complex.ob n .fst .is-tr
      (p n i .∫Hom.fst (A .Chain-complex.∂ᶜ n .∫Hom.fst x))
      (B .Chain-complex.∂ᶜ n .∫Hom.fst (p (suc n) i .∫Hom.fst x)))
    (f .comm n x) (g .comm n x) i

Chain-map-set : ∀ {ℓ} {A B : Chain-complex ℓ} → is-set (Chain-map A B)
Chain-map-set {A = A} {B} = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Π-is-hlevel 2 λ n → AbC.Hom-set _ _) λ f →
  Π-is-hlevel 2 λ n → Π-is-hlevel 2 λ x →
  is-prop→is-set (B .Chain-complex.ob n .fst .is-tr _ _)
```
-->

```agda
Ch : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Ch ℓ .Precategory.Ob = Chain-complex ℓ
Ch ℓ .Precategory.Hom = Chain-map
Ch ℓ .Precategory.Hom-set _ _ = Chain-map-set
Ch ℓ .Precategory.id {A} .map n = AbC.id
Ch ℓ .Precategory.id {A} .comm n x = refl
Ch ℓ .Precategory._∘_ {x} {y} {z} f g .map n =
  AbC._∘_ {x = x .Chain-complex.ob n} {y .Chain-complex.ob n}
    {z .Chain-complex.ob n} (f .map n) (g .map n)
Ch ℓ .Precategory._∘_ {x} {y} {z} f g .comm n a =
    ap (f .map n .∫Hom.fst) (g .comm n a)
  ∙ f .comm n (g .map (suc n) .∫Hom.fst a)
Ch ℓ .Precategory.idr f = Chain-map-path λ n → AbC.idr (f .map n)
Ch ℓ .Precategory.idl f = Chain-map-path λ n → AbC.idl (f .map n)
Ch ℓ .Precategory.assoc f g h =
  Chain-map-path λ n → AbC.assoc (f .map n) (g .map n) (h .map n)
```

The paper's (30) — probing a complex by the normalised chains of the
simplices to produce a Kan simplicial set, the Dold–Kan
correspondence — and its (31), the Eilenberg–MacLane spaces
$\mathbf{B}^n A$, are combinatorial constructions over this category
that remain future work.
