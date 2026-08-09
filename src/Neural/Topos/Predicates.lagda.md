---
description: |
  Ω-valued predicates on a presheaf: natural families of sieves, with
  the full intuitionistic propositional structure computed pointwise
  from the sieve-level connectives — the predicates on any presheaf
  form a Heyting algebra.
---
<!--
```agda
open import Cat.Functor.Base
open import Cat.Diagram.Sieve
open import Cat.Prelude

open import Data.Sum.Base

open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Heyting
open import Order.Base

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning

import Physics.SmoothWorld.Forcing as Forcing
```
-->

```agda
module Neural.Topos.Predicates {ℓ} (C : Precategory ℓ ℓ) where
```

# Predicates on a presheaf {defines="presheaf-predicate"}

The logical transport machinery of Belfiore–Bennequin's chapters 2–3
presumes, at every layer of a network, a Heyting algebra of
"propositions about" each object of the topos, with quantifiers along
maps. Upstream, the subobject lattice `Sub(X)` carries only finite
meets, and its Heyting structure is asserted in prose. Following the
roadmap's representation decision, we work instead with **Ω-valued
predicates**: a predicate on a presheaf $X$ assigns to every element
$x \in X(U)$ a sieve on $U$ — the stages at which the predicate
holds of $x$ — naturally in $U$. This is $\hom(X, \Omega)$ in
disguise, and every connective is computed pointwise from the
sieve-level intuitionistic connectives already machine-checked in
`Physics.SmoothWorld.Forcing`.

<!--
```agda
private
  module Cr = Cat.Reasoning C

open Forcing C public
open Sieve
```
-->

```agda
record Pred (X : Functor (C ^op) (Sets ℓ)) : Type (lsuc ℓ) where
  no-eta-equality
  private module X = Psh X
  field
    at  : ∀ {U} → X ʻ U → Sieve C U
    nat : ∀ {U V} (f : Cr.Hom V U) (x : X ʻ U)
        → at (X.₁ f x) ≡ pullback f (at x)

open Pred public
```

<!--
```agda
private variable
  X : Functor (C ^op) (Sets ℓ)

Pred-path
  : {P Q : Pred X}
  → (∀ {U} (x : X ʻ U) → P .at x ≡ Q .at x)
  → P ≡ Q
Pred-path {X = X} {P} {Q} p i .at x = p x i
Pred-path {X = X} {P} {Q} p i .nat f x =
  is-prop→pathp
    (λ i → Sieve-is-set (p (Psh.₁ X f x) i) (pullback f (p x i)))
    (P .nat f x) (Q .nat f x) i
  where
    Sieve-is-set : (S T : Sieve C _) → is-prop (S ≡ T)
    Sieve-is-set S T = hlevel 2 S T
```
-->

## The connectives

Pointwise truth, conjunction, implication, disjunction and falsity.
Naturality of each is the pullback-stability of the corresponding
sieve operation; stability of `⊤ᵢ`{.Agda} and `∧ᵢ`{.Agda} is
immediate, and for the implication it is the familiar shuffle of a
composite through the definition — the presheaf-topos fact that
implication, unlike in general categories, is stable under base
change.

```agda
private
  ⊥ᵢ : ∀ {c} → Sieve C c
  ⊥ᵢ .arrows _ = ⊥Ω
  ⊥ᵢ .closed p _ = p

  _∨ᵢ_ : ∀ {c} → Sieve C c → Sieve C c → Sieve C c
  (S ∨ᵢ T) .arrows f = S .arrows f ∨Ω T .arrows f
  (S ∨ᵢ T) .closed = rec! λ where
    (inl s) g → inc (inl (S .closed s g))
    (inr t) g → inc (inr (T .closed t g))

  pullback-⊤ : ∀ {u v} (f : Cr.Hom v u) → pullback f (⊤ᵢ {u}) ≡ ⊤ᵢ
  pullback-⊤ f = ext λ h → Ω-ua (λ _ → tt) (λ _ → tt)

  pullback-⊥ : ∀ {u v} (f : Cr.Hom v u) → pullback f (⊥ᵢ {u}) ≡ ⊥ᵢ
  pullback-⊥ f = ext λ h → Ω-ua (λ b → b) (λ b → b)

  pullback-∧
    : ∀ {u v} (f : Cr.Hom v u) (S T : Sieve C u)
    → pullback f (S ∧ᵢ T) ≡ pullback f S ∧ᵢ pullback f T
  pullback-∧ f S T = ext λ h → Ω-ua (λ p → p) (λ p → p)

  pullback-∨
    : ∀ {u v} (f : Cr.Hom v u) (S T : Sieve C u)
    → pullback f (S ∨ᵢ T) ≡ pullback f S ∨ᵢ pullback f T
  pullback-∨ f S T = ext λ h → Ω-ua (λ p → p) (λ p → p)

  pullback-⇒
    : ∀ {u v} (f : Cr.Hom v u) (S T : Sieve C u)
    → pullback f (S ⇒ᵢ T) ≡ (pullback f S ⇒ᵢ pullback f T)
  pullback-⇒ f S T = ext λ {w} h → Ω-ua
    (rec! λ α → inc λ g hs →
      subst (_∈ T) (sym (Cr.assoc f h g))
        (α g (subst (_∈ S) (Cr.assoc f h g) hs)))
    (rec! λ α → inc λ g hs →
      subst (_∈ T) (Cr.assoc f h g)
        (α g (subst (_∈ S) (sym (Cr.assoc f h g)) hs)))
```

```agda
⊤ᴾ : Pred X
⊤ᴾ .at _ = ⊤ᵢ
⊤ᴾ .nat f x = sym (pullback-⊤ f)

⊥ᴾ : Pred X
⊥ᴾ .at _ = ⊥ᵢ
⊥ᴾ .nat f x = sym (pullback-⊥ f)

_∧ᴾ_ : Pred X → Pred X → Pred X
(P ∧ᴾ Q) .at x = P .at x ∧ᵢ Q .at x
(P ∧ᴾ Q) .nat f x =
  ap₂ _∧ᵢ_ (P .nat f x) (Q .nat f x) ∙ sym (pullback-∧ f _ _)

_∨ᴾ_ : Pred X → Pred X → Pred X
(P ∨ᴾ Q) .at x = P .at x ∨ᵢ Q .at x
(P ∨ᴾ Q) .nat f x =
  ap₂ _∨ᵢ_ (P .nat f x) (Q .nat f x) ∙ sym (pullback-∨ f _ _)

_⇒ᴾ_ : Pred X → Pred X → Pred X
(P ⇒ᴾ Q) .at x = P .at x ⇒ᵢ Q .at x
(P ⇒ᴾ Q) .nat f x =
  ap₂ _⇒ᵢ_ (P .nat f x) (Q .nat f x) ∙ sym (pullback-⇒ f _ _)
```

## The Heyting algebra of predicates

Entailment is pointwise sieve inclusion, and the connectives above
make the predicates on any presheaf a [[Heyting algebra]] — the
structure the semantic-transfer machinery consumes. (Upstream, this
is the first Heyting structure on a topos-theoretic subobject-like
lattice; the poset of predicates is equivalent to `Sub(X)`, but we
never need that translation on the spine.)

```agda
_⊑_ : Pred X → Pred X → Type ℓ
_⊑_ {X = X} P Q = ∀ {U} (x : X ʻ U) → P .at x ⊆ Q .at x

Pred-poset : (X : Functor (C ^op) (Sets ℓ)) → Poset (lsuc ℓ) ℓ
Pred-poset X .Poset.Ob = Pred X
Pred-poset X .Poset._≤_ = _⊑_
Pred-poset X .Poset.≤-thin = hlevel 1
Pred-poset X .Poset.≤-refl x = λ _ m → m
Pred-poset X .Poset.≤-trans p q x = λ f m → q x f (p x f m)
Pred-poset X .Poset.≤-antisym p q = Pred-path λ x →
  ext λ f → Ω-ua (p x f) (q x f)

Pred-heyting : (X : Functor (C ^op) (Sets ℓ)) → is-heyting-algebra (Pred-poset X)
Pred-heyting X .is-heyting-algebra.has-top .Top.top = ⊤ᴾ
Pred-heyting X .is-heyting-algebra.has-top .Top.has-top P x f _ = tt
Pred-heyting X .is-heyting-algebra.has-bottom .Bottom.bot = ⊥ᴾ
Pred-heyting X .is-heyting-algebra.has-bottom .Bottom.has-bottom P x f b =
  absurd b
Pred-heyting X .is-heyting-algebra._∪_ = _∨ᴾ_
Pred-heyting X .is-heyting-algebra.∪-joins P Q .is-join.l≤join x f m =
  inc (inl m)
Pred-heyting X .is-heyting-algebra.∪-joins P Q .is-join.r≤join x f m =
  inc (inr m)
Pred-heyting X .is-heyting-algebra.∪-joins P Q .is-join.least R pl ql x f =
  rec! λ where
    (inl m) → pl x f m
    (inr m) → ql x f m
Pred-heyting X .is-heyting-algebra._∩_ = _∧ᴾ_
Pred-heyting X .is-heyting-algebra.∩-meets P Q .is-meet.meet≤l x f = fst
Pred-heyting X .is-heyting-algebra.∩-meets P Q .is-meet.meet≤r x f = snd
Pred-heyting X .is-heyting-algebra.∩-meets P Q .is-meet.greatest R pl ql x f m =
  pl x f m , ql x f m
Pred-heyting X .is-heyting-algebra._⇨_ = _⇒ᴾ_
Pred-heyting X .is-heyting-algebra.ƛ {x = P} {Q} {R} α x =
  ⇒ᵢ-curry (P .at x) (Q .at x) (R .at x) (α x)
Pred-heyting X .is-heyting-algebra.ev {x = P} {Q} {R} α x =
  ⇒ᵢ-uncurry (P .at x) (Q .at x) (R .at x) (α x)
```
