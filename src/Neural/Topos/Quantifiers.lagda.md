---
description: |
  Quantifiers along morphisms of presheaves: substitution, and its
  left and right adjoints on predicates, with the Beck–Chevalley-free
  adjunction laws the semantic-transfer machinery consumes.
---
<!--
```agda
open import Cat.Functor.Base
open import Cat.Diagram.Sieve
open import Cat.Prelude

import Neural.Topos.Predicates

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning
```
-->

```agda
module Neural.Topos.Quantifiers {ℓ} (C : Precategory ℓ ℓ) where
```

# Quantification along a map of presheaves {defines="predicate-quantifiers"}

The transfer of theories along the arrows of a network — the
$\exists_h \dashv h^\star \dashv \forall_h$ strings of
Belfiore–Bennequin's §2.2 — quantifies [[predicates|presheaf-predicate]]
along *morphisms of presheaves*, not merely along arrows of the base
site. This module provides substitution and both adjoints, pointwise
on the sieve semantics. The key device is the observation that a
predicate's sieve is determined by where it is *outright true*:
$f \in P(x)$ exactly when $P$ holds of the restriction $x \cdot f$
at the identity stage.

<!--
```agda
private
  module Cr = Cat.Reasoning C

open Neural.Topos.Predicates C
open Sieve
open _=>_

private variable
  X Y : Functor (C ^op) (Sets ℓ)
```
-->

```agda
holds : {X : Functor (C ^op) (Sets ℓ)} → Pred X → ∀ {U} → X ʻ U → Type
holds P {U} x = Cr.id {U} ∈ P .at x

member≃holds
  : {X : Functor (C ^op) (Sets ℓ)} (P : Pred X)
  → ∀ {U V} (f : Cr.Hom V U) (x : X ʻ U)
  → (f ∈ P .at x) ≃ holds P (Psh.₁ X f x)
member≃holds {X = X} P f x =
  prop-ext (hlevel 1) (hlevel 1)
    (λ m → subst (Cr.id ∈_) (sym (P .nat f x))
      (subst (_∈ P .at x) (sym (Cr.idr f)) m))
    (λ m → subst (_∈ P .at x) (Cr.idr f)
      (subst (Cr.id ∈_) (P .nat f x) m))
```

## Substitution

```agda
_^* : (h : X => Y) → Pred Y → Pred X
(h ^*) Q .at {U} x = Q .at (h .η U x)
(h ^*) Q .nat f x =
  ap (Q .at) (happly (h .is-natural _ _ f) x) ∙ Q .nat f (h .η _ x)
```

## The left adjoint

$\exists_h P$ holds of $y$ at a stage exactly when $y$'s restriction
there is *hit* by some element satisfying $P$ outright.

```agda
∃ᴾ : (h : X => Y) → Pred X → Pred Y
∃ᴾ {X = X} {Y = Y} h P .at {U} y .arrows {V} f = elΩ do
  Σ[ x ∈ X ʻ V ] ((h .η V x ≡ Psh.₁ Y f y) × holds P x)
∃ᴾ {X = X} {Y = Y} h P .at {U} y .closed {f = f} = rec! λ x heq hp g →
  inc
    ( Psh.₁ X g x
    , happly (h .is-natural _ _ g) x
      ∙ ap (Psh.₁ Y g) heq
      ∙ sym (Psh.F-∘ Y g f)
    , Equiv.to (member≃holds P g x)
        (subst (_∈ P .at x) (Cr.idl g) (P .at x .closed hp g)))
∃ᴾ {X = X} {Y = Y} h P .nat {U} {V} f y = ext λ {W} g → Ω-ua
  (rec! λ x heq hp → inc (x , heq ∙ sym (Psh.F-∘ Y g f) , hp))
  (rec! λ x heq hp → inc (x , heq ∙ Psh.F-∘ Y g f , hp))
```

## The right adjoint

$\forall_h P$ holds of $y$ at a stage when *every* element mapping
to *any further restriction* of $y$ satisfies $P$ outright.

```agda
∀ᴾ : (h : X => Y) → Pred X → Pred Y
∀ᴾ {X = X} {Y = Y} h P .at {U} y .arrows {V} f = elΩ
  (∀ {W} (g : Cr.Hom W V) (x : X ʻ W)
   → h .η W x ≡ Psh.₁ Y (f Cr.∘ g) y → holds P x)
∀ᴾ {X = X} {Y = Y} h P .at {U} y .closed {f = f} = rec! λ α g →
  inc λ g' x heq → α (g Cr.∘ g') x
    (heq ∙ ap (λ e → Psh.₁ Y e y) (sym (Cr.assoc f g g')))
∀ᴾ {X = X} {Y = Y} h P .nat {U} {V} f y = ext λ {W} g → Ω-ua
  (rec! λ α → inc λ g' x heq → α g' x (heq ∙ sym (cvt g g')))
  (rec! λ α → inc λ g' x heq → α g' x (heq ∙ cvt g g'))
  where
    cvt : ∀ {W W'} (g : Cr.Hom W V) (g' : Cr.Hom W' W)
        → Psh.₁ Y (g Cr.∘ g') (Psh.₁ Y f y)
        ≡ Psh.₁ Y ((f Cr.∘ g) Cr.∘ g') y
    cvt g g' = sym (Psh.F-∘ Y (g Cr.∘ g') f)
             ∙ ap (λ e → Psh.₁ Y e y) (Cr.assoc f g g')
```

## The adjunctions

```agda
∃ᴾ-adj-to
  : (h : X => Y) (P : Pred X) (Q : Pred Y)
  → ∃ᴾ h P ⊑ Q → P ⊑ (h ^*) Q
∃ᴾ-adj-to {X = X} h P Q α {U} x f m =
  α (h .η U x) f (inc
    ( Psh.₁ X f x
    , happly (h .is-natural _ _ f) x
    , Equiv.to (member≃holds P f x) m))

∃ᴾ-adj-from
  : (h : X => Y) (P : Pred X) (Q : Pred Y)
  → P ⊑ (h ^*) Q → ∃ᴾ h P ⊑ Q
∃ᴾ-adj-from {Y = Y} h P Q α {U} y f = rec! λ x heq hp →
  subst (_∈ Q .at y) (Cr.idr f) $
  subst (Cr.id ∈_) (Q .nat f y) $
  subst (λ e → Cr.id ∈ Q .at e) heq $
  α x Cr.id hp

∀ᴾ-adj-to
  : (h : X => Y) (P : Pred X) (Q : Pred Y)
  → (h ^*) Q ⊑ P → Q ⊑ ∀ᴾ h P
∀ᴾ-adj-to {X = X} {Y = Y} h P Q α {U} y f m = inc λ g x heq →
  α x Cr.id
    (subst (λ e → Cr.id ∈ Q .at e) (sym heq)
      (Equiv.to (member≃holds Q (f Cr.∘ g) y) (Q .at y .closed m g)))

∀ᴾ-adj-from
  : (h : X => Y) (P : Pred X) (Q : Pred Y)
  → Q ⊑ ∀ᴾ h P → (h ^*) Q ⊑ P
∀ᴾ-adj-from {X = X} {Y = Y} h P Q α {U} x f m =
  Equiv.from (member≃holds P f x) $
  □-out! (α (h .η U x) f m) Cr.id (Psh.₁ X f x)
    (happly (h .is-natural _ _ f) x
      ∙ ap (λ e → Psh.₁ Y e (h .η U x)) (sym (Cr.idr f)))
```
