---
description: |
  First-order Heyting hyperdoctrines: fibred Heyting algebras with
  logical substitution and both quantifier adjoints, and the model
  in Ω-valued predicates over any presheaf category.
---
<!--
```agda
open import Cat.Functor.Base
open import Cat.Prelude

open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Heyting
open import Order.Base

open import Neural.Order.Adjunction

import Neural.Topos.Quantifiers
import Neural.Topos.Predicates
```
-->

```agda
module Neural.Logic.Hyperdoctrine where
```

# Heyting hyperdoctrines {defines="heyting-hyperdoctrine"}

The library's `Regular-hyperdoctrine`{.Agda} stops at the regular
fragment — finite meets and the existential. The logical-transport
machinery of Belfiore–Bennequin needs the *full* first-order
intuitionistic signature: fibred [[Heyting algebras]], substitution
that is a **logical** morphism (the paper's silently-used hypotheses,
made explicit fields), and *both* adjoints to substitution. Following
the project's interface discipline, the record ships with its
inhabitant: the Ω-valued [[predicates|presheaf-predicate]] over any
presheaf category.

Beck–Chevalley conditions are deliberately not part of the record:
the chapters consume them only for specific squares, and they will be
stated as separate properties where they earn their keep.

```agda
record Heyting-hyperdoctrine
  {o ℓ} (B : Precategory o ℓ) (o' ℓ' : Level)
  : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  no-eta-equality
  open Precategory B

  field
    ℙ           : Ob → Poset o' ℓ'
    has-heyting : ∀ X → is-heyting-algebra (ℙ X)
    sub         : ∀ {X Y} → Hom X Y → Monotone (ℙ Y) (ℙ X)

  private module H {X : Ob} = is-heyting-algebra (has-heyting X)

  field
    sub-id : ∀ {X} {P : ⌞ ℙ X ⌟} → sub id · P ≡ P
    sub-∘
      : ∀ {X Y Z} {f : Hom Y Z} {g : Hom X Y} {P : ⌞ ℙ Z ⌟}
      → sub (f ∘ g) · P ≡ sub g · (sub f · P)

    sub-⊤
      : ∀ {X Y} {f : Hom X Y}
      → sub f · Top.top (H.has-top) ≡ Top.top (H.has-top)
    sub-⊥
      : ∀ {X Y} {f : Hom X Y}
      → sub f · Bottom.bot (H.has-bottom) ≡ Bottom.bot (H.has-bottom)
    sub-∧
      : ∀ {X Y} {f : Hom X Y} {P Q : ⌞ ℙ Y ⌟}
      → sub f · (P H.∩ Q) ≡ (sub f · P) H.∩ (sub f · Q)
    sub-∨
      : ∀ {X Y} {f : Hom X Y} {P Q : ⌞ ℙ Y ⌟}
      → sub f · (P H.∪ Q) ≡ (sub f · P) H.∪ (sub f · Q)
    sub-⇒
      : ∀ {X Y} {f : Hom X Y} {P Q : ⌞ ℙ Y ⌟}
      → sub f · (P H.⇨ Q) ≡ (sub f · P) H.⇨ (sub f · Q)

    exists : ∀ {X Y} (f : Hom X Y) → Monotone (ℙ X) (ℙ Y)
    forAll : ∀ {X Y} (f : Hom X Y) → Monotone (ℙ X) (ℙ Y)

    exists⊣sub : ∀ {X Y} (f : Hom X Y) → exists f ⊣ₚ sub f
    sub⊣forAll : ∀ {X Y} (f : Hom X Y) → sub f ⊣ₚ forAll f
```

## The predicate model

Over any (small) presheaf category, the Ω-valued predicates fibred
by substitution-as-precomposition satisfy every axiom — the
connectives are pointwise, so the logical-morphism equations hold on
the nose, and the quantifier adjunctions are the ones already
established.

<!--
```agda
module _ {ℓ} (C : Precategory ℓ ℓ) where
  open Neural.Topos.Quantifiers C
  open Neural.Topos.Predicates C
  open Heyting-hyperdoctrine
  open _=>_

  private
    sub-monotone
      : {X Y : Functor (C ^op) (Sets ℓ)} (h : X => Y)
      → Monotone (Pred-poset Y) (Pred-poset X)
    sub-monotone h .hom = h ^*
    sub-monotone h .pres-≤ α x f m = α (h .η _ x) f m

    ∃ᴾ-monotone
      : {X Y : Functor (C ^op) (Sets ℓ)} (h : X => Y)
      → Monotone (Pred-poset X) (Pred-poset Y)
    ∃ᴾ-monotone h .hom = ∃ᴾ h
    ∃ᴾ-monotone h .pres-≤ {P} {P'} α y f = rec! λ x heq hp →
      inc (x , heq , α x _ hp)

    ∀ᴾ-monotone
      : {X Y : Functor (C ^op) (Sets ℓ)} (h : X => Y)
      → Monotone (Pred-poset X) (Pred-poset Y)
    ∀ᴾ-monotone h .hom = ∀ᴾ h
    ∀ᴾ-monotone h .pres-≤ {P} {P'} α y f = rec! λ β →
      inc λ g x heq → α x _ (β g x heq)
```
-->

```agda
  Pred-hyperdoctrine : Heyting-hyperdoctrine (PSh ℓ C) (lsuc ℓ) ℓ
  Pred-hyperdoctrine .ℙ = Pred-poset
  Pred-hyperdoctrine .has-heyting = Pred-heyting
  Pred-hyperdoctrine .sub = sub-monotone
  Pred-hyperdoctrine .sub-id = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-∘ = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-⊤ = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-⊥ = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-∧ = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-∨ = Pred-path λ _ → refl
  Pred-hyperdoctrine .sub-⇒ = Pred-path λ _ → refl
  Pred-hyperdoctrine .exists = ∃ᴾ-monotone
  Pred-hyperdoctrine .forAll = ∀ᴾ-monotone
  Pred-hyperdoctrine .exists⊣sub h .unit {P} =
    ∃ᴾ-adj-to h P (∃ᴾ h P) λ _ _ m → m
  Pred-hyperdoctrine .exists⊣sub h .counit {Q} =
    ∃ᴾ-adj-from h ((h ^*) Q) Q λ _ _ m → m
  Pred-hyperdoctrine .sub⊣forAll h .unit {Q} =
    ∀ᴾ-adj-to h ((h ^*) Q) Q λ _ _ m → m
  Pred-hyperdoctrine .sub⊣forAll h .counit {P} =
    ∀ᴾ-adj-from h P (∀ᴾ h P) λ _ _ m → m
```

The syntactic layer — a formula grammar with the full signature and
a soundness theorem into any Heyting hyperdoctrine, extending
`Cat.Displayed.Doctrine.Logic` beyond the regular fragment — is the
successor milestone; the paper's chapters 2–3 consume the *semantic*
structure above.
