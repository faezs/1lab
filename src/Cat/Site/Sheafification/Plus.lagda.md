<!--
```agda
open import Cat.Site.Sheafification
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Data.Set.Coequaliser

open Functor
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Plus
  {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) {ℓs}
  (A : Functor (C ^op) (Sets ℓs))
  where
```

<!--
```agda
open Precategory C
open Coverage J using (Membership-covers)
open Sheafification J A

private
  module A = Functor A
```
-->

# The separated quotient {defines="separated-quotient plus-construction"}

This module carries out the first half of the classical
*plus-construction*, in the form needed to characterise the unit of
the [[sheafification]]: the quotient of a presheaf by *saturated
local equality* is a [[separated presheaf|separated-presheaf]], and
the quotient is effective, so its path spaces are known.

The key design point, after which everything is straightforward: the
local-equality relation is a **proposition-valued higher inductive
type**, mirroring the architecture of the sheafification HIT itself.
The `locally`{.Agda} constructor takes *untruncated* families — as
`sep`{.Agda} does — and propositionality is imposed by a squash
constructor. Because every target we eliminate into is a
proposition, the coverage's merely-existing stability witnesses can
be used freely, and — unlike for its truncation-nested variants —
all recursions below are plainly structural.

```agda
data Loc-eq : {U : ⌞ C ⌟} (x y : A ʻ U) → Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓs) where
  here
    : ∀ {U} {x y : A ʻ U}
    → x ≡ y → Loc-eq x y
  locally
    : ∀ {U} {x y : A ʻ U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c → Loc-eq (A ⟪ f ⟫ x) (A ⟪ f ⟫ y))
    → Loc-eq x y
  squash
    : ∀ {U} {x y : A ʻ U}
    → is-prop (Loc-eq x y)
```

Restriction-stability is where the coverage's `stable`{.Agda} field
enters, and propositionality is why it may: the merely-existing
refining cover is eliminated into the proposition `Loc-eq`{.Agda}.

<!--
```agda
private
  unrestrict
    : ∀ {U V W} (g : Hom V U) (f : Hom W V) (x : A ʻ U)
    → A ⟪ f ⟫ (A ⟪ g ⟫ x) ≡ A ⟪ g ∘ f ⟫ x
  unrestrict g f x = sym (happly (A .F-∘ f g) x)
```
-->

```agda
restrict
  : ∀ {U V} (g : Hom V U) {x y : A ʻ U}
  → Loc-eq x y → Loc-eq (A ⟪ g ⟫ x) (A ⟪ g ⟫ y)
restrict g (here p) = here (ap (A.₁ g) p)
restrict {U} {V} g {x} {y} (locally c k) =
  ∥-∥-rec squash
    (λ (S , incl) → locally S λ {W} f hf →
      transport
        (λ i → Loc-eq (unrestrict g f x (~ i)) (unrestrict g f y (~ i)))
        (k (g ∘ f) (incl f hf)))
    (J .stable c g)
restrict g (squash a b i) = squash (restrict g a) (restrict g b) i
```

Reflexivity and symmetry are structural; **transitivity** — the
lemma that defeats both the merely-truncated and the
depth-stratified formulations of local equality — is structural
recursion on the first derivation, restricting the second along the
way.

```agda
loc-refl : ∀ {U} {x : A ʻ U} → Loc-eq x x
loc-refl = here refl

loc-sym : ∀ {U} {x y : A ʻ U} → Loc-eq x y → Loc-eq y x
loc-sym (here p) = here (sym p)
loc-sym (locally c k) = locally c λ f hf → loc-sym (k f hf)
loc-sym (squash a b i) = squash (loc-sym a) (loc-sym b) i

loc-trans
  : ∀ {U} {x y z : A ʻ U}
  → Loc-eq x y → Loc-eq y z → Loc-eq x z
loc-trans (here p) w = subst (λ e → Loc-eq e _) (sym p) w
loc-trans (locally c k) w = locally c λ f hf →
  loc-trans (k f hf) (restrict f w)
loc-trans (squash a b i) w =
  squash (loc-trans a w) (loc-trans b w) i
```

The two theorems of the
[`Locality`](Cat.Site.Sheafification.Locality.html) module hold for
this relation as well, by the same proofs: locally equal sections
have equal units, and every map into every sheaf identifies them.

```agda
loc-eq→inc-path
  : ∀ {U} {x y : A ʻ U}
  → Loc-eq x y → Path (Sheafify₀ U) (inc x) (inc y)

sheaf-detects-loc
  : (B : Functor (C ^op) (Sets ℓs)) (shf : is-sheaf J B) (φ : A => B)
  → ∀ {U} {x y : A ʻ U}
  → Loc-eq x y → φ .η U x ≡ φ .η U y
```

<!--
```agda
private
  inc-path
    : ∀ {V} {x y : A ʻ V} → x ≡ y
    → Path (Sheafify₀ V) (inc x) (inc y)
  inc-path = ap inc

loc-eq→inc-path (here p) = inc-path p
loc-eq→inc-path {x = x} {y} (locally c k) = sep c λ f hf →
    sym (inc-natural x)
  ∙ loc-eq→inc-path (k f hf)
  ∙ inc-natural y
loc-eq→inc-path (squash a b i) =
  squash _ _ (loc-eq→inc-path a) (loc-eq→inc-path b) i

sheaf-detects-loc B shf φ (here p) = ap (φ .η _) p
sheaf-detects-loc B shf φ {U} {x} {y} (locally c k) =
  shf .is-sheaf.separate c λ {V} f hf →
      sym (happly (φ .is-natural U V f) x)
    ∙ sheaf-detects-loc B shf φ (k f hf)
    ∙ happly (φ .is-natural U V f) y
sheaf-detects-loc B shf φ {U} (squash a b i) =
  B .F₀ U .is-tr _ _
    (sheaf-detects-loc B shf φ a) (sheaf-detects-loc B shf φ b) i
```
-->

## The quotient, effectively

Saturated local equality is a proposition-valued equivalence
relation, so it is a [[congruence|congruence]], and the quotient of
each set of sections is *effective*: paths in the quotient are
exactly local equalities of representatives.

```agda
Loc-congruence : ∀ U → Congruence (A ʻ U) _
Loc-congruence U .Congruence._∼_ = Loc-eq
Loc-congruence U .Congruence.has-is-prop x y = squash
Loc-congruence U .Congruence.reflᶜ = loc-refl
Loc-congruence U .Congruence._∙ᶜ_ = loc-trans
Loc-congruence U .Congruence.symᶜ = loc-sym
```

<!--
```agda
private
  module Cong (U : ⌞ C ⌟) = Congruence (Loc-congruence U)

  quot-path
    : ∀ {U} {x y : A ʻ U} → x ≡ y
    → Path (Cong.quotient U) (inc x) (inc y)
  quot-path = ap inc
```
-->

The quotient is again a presheaf — restriction descends, by
`restrict`{.Agda} — and we call it $A_1$: the **separated
reflection** candidate.

```agda
A₁ : Functor (C ^op) (Sets (o ⊔ ℓ ⊔ ℓc ⊔ ℓs))
A₁ .F₀ U = el (Cong.quotient U) squash
A₁ .F₁ g = Coeq-rec (λ x → inc (A ⟪ g ⟫ x))
  (λ (x , y , r) → quot (restrict g r))
A₁ .F-id {U} = funext $ Coeq-elim-prop (λ _ → squash _ _)
  λ x → quot-path (happly (A .F-id) x)
A₁ .F-∘ {U} f g = funext $ Coeq-elim-prop (λ _ → squash _ _)
  λ x → quot-path (happly (A .F-∘ f g) x)
```

And — the theorem this module exists for — $A_1$ **is separated**:
if two classes agree on a cover, effectivity turns the pointwise
agreements into local equalities of representatives, and the
`locally`{.Agda} constructor reassembles them into a local equality
at the top, which the quotient then collapses.

```agda
A₁-is-separated : is-separated J A₁
A₁-is-separated {U} c {x} {y} = go x y where
  go
    : (x y : Cong.quotient U)
    → (∀ {V} (f : Hom V U) (hf : f ∈ c)
       → A₁ ⟪ f ⟫ x ≡ A₁ ⟪ f ⟫ y)
    → x ≡ y
  go = Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → squash _ _)
    λ x → Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → squash _ _)
      λ y agree → quot
        (locally c λ f hf → Cong.effective _ (agree f hf))
```

## What this buys, and what is still missing

By `sheaf-detects-loc`{.Agda}, the unit's kernel would be exactly
`Loc-eq`{.Agda} if $A_1$ — or any presheaf receiving $A$ through its
quotient map — were a sheaf. The present module delivers the first
half of the classical route to such a sheaf: the separated quotient,
with known path spaces. The remaining half is the *gluing* step: for
a [[separated presheaf|separated-presheaf]] $B$, the presheaf of
patches modulo agreement-on-refinements is a sheaf receiving $B$
injectively. Its formalisation must confront choosing pullback
covers inside set-level (not proposition-level) constructions, where
the coverage's merely-existing stability witnesses can no longer be
eliminated freely; the standard remedies are elimination into sets
via two-constancy, or saturating the coverage first. This is now the
entire distance between `Sh[_,_]`{.Agda} and `Topos`{.Agda}.
