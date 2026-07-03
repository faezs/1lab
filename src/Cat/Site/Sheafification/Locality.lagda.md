<!--
```agda
open import Cat.Site.Sheafification
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open Functor
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Locality
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

# Local equality and the unit of sheafification {defines="locally-equal-sections"}

When are two sections of a presheaf identified by the unit of its
[[sheafification]]? Classically the answer is: exactly when they are
*locally* equal — equal after restriction along some cover — but for
a mere [[coverage]], where covers need not compose, the correct
notion must be *saturated*: local equality is the least relation
containing equality and closed under being checked cover-by-cover.
We define it inductively. (For the eventual quotient construction
the recursive occurrence should additionally be truncated, so that
the coverage's *merely-existing* stability witnesses can restrict
derivations without choice; the two theorems below do not need
this, and we keep the relation proof-relevant here.)

```agda
data Locally-equal : {U : ⌞ C ⌟} (x y : A ʻ U) → Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓs) where
  here
    : ∀ {U} {x y : A ʻ U}
    → x ≡ y → Locally-equal x y
  local
    : ∀ {U} {x y : A ʻ U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c
       → Locally-equal (A ⟪ f ⟫ x) (A ⟪ f ⟫ y))
    → Locally-equal x y
```

<!--
```agda
loc-refl : ∀ {U} {x : A ʻ U} → Locally-equal x x
loc-refl = here refl

loc-sym : ∀ {U} {x y : A ʻ U} → Locally-equal x y → Locally-equal y x
loc-sym (here p) = here (sym p)
loc-sym (local c k) = local c λ f hf → loc-sym (k f hf)
```
-->

## Locally equal sections have equal units

The first half of the path-space characterisation of the
sheafification, over an arbitrary coverage: locally equal sections
are identified by the unit. The `here`{.Agda} constructor is
functoriality of the inclusion; the `local`{.Agda} constructor is
*exactly* the separation constructor of the higher inductive type,
mediated by naturality of the inclusion.

<!--
```agda
private
  inc-path
    : ∀ {V} {x y : A ʻ V} → x ≡ y
    → Path (Sheafify₀ V) (inc x) (inc y)
  inc-path = ap inc
```
-->

```agda
locally-equal→inc-path
  : ∀ {U} {x y : A ʻ U}
  → Locally-equal x y
  → Path (Sheafify₀ U) (inc x) (inc y)
locally-equal→inc-path (here p) = inc-path p
locally-equal→inc-path {x = x} {y} (local c k) = sep c λ f hf →
    sym (inc-natural x)
  ∙ locally-equal→inc-path (k f hf)
  ∙ inc-natural y
```

## Every sheaf detects local equality

Dually, any natural transformation into any sheaf identifies
locally equal sections: the sheaf's separatedness discharges the
`local`{.Agda} constructor. Together with the previous theorem this
pins the unit's kernel between local equality and "equality in every
sheaf", which is what the pullback half of left exactness consumes.

```agda
sheaf-detects
  : (B : Functor (C ^op) (Sets ℓs)) (shf : is-sheaf J B)
  → (φ : A => B)
  → ∀ {U} {x y : A ʻ U}
  → Locally-equal x y
  → φ .η U x ≡ φ .η U y
sheaf-detects B shf φ (here p) = ap (φ .η _) p
sheaf-detects B shf φ {U} {x} {y} (local c k) =
  shf .is-sheaf.separate c λ {V} f hf →
      sym (happly (φ .is-natural U V f) x)
    ∙ sheaf-detects B shf φ (k f hf)
    ∙ happly (φ .is-natural U V f) y
```

## The remaining gap, sharpened

The converse — that `inc x ≡ inc y`{.Agda} implies merely
`Locally-equal x y`{.Agda} — is what still stands between
`Sh[_,_]`{.Agda} and `Topos`{.Agda}. By `sheaf-detects`{.Agda}, it
would follow from exhibiting *one* sheaf that reflects local
equality of $A$'s sections: the natural candidate is the
sheafification of the separated quotient $A/\!\sim$ (whose path
spaces are known by [[effectivity|quotients-are-effective]] of the
quotient, since saturation makes $\sim$ an equivalence relation) —
but mapping *out* of `Sheafify`{.Agda} into it requires it to
already be a sheaf, which is the existence half of the classical
two-step plus-construction. Formalising that construction — the
presheaf of patches modulo refinement, its separatedness, and the
sheafness of its second iterate — is now the single remaining
ingredient, and everything in this module is stated so as to be
consumed by it unchanged.
