<!--
```agda
open import Cat.Diagram.Sieve
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Data.Set.Coequaliser

open Functor
open Section
open Patch
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Glue
  {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc)
  where
```

<!--
```agda
open Precategory C
open Coverage J using (Membership-covers)
```
-->

# Gluing: the plus-construction {defines="saturation-of-a-coverage plus-construction-gluing"}

This module carries out the *gluing* half of the plus-construction:
for a [[separated presheaf|separated-presheaf]] $B$ on a site, the
presheaf of patches-modulo-agreement is built, receives $B$
injectively, and is separated. The patches are indexed not by the
covers of the coverage but by its **saturation** — the closure of
the covering sieves under maximality, supersets, and local
character — defined, like local equality before it, as a
proposition-valued higher inductive type, so that the coverage's
merely-existing stability witnesses eliminate freely.

```agda
data is-covering : {U : ⌞ C ⌟} (S : Sieve C U) → Type (o ⊔ ℓ ⊔ ℓc) where
  has-id
    : ∀ {U} {S : Sieve C U}
    → id ∈ S → is-covering S
  by-J
    : ∀ {U} {S : Sieve C U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c → f ∈ S)
    → is-covering S
  glue-cover
    : ∀ {U} {S : Sieve C U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c → is-covering (pullback f S))
    → is-covering S
  squash
    : ∀ {U} {S : Sieve C U} → is-prop (is-covering S)
```

Saturated covers are closed under supersets and pullback — the
latter using stability, eliminated into the proposition.

```agda
covering-⊆
  : ∀ {U} {S T : Sieve C U}
  → (∀ {V} (f : Hom V U) → f ∈ S → f ∈ T)
  → is-covering S → is-covering T
covering-⊆ incl (has-id i) = has-id (incl id i)
covering-⊆ incl (by-J c sub) = by-J c λ f hf → incl f (sub f hf)
covering-⊆ incl (glue-cover c k) = glue-cover c λ f hf →
  covering-⊆ (λ g hg → incl (f ∘ g) hg) (k f hf)
covering-⊆ incl (squash a b i) =
  squash (covering-⊆ incl a) (covering-⊆ incl b) i

covering-stable
  : ∀ {U V} {S : Sieve C U} (g : Hom V U)
  → is-covering S → is-covering (pullback g S)
covering-stable {S = S} g (has-id i) = has-id
  (subst (_∈ S) (sym (idr g)) (subst (_∈ S) (idl g) (S .closed i g)))
covering-stable {S = S} g (by-J c sub) = ∥-∥-rec squash
  (λ (c' , sub') → by-J c' λ f hf → sub (g ∘ f) (sub' f hf))
  (J .stable c g)
covering-stable {S = S} g (glue-cover c k) = ∥-∥-rec squash
  (λ (c' , sub') → glue-cover c' λ f hf →
    covering-⊆ (λ h hh → subst (_∈ S) (sym (assoc g f h)) hh)
      (k (g ∘ f) (sub' f hf)))
  (J .stable c g)
covering-stable g (squash a b i) =
  squash (covering-stable g a) (covering-stable g b) i
```

A separated presheaf is separated at every saturated cover.

```agda
separated-at
  : ∀ {ℓs} {B : Functor (C ^op) (Sets ℓs)}
  → is-separated J B
  → ∀ {U} {S : Sieve C U} → is-covering S
  → is-separated₁ B S
separated-at {B = B} bsep (has-id i) l =
    sym (happly (B .F-id) _)
  ∙ l id i
  ∙ happly (B .F-id) _
separated-at bsep (by-J c sub) l =
  bsep c λ f hf → l f (sub f hf)
separated-at {B = B} bsep (glue-cover c k) l =
  bsep c λ f hf → separated-at {B = B} bsep (k f hf) λ g hg →
      sym (happly (B .F-∘ g f) _)
    ∙ l (f ∘ g) hg
    ∙ happly (B .F-∘ g f) _
separated-at {B = B} bsep (squash a b i) l =
  B .F₀ _ .is-tr _ _
    (separated-at {B = B} bsep a l) (separated-at {B = B} bsep b l) i
```
