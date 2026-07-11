<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Ring.Cat.Initial
open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex

import Cat.Instances.FormalSmoothSets
import Algebra.Ring.Kahler
import Cat.Reasoning

open make-abelian-group
open Chain-complex
open Chain-map
open Functor
```
-->

```agda
module Cat.Instances.FormalSmoothSets.Deligne {ℓ} (R : CRing ℓ) where
```

<!--
```agda
open Cat.Instances.FormalSmoothSets R
open Algebra.Ring.Kahler R
open ThHom

private
  module CR = Cat.Reasoning (CRings ℓ)
  module Rg = Cat.Reasoning (Rings ℓ)
```
-->

# The Deligne complex {defines="deligne-complex"}

A gauge field on a probe is not just a $1$-form: it is a $1$-form
*up to* gauge transformations by functions, which are themselves
identified up to integer shifts — the quantization of charge. The
**Deligne complex** packages exactly this data, as a [[chain
complex|chain-complex]] valued presheaf on the [[site of thickened
affine spaces|formal-smooth-set]]: in degree $0$ the [[Kähler
differentials|kahler-differentials]] $\Omega^1$, in degree $1$ the
functions, in degree $2$ the integers, mapping by the universal
derivation and the initial ring homomorphism respectively:

$$
\bZ \hookrightarrow \scO \xrightarrow{\mathrm{d}} \Omega^1.
$$

Applying the [[inverse Dold–Kan construction|dold-kan]] $\Gamma$
probe-wise then produces the simplicial presheaf $\mathbf{B}U(1)_%
\mathrm{conn}$ of gauge fields, gauge transformations between them,
and the discrete ambiguity of the gauge transformations themselves.

## The groups

Each level of the complex is an abelian group: the additive group of
integers, the additive group of the probe's function ring, and the
Kähler differentials under addition of forms.

```agda
Liftℤ-ab : Abelian-group ℓ
Liftℤ-ab = Liftℤ .fst , record
  { _*_ = Zr._+_ ; has-is-ab = Zr.+-group }
  where module Zr = Ring-on (Liftℤ .snd)

O-ab : ThAff → Abelian-group ℓ
O-ab U = O U .fst , record
  { _*_ = OU._+_ ; has-is-ab = OU.+-group }
  where module OU = CRing-on (O U .snd)

Ω¹-ab : ThAff → Abelian-group ℓ
Ω¹-ab U = to-ab mk where
  mk : make-abelian-group (Ω¹ (O U) (struct U))
  mk .ab-is-set = squashω
  mk .mul = _+ω_
  mk .inv = -ω_
  mk .1g = 0ω
  mk .idl = +ω-idl
  mk .assoc = +ω-assoc
  mk .invl x = +ω-comm (-ω x) x ∙ +ω-invr x
  mk .comm = +ω-comm
```

## The boundaries

The differential $\scO \to \Omega^1$ is the universal derivation,
additive by the defining law of $\Omega^1$; the inclusion $\bZ \to
\scO$ is the [[initial|initial-ring]] ring homomorphism. Their
composite vanishes because the initial map into the probe's ring
factors — by initiality — through the structure map from the base
ring, whose image the derivation kills.

<!--
```agda
private
  ring-of : ThAff → Ring ℓ
  ring-of U = O U .fst , CRing-on.has-ring-on (O U .snd)

  Rring : Ring ℓ
  Rring = R .fst , CRing-on.has-ring-on (R .snd)

  to-rings
    : {A B : CRing ℓ} → CRings ℓ .Precategory.Hom A B
    → Rings ℓ .Precategory.Hom
        (A .fst , CRing-on.has-ring-on (A .snd))
        (B .fst , CRing-on.has-ring-on (B .snd))
  to-rings f .∫Hom.fst = f .∫Hom.fst
  to-rings f .∫Hom.snd = f .∫Hom.snd
```
-->

```agda
ιO : (U : ThAff) → Rings ℓ .Precategory.Hom Liftℤ (ring-of U)
ιO U = Int-is-initial (ring-of U) .centre

d-hom : (U : ThAff) → Ab ℓ .Precategory.Hom (O-ab U) (Ω¹-ab U)
d-hom U .∫Hom.fst = dₖ
d-hom U .∫Hom.snd .is-group-hom.pres-⋆ = d-+

ι-hom : (U : ThAff) → Ab ℓ .Precategory.Hom Liftℤ-ab (O-ab U)
ι-hom U .∫Hom.fst = ιO U .∫Hom.fst
ι-hom U .∫Hom.snd .is-group-hom.pres-⋆ =
  is-ring-hom.pres-+ (ιO U .∫Hom.snd)

d-kills-ι
  : (U : ThAff) (x : ⌞ Liftℤ-ab ⌟)
  → dₖ (ιO U .∫Hom.fst x) ≡ 0ω
d-kills-ι U x =
    ap (λ h → dι h x)
      (Int-is-initial (ring-of U) .paths
        (to-rings (struct U) Rg.∘ Int-is-initial Rring .centre))
  ∙ d-const (Int-is-initial Rring .centre .∫Hom.fst x)
  where
  dι : Rings ℓ .Precategory.Hom Liftℤ (ring-of U) → ⌞ Liftℤ-ab ⌟
     → Ω¹ (O U) (struct U)
  dι h y = dₖ (h .∫Hom.fst y)
```

## The complex, functorially

<!--
```agda
private
  Zero-ab' : Abelian-group ℓ
  Zero-ab' = to-ab mk where
    mk : make-abelian-group (Lift ℓ ⊤)
    mk .ab-is-set = hlevel 2
    mk .mul _ _ = lift tt
    mk .inv _ = lift tt
    mk .1g = lift tt
    mk .idl _ = refl
    mk .assoc _ _ _ = refl
    mk .invl _ = refl
    mk .comm _ _ = refl

  zero-hom : {X Y : Abelian-group ℓ} → Ab ℓ .Precategory.Hom X Y
  zero-hom {X} {Y} .∫Hom.fst _ = Abelian-group-on.1g (Y .snd)
  zero-hom {X} {Y} .∫Hom.snd .is-group-hom.pres-⋆ _ _ =
    sym (Abelian-group-on.idl (Y .snd))
```
-->

```agda
Del²-at : ThAff → Chain-complex ℓ
Del²-at U .ob 0 = Ω¹-ab U
Del²-at U .ob 1 = O-ab U
Del²-at U .ob 2 = Liftℤ-ab
Del²-at U .ob (suc (suc (suc k))) = Zero-ab'
Del²-at U .∂ᶜ 0 = d-hom U
Del²-at U .∂ᶜ 1 = ι-hom U
Del²-at U .∂ᶜ (suc (suc n)) = zero-hom
Del²-at U .∂ᶜ-∂ᶜ 0 x = d-kills-ι U x
Del²-at U .∂ᶜ-∂ᶜ 1 x = is-group-hom.pres-id (ι-hom U .∫Hom.snd)
Del²-at U .∂ᶜ-∂ᶜ (suc (suc n)) x = refl
```

Functoriality is inherited from the pushforward of differential
forms: the square with the derivation commutes definitionally, and
the square with the integers commutes because *both* composites are
ring homomorphisms out of $\bZ$, of which there is exactly one.

```agda
Del²-map
  : {U V : ThAff} (h : ThHom V U)
  → Chain-map (Del²-at U) (Del²-at V)
Del²-map h .map 0 .∫Hom.fst = Ω¹-map (h .fun) (h .commutes)
Del²-map h .map 0 .∫Hom.snd .is-group-hom.pres-⋆ x y = refl
Del²-map h .map 1 .∫Hom.fst = h .fun .∫Hom.fst
Del²-map h .map 1 .∫Hom.snd .is-group-hom.pres-⋆ =
  is-ring-hom.pres-+ (h .fun .∫Hom.snd)
Del²-map h .map 2 .∫Hom.fst x = x
Del²-map h .map 2 .∫Hom.snd .is-group-hom.pres-⋆ x y = refl
Del²-map h .map (suc (suc (suc k))) .∫Hom.fst x = x
Del²-map h .map (suc (suc (suc k))) .∫Hom.snd
  .is-group-hom.pres-⋆ x y = refl
Del²-map {U} {V} h .comm 0 x = refl
Del²-map {U} {V} h .comm 1 x = sym
  (ap (λ h' → h' .∫Hom.fst x)
    (Int-is-initial (ring-of V) .paths
      (to-rings (h .fun) Rg.∘ ιO U)))
Del²-map {U} {V} h .comm 2 x = refl
Del²-map {U} {V} h .comm (suc (suc (suc n))) x = refl

Deligne² : Functor (ThCartSp ^op) (Ch ℓ)
Deligne² .F₀ = Del²-at
Deligne² .F₁ = Del²-map
Deligne² .F-id {U} = Chain-map-path λ where
  0 → ext λ x → Ω¹-map-id (CR.idl (struct U)) x
  1 → ext λ x → refl
  2 → ext λ x → refl
  (suc (suc (suc k))) → ext λ x → refl
Deligne² .F-∘ f g = Chain-map-path λ where
  0 → ext λ x → Ω¹-map-∘ (f .fun) (g .fun) _ _ _ x
  1 → ext λ x → refl
  2 → ext λ x → refl
  (suc (suc (suc k))) → ext λ x → refl
```
