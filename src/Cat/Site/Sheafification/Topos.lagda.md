<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Naturality
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Site.Sheafification
open import Cat.Instances.Sheaves
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Topoi.Base using (Topos)

import Cat.Site.Sheafification.Kernel
import Cat.Site.Sheafification.Plus
import Cat.Site.Sheafification.Lex
import Cat.Reasoning

open Functor
open _=>_
open is-pullback
```
-->

```agda
module Cat.Site.Sheafification.Topos
  {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  where
```

<!--
```agda
open Precategory C
open Coverage J using (Membership-covers)

private
  module S     = Small J
  module Sh    = Cat.Reasoning (Sheaves J ℓ)
  module PShR  = Cat.Reasoning (PSh ℓ C)
  module SetsR = Cat.Reasoning (Sets ℓ)
```
-->

# The topos of sheaves, officially {defines="sheafification-is-lex sheaves-topos"}

The [[topos of sheaves]] on a [[site]] deserves its name in the
official, structural sense of `Topos`{.Agda}: it is a full
subcategory of a presheaf category whose reflector preserves finite
limits. Everything but the left exactness of the reflector is
already established elsewhere; the [[kernel of the sheafification
unit|sheafification-kernel]] is the last missing ingredient, and this
module spends it. The strategy for pullback preservation is entirely
concrete: compute the pullback of presheaves *pointwise*, compute
the pullback of sheaves pointwise as well, and connect the
sheafification of the former to the latter by a comparison map whose
bijectivity is exactly the kernel theorem plus gluing.

## The pointwise pullback of presheaves

Fix a cospan $X \xrightarrow{f} Z \xleftarrow{g} Y$ of presheaves.
Its pullback is computed pointwise: a section over $U$ is a pair of
sections agreeing in $Z(U)$.

```agda
module _ {X Y Z : Functor (C ^op) (Sets ℓ)} (f : X => Z) (g : Y => Z) where
  Pc : Functor (C ^op) (Sets ℓ)
  Pc .F₀ U = el
    (Σ[ xy ∈ X ʻ U × Y ʻ U ] (f .η U (xy .fst) ≡ g .η U (xy .snd)))
    (Σ-is-hlevel 2
      (×-is-hlevel 2 (X .F₀ U .is-tr) (Y .F₀ U .is-tr))
      (λ _ → is-prop→is-set (Z .F₀ U .is-tr _ _)))
  Pc .F₁ h ((x , y) , e) = (X ⟪ h ⟫ x , Y ⟪ h ⟫ y) ,
       happly (f .is-natural _ _ h) x
    ∙∙ ap (Z .F₁ h) e
    ∙∙ sym (happly (g .is-natural _ _ h) y)
  Pc .F-id = funext λ ((x , y) , e) →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (happly (X .F-id) x) (happly (Y .F-id) y))
  Pc .F-∘ h₂ h₁ = funext λ ((x , y) , e) →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (happly (X .F-∘ h₂ h₁) x) (happly (Y .F-∘ h₂ h₁) y))
```

The two projections are natural on the nose, and the agreement
condition *is* the commutativity of the square.

```agda
  pc1 : Pc => X
  pc1 .η U ((x , y) , e) = x
  pc1 .is-natural U V h = refl

  pc2 : Pc => Y
  pc2 .η U ((x , y) , e) = y
  pc2 .is-natural U V h = refl
```

That this is a pullback in $\psh(\cC)$ is a pointwise computation:
maps into the pullback are pairs of maps with a pointwise agreement,
and equality of such maps is equality of the two components, since
the agreement is a proposition.

```agda
  Pc-is-pullback : is-pullback (PSh ℓ C) pc1 f pc2 g
  Pc-is-pullback .square = Nat-path λ U → funext λ ((x , y) , e) → e
  Pc-is-pullback .universal {p₁' = p₁'} {p₂'} sq .η U a =
    (p₁' .η U a , p₂' .η U a) , (sq ηₚ U $ₚ a)
  Pc-is-pullback .universal {p₁' = p₁'} {p₂'} sq .is-natural U V h =
    funext λ a → Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_
        (happly (p₁' .is-natural U V h) a)
        (happly (p₂' .is-natural U V h) a))
  Pc-is-pullback .p₁∘universal = Nat-path λ U → refl
  Pc-is-pullback .p₂∘universal = Nat-path λ U → refl
  Pc-is-pullback .unique {lim' = lim'} q₁ q₂ = Nat-path λ U → funext λ a →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (q₁ ηₚ U $ₚ a) (q₂ ηₚ U $ₚ a))
```

## The pointwise pullback of sheaves

Now apply the same construction one level up: sheafify the cospan,
and form the pointwise pullback $Q$ of the resulting cospan
$X^+ \to Z^+ \ot Y^+$ of sheaves. Because the sheafification functor
is built from the universal property, its action on morphisms
computes definitionally on the `inc`{.Agda} constructor, which the
rest of this module uses without further comment.

<!--
```agda
  private
    module LX = Sheafification J X
    module LY = Sheafification J Y
    module LZ = Sheafification J Z
```
-->

```agda
  Lf : LX.Sheafify => LZ.Sheafify
  Lf = Sheafification {C = C} {J = J} .F₁ f

  Lg : LY.Sheafify => LZ.Sheafify
  Lg = Sheafification {C = C} {J = J} .F₁ g

  Q : Functor (C ^op) (Sets ℓ)
  Q .F₀ U = el
    (Σ[ ab ∈ LX.Sheafify ʻ U × LY.Sheafify ʻ U ]
      (Lf .η U (ab .fst) ≡ Lg .η U (ab .snd)))
    (Σ-is-hlevel 2
      (×-is-hlevel 2 LX.squash LY.squash)
      (λ _ → is-prop→is-set (LZ.squash _ _)))
  Q .F₁ h ((a , b) , w) = (LX.map h a , LY.map h b) ,
       happly (Lf .is-natural _ _ h) a
    ∙∙ ap (LZ.map h) w
    ∙∙ sym (happly (Lg .is-natural _ _ h) b)
  Q .F-id = funext λ ((a , b) , w) →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (LX.map-id a) (LY.map-id b))
  Q .F-∘ h₂ h₁ = funext λ ((a , b) , w) →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (LX.map-∘ a) (LY.map-∘ b))

  q1 : Q => LX.Sheafify
  q1 .η U ((a , b) , w) = a
  q1 .is-natural U V h = refl

  q2 : Q => LY.Sheafify
  q2 .η U ((a , b) , w) = b
  q2 .is-natural U V h = refl
```

The point of the construction: $Q$ is itself a sheaf. Separatedness
is componentwise, since both components live in sheaves. For gluing,
a patch of $Q$ has two component patches; gluing each in its own
sheafification gives the two components of the candidate section,
and the *agreement* of these components is a $J$-local question —
so it follows from separatedness of $Z^+$, since it holds on the
cover by the very compatibility the patch carries.

<!--
```agda
  private
    patch-X : ∀ {U} {c : J ʻ U} → Patch Q (J .cover c) → Patch LX.Sheafify (J .cover c)
    patch-X p .part h hh = p .part h hh .fst .fst
    patch-X p .patch h hh h' hh' = ap (λ t → t .fst .fst) (p .patch h hh h' hh')

    patch-Y : ∀ {U} {c : J ʻ U} → Patch Q (J .cover c) → Patch LY.Sheafify (J .cover c)
    patch-Y p .part h hh = p .part h hh .fst .snd
    patch-Y p .patch h hh h' hh' = ap (λ t → t .fst .snd) (p .patch h hh h' hh')
```
-->

```agda
  Q-is-sheaf : is-sheaf J Q
  Q-is-sheaf = from-is-separated Q-sep Q-split where
    Q-sep : is-separated J Q
    Q-sep c loc = Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_
        (LX.Sheafify-is-sep c λ h hh → ap (λ t → t .fst .fst) (loc h hh))
        (LY.Sheafify-is-sep c λ h hh → ap (λ t → t .fst .snd) (loc h hh)))

    Q-split : ∀ {U} (c : J .covers U) (p : Patch Q (J .cover c)) → Section Q p
    Q-split c p = record { whole = (wx , wy) , cond ; glues = λ h hh →
      Σ-prop-path (λ _ → LZ.squash _ _)
        (ap₂ _,_
          (LX.Sheafify-is-sheaf .glues c (patch-X p) h hh)
          (LY.Sheafify-is-sheaf .glues c (patch-Y p) h hh)) }
      where
      wx = LX.Sheafify-is-sheaf .whole c (patch-X p)
      wy = LY.Sheafify-is-sheaf .whole c (patch-Y p)

      cond : Lf .η _ wx ≡ Lg .η _ wy
      cond = LZ.Sheafify-is-sep c λ h hh →
           ap (Lf .η _) (LX.Sheafify-is-sheaf .glues c (patch-X p) h hh)
        ∙∙ p .part h hh .snd
        ∙∙ sym (ap (Lg .η _) (LY.Sheafify-is-sheaf .glues c (patch-Y p) h hh))
```

Finally, $Q$ is a pullback of the sheafified cospan *in the category
of sheaves*. Since morphisms of sheaves are just morphisms of the
underlying presheaves, the proof is word for word the one for
`Pc`{.Agda} — note that it nowhere uses that the competitor is a
sheaf.

```agda
  Q-is-pullback : is-pullback (Sheaves J ℓ)
    {X = LX.Sheafify , LX.Sheafify-is-sheaf}
    {Z = LZ.Sheafify , LZ.Sheafify-is-sheaf}
    {Y = LY.Sheafify , LY.Sheafify-is-sheaf}
    {P = Q , Q-is-sheaf}
    q1 Lf q2 Lg
  Q-is-pullback .square = Nat-path λ U → funext λ ((a , b) , w) → w
  Q-is-pullback .universal {p₁' = p₁'} {p₂'} sq .η U t =
    (p₁' .η U t , p₂' .η U t) , (sq ηₚ U $ₚ t)
  Q-is-pullback .universal {p₁' = p₁'} {p₂'} sq .is-natural U V h =
    funext λ t → Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_
        (happly (p₁' .is-natural U V h) t)
        (happly (p₂' .is-natural U V h) t))
  Q-is-pullback .p₁∘universal = Nat-path λ U → refl
  Q-is-pullback .p₂∘universal = Nat-path λ U → refl
  Q-is-pullback .unique {lim' = lim'} q₁ q₂ = Nat-path λ U → funext λ t →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (q₁ ηₚ U $ₚ t) (q₂ ηₚ U $ₚ t))
```
