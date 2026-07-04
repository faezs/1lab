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
