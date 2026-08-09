<!--
```agda
open import Cat.Instances.Localisation
open import Cat.Functor.WideSubcategory
open import Cat.Functor.Equivalence
open import Cat.Prelude

import Cat.Reasoning

open is-precat-iso
open Functor
```
-->

```agda
module Cat.Instances.Localisation.Invertible where
```

# Localising at isomorphisms is inessential {defines="localisation-at-isomorphisms"}

If every map in the class $W$ is *already* invertible in $\cC$, then
freely inverting it does nothing: the [[localisation|localisation]]
functor $\cC \to \cC[W\inv]$ is an isomorphism of precategories. This
is the degenerate — but load-bearing — case of the presentation of
sheaf topoi as localisations of presheaf topoi: over a site with
trivial coverage, every presheaf is a sheaf, the local isomorphisms
are the honest isomorphisms, and the localisation collapses.

```agda
module _ {o ℓ w} (C : Precategory o ℓ) (W : Wide-subcat C w)
         (invs : ∀ {a b} (f : C .Precategory.Hom a b) → f ∈ W
               → Cat.Reasoning.is-invertible C f)
  where

  private
    module C = Cat.Reasoning C

    fold : Functor (Localisation C W) C
    fold = Localisation-fold C W invs

    module fold = Functor fold
```

By zigzag induction, embedding the folded-down value of a zigzag back
into the localisation recovers the zigzag: a forwards step is
functoriality, and a backwards step collapses against its formal
inverse using that the fold sends it to an honest inverse.

```agda
    rinv : ∀ {a b} (h : Zigzag C W a b) → zig (fold.₁ h) [] ≡ h
    rinv = Zigzag-elim-prop (λ h → zig (fold.₁ h) [] ≡ h)
      (zig-id [])
      (λ f h ih → sym (zig-∘ f (fold.₁ h) []) ∙ ap (zig f) ih)
      (λ f hf h ih →
          sym (zig-∘ (C.is-invertible.inv (invs f hf)) (fold.₁ h) [])
        ∙ ap (zig (C.is-invertible.inv (invs f hf))) ih
        ∙ sym (zag-zig f hf (zig (C.is-invertible.inv (invs f hf)) h))
        ∙ ap (zag f hf)
            ( zig-∘ f (C.is-invertible.inv (invs f hf)) h
            ∙ ap (λ e → zig e h) (C.is-invertible.invl (invs f hf))
            ∙ zig-id h))
```

Since the localisation has the same objects as $\cC$, and the fold is
inverse to the inclusion on morphisms, the localisation functor is an
isomorphism of precategories.

```agda
  Localise-is-precat-iso : is-precat-iso (Localise C W)
  Localise-is-precat-iso .has-is-iso = id-equiv
  Localise-is-precat-iso .has-is-ff = is-iso→is-equiv
    (iso fold.₁ rinv λ f → C.idr f)
```
