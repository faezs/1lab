---
description: |
  The presentation theorem for split-stack presheaves: taking total
  presheaves is an equivalence between compatible families and the
  presheaf topos of the total category.
---
<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
import Neural.Stack.Grothendieck
import Neural.Stack.Restriction
import Neural.Stack.Equivalence
import Neural.Stack.Presheaves
import Neural.Stack.Family
import Neural.Stack.Fibre
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Presentation
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  (κ : Level)
  where
```

# The presentation theorem {defines="stack-presentation"}

The two presentations of a split stack's presheaves — compatible
families of fibre presheaves, and presheaves on the total category —
are *equivalent categories*: the total-presheaf functor is fully
faithful (a natural transformation is determined by, and freely
reconstructed from, its fibrewise components) and split essentially
surjective (the counit is an isomorphism with identity components).
This is the precise content behind the paper's silent interchange of
equations 2.3 and 2.4–2.6.

<!--
```agda
private
  module B = Cat.Reasoning B
  module PC = Cat.Reasoning (PSh κ (Neural.Stack.Grothendieck.∫F F))

open Neural.Stack.Grothendieck F
open Neural.Stack.Restriction F κ
open Neural.Stack.Equivalence F κ
open Neural.Stack.Presheaves F κ
open Neural.Stack.Family F κ
open Neural.Stack.Fibre F

open Precategory
open Family-hom
open Functor
open Family
open ∫Hom
open _=>_
```
-->

## Full faithfulness

A map of total presheaves restricts to fibrewise components, whose
compatibility with the family structure is its naturality at
vertical and cartesian arrows — massaged through the identity
comparison maps.

```agda
back : {A A' : Family} → Tot₀ A => Tot₀ A' → Family-hom A A'
back {A} {A'} h .map U .η ξ = h .η (U , ξ)
back {A} {A'} h .map U .is-natural ξ ζ u = funext λ x →
     ap (h .η (U , ζ)) (happly (unit A .map U .is-natural ξ ζ u) x)
  ∙  happly (h .is-natural (U , ξ) (U , ζ) (ι U .F₁ u)) x
  ∙  sym (happly (unit A' .map U .is-natural ξ ζ u) (h .η (U , ξ) x))
back {A} {A'} h .com {U} {V} α {ξ} x =
     sym (Psh.F-id (A' .fam U))
  ∙  sym (happly (h .is-natural (V , ξ) (U , α ·₀ ξ) (∫hom α (Fib U .id))) x)
  ∙  ap (h .η (U , α ·₀ ξ)) (Psh.F-id (A .fam U))

Tot-is-ff : is-fully-faithful Tot
Tot-is-ff {A} {A'} = is-iso→is-equiv isom where
  isom : is-iso (Tot .F₁)
  isom .is-iso.from = back
  isom .is-iso.rinv h = Nat-path λ _ → refl
  isom .is-iso.linv g = Family-hom-path λ U → Nat-path λ ξ → refl
```

## Split essential surjectivity, and the theorem

```agda
Tot-is-split-eso : is-split-eso Tot
Tot-is-split-eso X = Res₀ X , PC.make-iso (counit X) (counit⁻¹ X)
  (counit-invl X) (counit-invr X)

Tot-is-equivalence : is-equivalence Tot
Tot-is-equivalence = ff+split-eso→is-equivalence Tot-is-ff Tot-is-split-eso
```

With the equivalence in hand, every statement about the presheaf
topos of $\int F$ — its classifier, its logic — transports to the
family presentation and back; the glued classifier module already
uses the counit half of this directly.
