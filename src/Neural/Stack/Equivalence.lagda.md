---
description: |
  The unit and counit comparing a compatible family with the
  fibrewise restriction of its total presheaf, and conversely — with
  identity components, since the two round trips agree on the nose
  on objects.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Neural.Stack.Transport

import Cat.Functor.Reasoning.Presheaf as Psh
import Neural.Stack.Grothendieck
import Neural.Stack.Restriction
import Neural.Stack.Presheaves
import Neural.Stack.Family
import Neural.Stack.Fibre
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Equivalence
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  (κ : Level)
  where
```

# The two presentations agree {defines="family-presheaf-unit"}

Round-tripping a [[compatible family|presheaf-family]] through its
[[total presheaf|family-to-presheaf]] and back along the
[[fibrewise restriction|presheaf-to-family]] changes *nothing on
objects*: both composites literally preserve the underlying sets.
The comparison maps therefore have identity components, and all
their content lives in the naturality proofs — which close with the
transport lemma stock already established. This module constructs
the unit (family side) and counit (presheaf side); their pointwise
invertibility is manifest, and the full packaging as an equivalence
of categories is deferred to where a theorem first consumes it.

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

open Neural.Stack.Grothendieck F
open Neural.Stack.Restriction F κ
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

## The unit

```agda
unit : (A : Family) → Family-hom A (Res₀ (Tot₀ A))
unit A .map U .η ξ x = x
unit A .map U .is-natural ξ ζ u = funext λ x → sym $
     ap (Psh.₁ (A .fam U) (subst (Fib U .Hom ζ) (sym (·₀-id ξ)) u))
       (A .tr-id x)
  ∙  P-sub-both (Fib U) (A .fam U) (sym (·₀-id ξ)) u x
unit A .com {U} {V} α {ξ} x = Psh.F-id (A .fam U)
```

## The counit

The composite of the cartesian arrow with a vertical inclusion *is*
the general morphism $(\alpha, u)$, up to the unit law of the base —
one `∫Hom-path`{.Agda ident=∫Hom-path} away.

```agda
counit : (X : Functor ((∫F) ^op) (Sets κ)) → Tot₀ (Res₀ X) => X
counit X .η (U , ξ) x = x
counit X .is-natural (V , ζ) (U , ξ) (∫hom α u) = funext λ x →
     sym (Psh.F-∘ X (ι U .F₁ u) (∫hom α (Fib U .id)))
  ∙  ap (λ m → X .F₁ m x) keycu
  where
    S = sym (·₀-∘ α B.id ζ)
    Q = sym (·₀-id (α ·₀ ζ))

    keycu : ∫F ._∘_ (∫hom α (Fib U .id)) (ι U .F₁ u) ≡ ∫hom α u
    keycu = ∫Hom-path Grothendieck (B.idr α) $ to-pathp $
         ap (subst (Fib U .Hom ξ) (ap (_·₀ ζ) (B.idr α)))
           (ap (subst (Fib U .Hom ξ) S)
             ( comp-key F.F-id (Fib U .id) u
             ∙ ap (subst (Fib U .Hom ξ) Q) (Fib U .idl u))
           ∙ sym (subst-∙ (Fib U .Hom ξ) Q S u))
      ∙  sym (subst-∙ (Fib U .Hom ξ) (Q ∙ S) (ap (_·₀ ζ) (B.idr α)) u)
      ∙  sub-set (Fib U) (Fib-set U) ((Q ∙ S) ∙ ap (_·₀ ζ) (B.idr α)) u
```

Both comparison maps have identity components, so each is invertible
fibrewise by inspection; what is *not* yet here is the packaging of
`Tot`{.Agda ident=Tot} and `Res`{.Agda ident=Res} as an equivalence
of categories (naturality of the comparisons in their argument, the
triangle identities, and the invertibility record) — mechanical from
this module's content, and deferred to its first consumer.
