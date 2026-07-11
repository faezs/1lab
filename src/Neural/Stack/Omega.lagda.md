---
description: |
  The glued subobject classifier of a split stack: the family of
  fibrewise sieve-presheaves obtained by restricting the classifier
  of the total presheaf topos, and the comparison isomorphism that
  is the paper's Proposition 2.1.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Cat.Diagram.Sieve

import Cat.Instances.Presheaf.Omega
import Neural.Stack.Grothendieck
import Neural.Stack.Restriction
import Neural.Stack.Equivalence
import Neural.Stack.Presheaves
import Neural.Stack.Family
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Omega
  {ℓ} {B : Precategory ℓ ℓ}
  (F : Functor (B ^op) (Strict-cats ℓ ℓ))
  where
```

# The glued classifier of a stack {defines="glued-classifier"}

The presheaf topos of the total category $\int F$ has a [[subobject
classifier|subobject-classifier-presheaf]] — the presheaf of sieves.
Belfiore–Bennequin's Proposition 2.1 computes it *fibrewise*: the
classifier is glued from the sieves of the fibres, with transition
maps pulling back along the cartesian arrows. In this development
that computation is a one-liner, because the machinery already
built does the gluing: the glued classifier **is** the [[fibrewise
restriction|presheaf-to-family]] of the total classifier, and the
comparison between its total presheaf and the classifier is the
counit of the presentation equivalence — an isomorphism with
identity components. The uniform universe level matches the
project's logic-layer policy (the network sites are finite).

<!--
```agda
private
  module B = Cat.Reasoning B

open Neural.Stack.Grothendieck F
open Neural.Stack.Restriction F ℓ
open Neural.Stack.Equivalence F ℓ
open Neural.Stack.Presheaves F ℓ
open Neural.Stack.Family F ℓ

open Cat.Instances.Presheaf.Omega ∫F using (PSh-omega) public

open Functor
open _=>_
```
-->

```agda
Ω-family : Family
Ω-family = Res₀ ((Sieves {C = ∫F}))
```

The value of the glued classifier over $U$ at a fibre object $\xi$
is, definitionally, the set of sieves on $(U, \xi)$ in the total
category — the paper's description of $\Omega_F$, verified by
`refl`{.Agda}:

```agda
_ : ∀ {U : B.Ob} {ξ : Fib U .Precategory.Ob}
  → Ω-family .Family.fam U ʻ ξ ≡ ((Sieves {C = ∫F}) ʻ (U , ξ))
_ = refl
```

## Proposition 2.1

The counit has identity components, so it is invertible outright:
the total presheaf of the glued family *is* the subobject
classifier of $\psh(\int F)$, and subobjects in the stack topos are
classified by fibrewise sieve data.

```agda
counit⁻¹ : (X : Functor ((∫F) ^op) (Sets ℓ)) → X => Tot₀ (Res₀ X)
counit⁻¹ X .η (U , ξ) x = x
counit⁻¹ X .is-natural a b f = sym (counit X .is-natural a b f)

counit-invl : (X : Functor ((∫F) ^op) (Sets ℓ))
  → counit X ∘nt counit⁻¹ X ≡ idnt
counit-invl X = Nat-path λ _ → refl

counit-invr : (X : Functor ((∫F) ^op) (Sets ℓ))
  → counit⁻¹ X ∘nt counit X ≡ idnt
counit-invr X = Nat-path λ _ → refl

Ω-comparison : Tot₀ Ω-family => (Sieves {C = ∫F})
Ω-comparison = counit ((Sieves {C = ∫F}))
```

What is honestly *not* here: the fibrewise characterisation of the
*closed* sieves once the base carries its Grothendieck topology
(that belongs to the openness module), and the `true`-classifying
square in family form — both consumers of `PSh-omega`{.Agda}, which
this module re-exports for them.
