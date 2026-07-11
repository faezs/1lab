---
description: |
  Lemma 2.4: the transition maps of the glued classifier have right
  adjoints, as a Galois adjunction between fibrewise sieve posets at
  every cartesian arrow.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Diagram.Sieve
open import Cat.Prelude

open import Neural.Order.Adjunction

open import Order.Base

import Physics.SmoothWorld.Forcing
import Neural.Stack.Grothendieck
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Adjunction
  {ℓ} {B : Precategory ℓ ℓ}
  (F : Functor (B ^op) (Strict-cats ℓ ℓ))
  where
```

# Transporting the classifier: Lemma 2.4 {defines="classifier-adjunction"}

The transition maps of the [[glued classifier|glued-classifier]]
pull sieves back along the cartesian arrows $(\alpha, \mathrm{id})$
of the total category. Belfiore–Bennequin's Lemma 2.4 equips each
with a right adjoint $\tau'_\alpha$ — the transport that carries a
theory at the deeper layer to the strongest theory at the shallower
one whose pullback it dominates. In this development the adjunction
is an instantiation: the sieve quantifiers of the forcing module
already provide $f^\star \dashv \forall_f$ over any category, and
the cartesian arrows are just particular $f$. What is new here is
the packaging the later modules consume: fibrewise sieve *posets*,
monotone transition and transport maps, and the [[Galois
adjunction|poset-adjunction]] between them.

<!--
```agda
private
  module B = Cat.Reasoning B

open Neural.Stack.Grothendieck F
open Physics.SmoothWorld.Forcing ∫F

open Precategory
open Poset
open ∫Hom
```
-->

## The fibrewise sieve posets

```agda
Sieves-on : (o : ∫F .Ob) → Poset ℓ ℓ
Sieves-on o .Ob = Sieve ∫F o
Sieves-on o ._≤_ S T = S ⊆ T
Sieves-on o .≤-thin = hlevel 1
Sieves-on o .≤-refl h m = m
Sieves-on o .≤-trans p q h m = q h (p h m)
Sieves-on o .≤-antisym p q = ext λ h → Ω-ua (p h) (q h)
```

## The adjunction

The left adjoint is the classifier's transition — pullback along
the cartesian arrow, definitionally — and the right adjoint is the
universal quantifier along it.

```agda
module _ {U V : B.Ob} (α : B.Hom U V) (ξ : Fib V .Ob) where
  private
    cart : ∫F .Hom (U , α ·₀ ξ) (V , ξ)
    cart = ∫hom α (Fib U .id)

  Ω-tr : Monotone (Sieves-on (V , ξ)) (Sieves-on (U , α ·₀ ξ))
  Ω-tr .hom = pullback cart
  Ω-tr .pres-≤ p h m = p (∫F ._∘_ cart h) m

  τ' : Monotone (Sieves-on (U , α ·₀ ξ)) (Sieves-on (V , ξ))
  τ' .hom = ∀[ cart ]
  τ' .pres-≤ {T} {T'} p = ∀[]-adj-→ cart (∀[ cart ] T) T' λ h m →
    p h (∀[]-adj-← cart (∀[ cart ] T) T (λ h' m' → m') h m)

  Ω⊣τ' : Ω-tr ⊣ₚ τ'
  Ω⊣τ' .unit {S} = ∀[]-adj-→ cart S (pullback cart S) (λ h m → m)
  Ω⊣τ' ._⊣ₚ_.counit {T} = ∀[]-adj-← cart (∀[ cart ] T) T (λ h m → m)
```

What is honestly *not* here: the paper's *section* equations
2.24–2.29, which further identify $\Omega_\alpha \circ \tau'_\alpha$
with the identity — that uses the split structure of the stack and
is deferred to the openness module, where the trivial-topology
hypotheses it depends on are set up; and the left-most adjoint
$\exists$ string, available from the same forcing module the moment
a construction wants it.
