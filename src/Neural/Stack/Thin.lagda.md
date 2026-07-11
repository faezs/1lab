---
description: |
  The Grothendieck construction of a poset-valued presheaf: a thinly
  displayed category with cartesian lifts given by reindexing — the
  fibrations of propositions and theories over a network that
  chapters 2 and 3 of Belfiore–Bennequin transport logic along.
---
<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

open import Order.Base

import Cat.Reasoning
import Order.Reasoning
```
-->

```agda
module Neural.Stack.Thin
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Posets o' ℓ'))
  where
```

# Thin stacks: poset-valued presheaves, fibred {defines="thin-stack"}

The stacks of Belfiore–Bennequin's chapter 2 are split fibrations
built from functors valued in categories; but the *logical* fibers
the transport machinery actually moves — layerwise posets of
propositions and theories, chapter 3's $\tilde A$ and $\tilde A'$ —
are *thin*. For these, the Grothendieck construction collapses to
something entirely propositional: a morphism over $\alpha$ from $x$
to $y$ is the inequality $x \le \alpha^\star y$, and every coherence
condition is automatic. This module performs that construction once,
for any poset-valued presheaf on any base, and equips it with its
cartesian lifts: the reindexings themselves.

Working thin-first is also the project's memory discipline: the
category-valued construction (with its transport bookkeeping) can be
developed against this module's template where a theorem genuinely
needs non-thin fibers.

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

  module Fb (U : B.Ob) = Order.Reasoning (F .Functor.F₀ U)

open Displayed
```
-->

A morphism over $\alpha : U \to V$, from $x$ in the fiber over $U$
to $y$ in the fiber over $V$, is the inequality $x \le \alpha^\star
y$; identities and composites are the reflexivity and transitivity
of the fibre orders, transported along the functoriality of the
reindexing.

```agda
private
  reidx : ∀ {U V} (α : B.Hom U V) → Monotone (F.₀ V) (F.₀ U)
  reidx α = F.₁ α

  thin : Thinly-displayed B o' ℓ'
  thin .Thinly-displayed.Ob[_] U = ⌞ F.₀ U ⌟
  thin .Thinly-displayed.Hom[_] {U} {V} α x y =
    Fb._≤_ U x (reidx α · y)
  thin .Thinly-displayed.H-Level-Hom[_] {a = U} =
    prop-instance (Fb.≤-thin U)
  thin .Thinly-displayed.id' {a = U} {x} =
    subst (Fb._≤_ U x) (sym (ap (_· x) F.F-id)) (Fb.≤-refl U)
  thin .Thinly-displayed._∘'_ {a = U} {x = x} {y} {z} {f} {g} f' g' =
    subst (Fb._≤_ U x) (sym (ap (_· z) (F.F-∘ g f)))
      (Fb.≤-trans U g' (reidx g .pres-≤ f'))

Thin-stack : Displayed B o' ℓ'
Thin-stack = with-thin-display thin
```

## The cartesian lifts

The lift of $\alpha$ at $y$ is the reindexing $\alpha^\star y$
itself, with the identity inequality; universality is a transport
along functoriality, and every coherence condition is a proposition.

```agda
open Cartesian-lift
open is-cartesian

Thin-stack-fibration : Cartesian-fibration Thin-stack
Thin-stack-fibration α y' .x' = reidx α · y'
Thin-stack-fibration {x = U} α y' .lifting = Fb.≤-refl U
Thin-stack-fibration {x = U} α y' .cartesian .universal {u = u'} m h' =
  subst (Fb._≤_ u' _) (ap (_· y') (F.F-∘ m α)) h'
Thin-stack-fibration α y' .cartesian .commutes m h' = prop!
Thin-stack-fibration α y' .cartesian .unique m' p = prop!
```
