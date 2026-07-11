---
description: |
  Every frame is a Heyting algebra: the implication is a join over a
  resized subset, giving the first inhabitants of is-heyting-algebra
  in the library, including the propositions and any power set.
---
<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Lub.Subset
open import Order.Instances.Pointwise
open import Order.Instances.Props
open import Order.Heyting
open import Order.Frame
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Neural.Order.FrameHeyting where
```

# Frames are Heyting algebras {defines="frame-heyting"}

A [[frame]] has finite meets and arbitrary (small) joins, with meets
distributing over joins. The distributive law says exactly that the
monotone map $- \cap y$ preserves joins, so it ought to have a right
adjoint $y \heyt -$ — making every frame a complete [[Heyting
algebra]]. Classically one invokes the adjoint functor theorem; here
we simply *write down* the adjoint as a join over a subset,

$$
y \heyt z \coloneqq \bigcup\, \{\, \gamma \mid \gamma \cap y \le z \,\}\text{,}
$$

using [[propositional resizing]] (in the guise of the subset-join
operator `⋃ˢ`{.Agda}) to make the subset small. This discharges a
long-standing TODO in `Order.Frame`, and produces the first
inhabitants of `is-heyting-algebra`{.Agda} in the library — the
record itself previously had none.

<!--
```agda
open is-heyting-algebra

private variable
  o ℓ : Level
```
-->

```agda
module _ {P : Poset o ℓ} (frm : is-frame P) where
  private
    module P = Order.Reasoning P
    module F = is-frame frm

  open Join-subsets P F.⋃-lubs
```

The implication, and the easy (currying) half of its universal
property: if $x \cap y \le z$ then $x$ itself is a member of the
subset being joined, so it lies below the join.

```agda
  frame-⇨ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
  frame-⇨ y z = ⋃ˢ λ γ → elΩ (γ F.∩ y P.≤ z)

  frame-ƛ : ∀ {x y z} → x F.∩ y P.≤ z → x P.≤ frame-⇨ y z
  frame-ƛ p = ⋃ˢ-inj (inc p)
```

Evaluation is where the frame condition earns its keep. Meeting the
join with $y$ distributes to a join of meets $\gamma \cap y$, each of
which lies below $z$ by the very membership condition defining the
subset. Since `⋃ˢ`{.Agda} is opaque, we unfold it for this one
computation.

```agda
  opaque
    unfolding ⋃ˢ

    frame-ev : ∀ {x y z} → x P.≤ frame-⇨ y z → x F.∩ y P.≤ z
    frame-ev {x} {y} {z} p =
      P.≤-trans (F.∩≤∩l p) $
      P.≤-trans (P.≤-refl' F.∩-comm) $
      P.≤-trans (P.≤-refl' (F.⋃-distribl y fst)) $
      F.⋃-universal z λ where
        (γ , w) → P.≤-trans (P.≤-refl' F.∩-comm) (□-out! (□-out! w))
```

Assembling the record is now entirely bookkeeping: the lattice
structure of a frame is already known upstream (binary joins and the
bottom element come from small joins), and the three implication
fields are exactly the definitions above.

```agda
  open is-heyting-algebra

  frame→heyting : is-heyting-algebra P
  frame→heyting .has-top    = F.has-top
  frame→heyting .has-bottom = F.has-bottom
  frame→heyting ._∪_        = F._∪_
  frame→heyting .∪-joins    = F.∪-joins
  frame→heyting ._∩_        = F._∩_
  frame→heyting .∩-meets    = F.∩-meets
  frame→heyting ._⇨_        = frame-⇨
  frame→heyting .ƛ          = frame-ƛ
  frame→heyting .ev         = frame-ev
```

## First instances

The poset of [[propositions]] is a Heyting algebra with implication
given by — implication. This instance is worth giving by hand rather
than through `frame→heyting`{.Agda}, because it then *computes*: the
implication of two propositions is literally the function type.

```agda
Props-heyting : is-heyting-algebra Props
Props-heyting .has-top    = Props-has-top
Props-heyting .has-bottom = Props-has-bot
Props-heyting ._∪_        = _∨Ω_
Props-heyting .∪-joins    = Props-has-joins
Props-heyting ._∩_        = _∧Ω_
Props-heyting .∩-meets    = Props-has-meets
Props-heyting ._⇨_        = _→Ω_
Props-heyting .ƛ p x y    = p (x , y)
Props-heyting .ev p (x , y) = p x y
```

Any power set is a Heyting algebra, by applying the theorem to the
frame of subsets. In particular the subobject lattices of sets — the
fibers of the simplest semantic transfer structures in the
topos-of-DNNs development — carry implication.

```agda
Subsets-heyting : ∀ {ℓ} {A : Type ℓ} → is-heyting-algebra (Subsets A)
Subsets-heyting {A = A} = frame→heyting (Power-frame A .snd)
```
