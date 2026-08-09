---
description: |
  Reasoning combinators for Heyting algebras: modus ponens,
  monotonicity of implication, the exponential law, negation and its
  elementary laws, and the exclusion lemma repairing Proposition 3.4
  of Belfiore-Bennequin.
---
<!--
```agda
open import Cat.Prelude hiding (¬_)

open import Order.Heyting
open import Order.Base

import Order.Lattice.Reasoning as Lat
import Order.Reasoning
```
-->

```agda
module Neural.Order.Heyting.Reasoning
  {o ℓ} {P : Poset o ℓ} (heyt : is-heyting-algebra P)
  where
```

<!--
```agda
open Order.Reasoning P
open is-heyting-algebra heyt
open Lat has-is-lattice hiding (_∪_ ; _∩_)

private variable
  x y z : ⌞ P ⌟
```
-->

# Reasoning about Heyting algebras

This module collects the elementary consequences of the [[Heyting
algebra]] axioms that the semantic-information development uses
constantly. Upstream, `Order.Heyting` provides only the record and
distributivity; everything below is derived from the adjunction
`ƛ`{.Agda}/`ev`{.Agda} alone, so it holds in any Heyting algebra.

The fundamental combinator is **modus ponens**, the counit of the
adjunction $- \cap y \dashv y \heyt -$:

```agda
abstract
  mp : (x ⇨ y) ∩ x ≤ y
  mp = ev ≤-refl
```

Implication is monotone on the right and antitone on the left.

```agda
  ⇨-monotone-r : y ≤ z → (x ⇨ y) ≤ (x ⇨ z)
  ⇨-monotone-r p = ƛ (≤-trans mp p)

  ⇨-antitone-l : x ≤ y → (y ⇨ z) ≤ (x ⇨ z)
  ⇨-antitone-l p = ƛ (≤-trans (∩≤∩r p) mp)
```

Implication out of the top element is trivial, and implication *into*
the top element is trivially true; the first of these is the **unit
law of conditioning** ($\top.T = T$ in the notation of
Belfiore–Bennequin's Definition 3.1, reading $T|Q = Q \heyt T$).

```agda
  top-⇨ : (top ⇨ x) ≡ x
  top-⇨ = ≤-antisym
    (≤-trans (∩-universal _ ≤-refl !) mp)
    (ƛ ∩≤l)

  ⇨-top : (x ⇨ top) ≡ top
  ⇨-top = ≤-antisym ! (ƛ !)
```

The **exponential law**: implication from a meet is iterated
implication. Through the conditioning reading this is Proposition 3.1
of the paper — conditioning is an action of the meet monoid on
theories.

```agda
  ⇨-curry : ((x ∩ y) ⇨ z) ≡ (x ⇨ (y ⇨ z))
  ⇨-curry = ≤-antisym
    (ƛ (ƛ (≤-trans (≤-refl' (sym ∩-assoc)) mp)))
    (ƛ (≤-trans (≤-refl' ∩-assoc) (≤-trans (∩≤∩l mp) mp)))
```

Implication preserves meets in its codomain:

```agda
  ⇨-∩-r : (x ⇨ (y ∩ z)) ≡ ((x ⇨ y) ∩ (x ⇨ z))
  ⇨-∩-r = ≤-antisym
    (∩-universal _ (⇨-monotone-r ∩≤l) (⇨-monotone-r ∩≤r))
    (ƛ (∩-universal _
      (≤-trans (∩≤∩l ∩≤l) mp)
      (≤-trans (∩≤∩l ∩≤r) mp)))
```

An entailment $x \le y$ is the same thing as the implication $x \heyt
y$ being all of truth:

```agda
  ≤→⇨-top : x ≤ y → (x ⇨ y) ≡ top
  ≤→⇨-top p = ≤-antisym ! (ƛ (≤-trans ∩≤r p))

  ⇨-top→≤ : (x ⇨ y) ≡ top → x ≤ y
  ⇨-top→≤ p = ≤-trans
    (∩-universal _ (≤-trans ! (≤-refl' (sym p))) ≤-refl)
    mp
```

## Negation

Negation is implication into the bottom element. It is antitone,
meets its argument in falsity, and satisfies the unit and
triple-negation laws of double negation — but not, of course,
$\lnot\lnot x = x$, which is exactly what separates the intuitionistic
logic of a topos of DNNs from the Boolean case that
Belfiore–Bennequin's Lemma 2.1 must assume separately.

```agda
infix 30 ¬_

¬_ : ⌞ P ⌟ → ⌞ P ⌟
¬ x = x ⇨ bot

abstract
  ¬-antitone : x ≤ y → ¬ y ≤ ¬ x
  ¬-antitone = ⇨-antitone-l

  ∩-¬ : x ∩ ¬ x ≤ bot
  ∩-¬ = ≤-trans (≤-refl' ∩-comm) mp

  ¬¬-unit : x ≤ ¬ ¬ x
  ¬¬-unit = ƛ ∩-¬

  ¬¬¬ : ¬ ¬ ¬ x ≡ ¬ x
  ¬¬¬ = ≤-antisym (¬-antitone ¬¬-unit) ¬¬-unit
```

## The exclusion lemma

If a theory $y$ *excludes* the proposition $x$ — that is, $y \le \lnot
x$ — then conditioning $y$ by $x$ collapses it to $\lnot x$ exactly:

$$
x \heyt y \;=\; \lnot x\text{.}
$$

This innocuous computation is the repair of the garbled step in
Belfiore–Bennequin's Proposition 3.4 (their "$S|\top = \top$"): it is
what forces every degree-zero semantic cocycle to be constant on
theories excluding a fixed proposition, in *any* Heyting algebra, with
no connectivity or principality assumptions.

```agda
  ⇨-exclusion : y ≤ ¬ x → (x ⇨ y) ≡ ¬ x
  ⇨-exclusion {y} {x} p = ≤-antisym
    (≤-trans (⇨-monotone-r p)
             (≤-refl' (sym ⇨-curry ∙ ap (_⇨ bot) ∩-idem)))
    (ƛ (≤-trans (≤-refl' ∩-comm) (≤-trans ∩-¬ ¡)))
```
