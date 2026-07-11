---
description: |
  Theorem 2.1 and Definition 2.1: the standard and strong standard
  hypotheses for logical propagation along a split stack, and the
  theorem that fibrations satisfy them.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Diagram.Sieve
open import Cat.Prelude

open import Neural.Order.Adjunction

open import Order.Base

import Neural.Stack.Grothendieck
import Neural.Stack.Adjunction
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Semantics
  {ℓ} {B : Precategory ℓ ℓ}
  (F : Functor (B ^op) (Strict-cats ℓ ℓ))
  where
```

# Theorem 2.1: logical propagation along a stack {defines="standard-hypothesis"}

Belfiore–Bennequin's central chapter-2 result assembles the
transport lemmas: along every arrow $\alpha$ of the network, a
theory at the shallower layer propagates *backward* by
$\tau'_\alpha$ (feedback), a theory at the deeper layer propagates
*forward* by $\Omega_\alpha = \lambda_\alpha$ (feed-forward), the
two are adjoint, and — when each $F_\alpha$ is a fibration —
equation 2.30 holds: $\lambda_\alpha \circ \tau'_\alpha =
\mathrm{Id}$. Definition 2.1 then names the situation: a stack
satisfies the **standard hypothesis** when the adjoint transports
exist, and the **strong standard hypothesis** when 2.30 holds as
well.

In this sieve-level formalization the standard hypothesis is a
*theorem*, not a hypothesis: the direct-image/preimage adjunction of
[[Lemma 2.4|classifier-adjunction]] needs nothing at all, dissolving
the paper's caution about geometricity of $(F_\alpha)_!$ — an honest
strengthening, recorded here. The strong hypothesis is exactly the
section property, so Theorem 2.1 is: *mere strict lifts for every
transition functor imply the strong standard hypothesis*.

<!--
```agda
private
  module B = Cat.Reasoning B

open Neural.Stack.Grothendieck F
open Neural.Stack.Adjunction F
```
-->

```agda
standard-hypothesis : Type ℓ
standard-hypothesis =
  ∀ {U V : B.Ob} (α : B.Hom U V) {ξ' : Fib V .Precategory.Ob}
  → Ω-mono α {ξ'} ⊣ₚ τ'-mono α {ξ'}

strong-standard-hypothesis : Type ℓ
strong-standard-hypothesis =
  standard-hypothesis
  × ( ∀ {U V : B.Ob} (α : B.Hom U V) {ξ' : Fib V .Precategory.Ob}
      (T : Sieve (Fib U) (α ·₀ ξ'))
    → Ω[_] α (τ'[_] α T) ≡ T)
```

The theorem, in both halves: the standard hypothesis holds
unconditionally, and lifts upgrade it to the strong one.

```agda
standard : standard-hypothesis
standard α = Ω-fib⊣τ' α

theorem-2·1
  : (∀ {U V : B.Ob} (α : B.Hom U V) → has-lifts α)
  → strong-standard-hypothesis
theorem-2·1 lifts .fst = standard
theorem-2·1 lifts .snd α = lifts→section α (lifts α)
```

What is honestly *not* here, per the paper's own text: the claim
that $\lambda_\alpha$ is a morphism of *Heyting* algebras (that is
the openness dictionary of equations 2.13–2.16 and Proposition 2.2,
formalized in the openness module with the Boolean/complemented case
of [[Lemma 2.1|complemented-boolean]] as its classical instance);
and the groupoid contracted-product Lemma 2.2, whose group tier is
its own module. The paper's prose gloss — "the logic is richer in
$U'$ than in $U$" — is the split-monomorphism half of the section
property.
