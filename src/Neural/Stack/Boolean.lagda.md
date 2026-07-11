---
description: |
  Lemma 2.1, repaired: a Heyting algebra in which every element has
  a complement is Boolean — complements are unique, coincide with
  negation, and double negation is the identity.
---
<!--
```agda
open import Cat.Prelude hiding (¬_)

open import Order.Heyting
open import Order.Base

import Order.Lattice.Reasoning as Lat
import Neural.Order.Heyting.Reasoning
import Order.Reasoning
```
-->

```agda
module Neural.Stack.Boolean
  {o ℓ} {P : Poset o ℓ} (heyt : is-heyting-algebra P)
  where
```

# Complemented Heyting algebras are Boolean {defines="complemented-boolean"}

Belfiore–Bennequin's Lemma 2.1 asserts that the logic of a stack of
*groupoids* is Boolean. Constructively that is not a theorem — the
subobject classifier of groupoid presheaves is not decidable — so
the honest form, recorded by the roadmap, isolates the actually
classical ingredient as a hypothesis: **complementedness**. This
module proves the order-theoretic core, valid in any [[Heyting
algebra|heyting-algebra]]: an element with a complement has that
complement equal to its negation, complements are unique, and if
*every* element is complemented then double negation is the
identity — the algebra is Boolean. Where the paper uses Lemma 2.1,
the development will consume these lemmas together with an explicit
complementedness (equivalently, decidability) hypothesis on the
relevant fibers.

<!--
```agda
open Order.Reasoning P
open is-heyting-algebra heyt
open Lat has-is-lattice hiding (_∪_ ; _∩_)
open Neural.Order.Heyting.Reasoning heyt using (¬_; mp)
```
-->

```agda
record is-complement (x y : ⌞ P ⌟) : Type (o ⊔ ℓ) where
  field
    ∩-bot : x ∩ y ≡ bot
    ∪-top : x ∪ y ≡ top

open is-complement
```

A complement is exactly the negation: one inequality is the currying
of the meet equation, the other distributes the join equation.

```agda
complement→¬ : ∀ {x y} → is-complement x y → y ≡ ¬ x
complement→¬ {x} {y} c = ≤-antisym
  (ƛ (≤-trans (≤-refl' ∩-comm) (≤-refl' (c .∩-bot))))
  (≤-trans
    (∩-universal _ ≤-refl (≤-trans ! (≤-refl' (sym (c .∪-top)))))
    (≤-trans (∩-∪-distrib≤ heyt) (∪-universal _ (≤-trans mp ¡) ∩≤r)))
```

Uniqueness is immediate, and so is the symmetry of the complement
relation; combining the two directions gives the involution.

```agda
complement-unique
  : ∀ {x y z} → is-complement x y → is-complement x z → y ≡ z
complement-unique c c' = complement→¬ c ∙ sym (complement→¬ c')

complement-sym : ∀ {x y} → is-complement x y → is-complement y x
complement-sym c .∩-bot = ∩-comm ∙ c .∩-bot
complement-sym c .∪-top = ∪-comm ∙ c .∪-top

complement→involution
  : ∀ {x y} → is-complement x y → ¬ ¬ x ≡ x
complement→involution {x} {y} c =
  sym (complement→¬ (complement-sym c) ∙ ap ¬_ (complement→¬ c))

complemented→boolean
  : (∀ x → Σ[ y ∈ ⌞ P ⌟ ] is-complement x y)
  → ∀ x → ¬ ¬ x ≡ x
complemented→boolean compl x = complement→involution (compl x .snd)
```

What is honestly *not* claimed: that any stack of groupoids
satisfies the hypothesis. For the finite classical networks of the
golden thread the fibres are decidable and the hypothesis is
checkable; for general fibers it is irreducibly classical, exactly
as the roadmap's risk register records.
