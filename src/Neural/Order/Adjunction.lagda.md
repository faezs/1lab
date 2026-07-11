---
description: |
  Galois adjunctions between posets: monotone adjoint pairs, their
  triangle identities, uniqueness and composition, and preservation of
  joins and meets.
---
<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Neural.Order.Adjunction where
```

# Galois adjunctions between posets {defines="galois-connection poset-adjunction"}

A **Galois adjunction** (or *Galois connection*, in its
order-reversing guise) is an adjunction between posets: a pair of
[[monotone maps]] $L : P \to Q$ and $R : Q \to P$ such that

$$
L(x) \le y \quad\text{iff}\quad x \le R(y)\text{.}
$$

Because hom-"sets" in a poset are propositions, all the coherence data
of an adjunction collapses: it suffices to give the unit and counit
inequalities, and every diagram commutes automatically. This tiny
record is the engine behind the semantic-transfer machinery of the
topos-of-DNNs development — the transfer maps $\pi^\star \dashv
\pi_\star$ between layer logics, the adjunction $\Omega_\alpha \dashv
\tau'_\alpha$ of Belfiore–Bennequin's Lemma 2.4, and the quantifier
strings all instantiate it — but it is completely general order
theory, missing upstream as a first-class notion.

<!--
```agda
private variable
  o ℓ o' ℓ' o'' ℓ'' : Level
```
-->

```agda
module _ {P : Poset o ℓ} {Q : Poset o' ℓ'} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  record _⊣ₚ_ (L : Monotone P Q) (R : Monotone Q P) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    field
      unit   : ∀ {x} → x P.≤ R · (L · x)
      counit : ∀ {y} → L · (R · y) Q.≤ y
```

The two *adjunct* maps translate between the two hom-inequalities; in
the posetal setting they are inverse implications between
propositions, so the adjunction really is the biconditional above.

```agda
    adjunct-l : ∀ {x y} → L · x Q.≤ y → x P.≤ R · y
    adjunct-l p = P.≤-trans unit (R .pres-≤ p)

    adjunct-r : ∀ {x y} → x P.≤ R · y → L · x Q.≤ y
    adjunct-r p = Q.≤-trans (L .pres-≤ p) counit
```

The triangle identities also degenerate into something stronger than
usual: the composites $LRL$ and $RLR$ are *equal* to $L$ and $R$, by
antisymmetry.

```agda
    L-R-L : ∀ {x} → L · (R · (L · x)) ≡ L · x
    L-R-L = Q.≤-antisym counit (L .pres-≤ unit)

    R-L-R : ∀ {y} → R · (L · (R · y)) ≡ R · y
    R-L-R = P.≤-antisym (R .pres-≤ counit) unit

  open _⊣ₚ_ public
```

<!--
```agda
  unquoteDecl H-Level-⊣ₚ = declare-record-hlevel 1 H-Level-⊣ₚ (quote _⊣ₚ_)
```
-->

Adjoints determine each other: two right adjoints to the same monotone
map agree, and dually.

```agda
  right-adjoint-unique
    : {L : Monotone P Q} {R R' : Monotone Q P}
    → L ⊣ₚ R → L ⊣ₚ R' → R ≡ R'
  right-adjoint-unique a b = ext λ y → P.≤-antisym
    (adjunct-l b (a .counit))
    (adjunct-l a (b .counit))

  left-adjoint-unique
    : {L L' : Monotone P Q} {R : Monotone Q P}
    → L ⊣ₚ R → L' ⊣ₚ R → L ≡ L'
  left-adjoint-unique a b = ext λ x → Q.≤-antisym
    (adjunct-r a (b .unit))
    (adjunct-r b (a .unit))
```

Left adjoints preserve any least upper bounds that exist, and right
adjoints preserve greatest lower bounds. Note that this is
*preservation*, not the adjoint functor theorem: no completeness
assumption on either poset is needed.

```agda
  module _ {L : Monotone P Q} {R : Monotone Q P} (adj : L ⊣ₚ R) where
    open is-lub
    open is-glb

    left-adjoint-pres-lub
      : ∀ {ι} {I : Type ι} {f : I → ⌞ P ⌟} {l}
      → is-lub P f l → is-lub Q (λ i → L · f i) (L · l)
    left-adjoint-pres-lub lub .fam≤lub i = L .pres-≤ (lub .fam≤lub i)
    left-adjoint-pres-lub lub .least ub p = adjunct-r adj
      (lub .least (R · ub) λ i → adjunct-l adj (p i))

    right-adjoint-pres-glb
      : ∀ {ι} {I : Type ι} {f : I → ⌞ Q ⌟} {g}
      → is-glb Q f g → is-glb P (λ i → R · f i) (R · g)
    right-adjoint-pres-glb glb .glb≤fam i = R .pres-≤ (glb .glb≤fam i)
    right-adjoint-pres-glb glb .greatest lb p = adjunct-l adj
      (glb .greatest (L · lb) λ i → adjunct-r adj (p i))
```

Finally, adjunctions compose, and the identity is self-adjoint — so
posets, monotone maps and adjunctions organise the way one expects,
though we do not need the 2-categorical packaging here.

```agda
idₘ⊣idₘ : {P : Poset o ℓ} → idₘ {P = P} ⊣ₚ idₘ
idₘ⊣idₘ {P = P} .unit   = Poset.≤-refl P
idₘ⊣idₘ {P = P} .counit = Poset.≤-refl P

module _
  {A : Poset o ℓ} {B : Poset o' ℓ'} {C : Poset o'' ℓ''}
  {L' : Monotone B C} {R' : Monotone C B}
  {L : Monotone A B} {R : Monotone B A}
  where
  private
    module A = Order.Reasoning A
    module C = Order.Reasoning C

  _∘⊣ₚ_ : L' ⊣ₚ R' → L ⊣ₚ R → (L' ∘ₘ L) ⊣ₚ (R ∘ₘ R')
  (u ∘⊣ₚ l) .unit   = A.≤-trans (l .unit) (R .pres-≤ (u .unit))
  (u ∘⊣ₚ l) .counit = C.≤-trans (L' .pres-≤ (l .counit)) (u .counit)
```
