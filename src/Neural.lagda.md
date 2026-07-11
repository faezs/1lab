---
description: |
  A reading guide to the formalization of Belfiore and Bennequin's
  "Topos and stacks of deep neural networks": what exists, where it
  lives, and what is honestly missing.
---
<!--
```agda
open import Cat.Prelude hiding (¬_)

open import Order.Heyting
open import Order.Base

open import Neural.Base
open import Neural.Order.Adjunction
open import Neural.Order.FrameHeyting

import Neural.Order.Heyting.Reasoning
```
-->

```agda
module Neural where
```

# Topos and stacks of deep neural networks: the reading guide

These modules formalize the mathematical content of Jean-Claude
Belfiore and Daniel Bennequin's *Topos and stacks of deep neural
networks* (arXiv:2106.14587v3) in cubical Agda, on top of this fork's
topos-theoretic physics stack. The governing document is
`TOPOS-OF-DNNS.md` at the repository root: an audited chapter-by-
chapter mapping of the paper onto this library, with the risks,
reformulation policies, and explicit skips recorded there once. The
project conventions — universe policy, arrow directions, the
split/strict modelling choice, the ban on model-structure records,
and the inhabited-interfaces rule — live in [`Neural.Base`].

[`Neural.Base`]: Neural.Base.html

Every claim below is a typechecked link: a `_ = theorem` block that
would fail to compile if the cited theorem changed. The guide grows a
section per milestone; the final section is the authoritative list of
what is *not* yet done.

## Phase 0: order-theoretic infrastructure

The logic of a network in this development is valued in [[Heyting
algebras]], and the semantic-transfer maps between layers are
adjunctions of monotone maps. Upstream 1lab had the Heyting record but
no inhabitants, and no first-class notion of poset adjunction; both
gaps are now filled.

**Galois adjunctions between posets.** The record `_⊣ₚ_`{.Agda}
packages a monotone adjoint pair by its unit and counit inequalities;
adjuncts, degenerate triangle identities, uniqueness of adjoints,
composition, and preservation of joins by left (meets by right)
adjoints all follow.

```agda
_ = _⊣ₚ_
_ = right-adjoint-unique
_ = left-adjoint-pres-lub
_ = _∘⊣ₚ_
```

**Frames are Heyting algebras.** The implication of a frame is the
join of a resized subset, discharging the TODO recorded in
`Order.Frame` since 2024. The instance layer gives the poset of
propositions (with implication computing to the function type) and
every power set.

```agda
_ = frame→heyting
_ = Props-heyting
_ = Subsets-heyting
```

**Heyting reasoning.** Modus ponens, mono/antitonicity of implication,
the unit law of conditioning $\top \heyt x = x$, the exponential law
$(x \cap y) \heyt z = x \heyt (y \heyt z)$ (Proposition 3.1 of the
paper: conditioning is a monoid action), preservation of meets,
negation with its unit and triple-negation laws, and the *exclusion
lemma* $y \le \lnot x \Rightarrow (x \heyt y) = \lnot x$ — the repair
of the broken step in the paper's Proposition 3.4, valid in any
Heyting algebra.

```agda
_ = Neural.Order.Heyting.Reasoning.mp
_ = Neural.Order.Heyting.Reasoning.top-⇨
_ = Neural.Order.Heyting.Reasoning.⇨-curry
_ = Neural.Order.Heyting.Reasoning.⇨-∩-r
_ = Neural.Order.Heyting.Reasoning.¬¬¬
_ = Neural.Order.Heyting.Reasoning.⇨-exclusion
```

## What is missing

Everything after Phase 0, at this point. In particular, and next in
order: the golden-thread chain network and its subobject classifier
computation; the typed-vertex fork site with the tine coverage (the
branch's first nontrivial `Coverage`); the explicit one-step
sheafification and its agreement with the HIT sheafification; the
reduction `Sh(C,J) ≃ PSh(C_𝐗)` (the paper's Proposition 1.1 and its
corollary); Alexandrov duality for arbitrary posets (Proposition 1.2,
generalized); and the discrete backpropagation flow (Theorem 1.1,
reformulated). The Ran-side Kan extension dualization
(`precompose ⊣ Ran`) is deliberately deferred to its first consumer;
over the finite network sites, direct limits will be finite products.
