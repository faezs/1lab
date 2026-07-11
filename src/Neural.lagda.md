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

open import Neural.Chain
open import Neural.Chain.Omega
open import Neural.Graph.Fork
open import Neural.Site.Topology
open import Neural.Sheaf.Explicit
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

## Phase 1: the chain network (the golden thread)

The [[chain network|chain-network]] — the multilayer perceptron — is
the permanent regression test of the development: its site, dynamics,
and classifier are computed concretely, and the two-layer Boolean
example runs by `refl`{.Agda}.

**The dynamical objects.** The chain graph, its path-category site,
directedness (`path-≤`{.Agda}, `chain-no-loop`{.Agda}); the
functioning `X^`{.Agda} at fixed weights, the presheaf `𝕎`{.Agda} of
unconsumed weights — strictly functorial, since 1lab's `Nat.≤` is
definitionally proof-irrelevant — and the crossed object `𝕏`{.Agda}
with the paper's equation (1.1) dynamics. A total weight assignment
is a global section of `𝕎`{.Agda}, and the functioning at those
weights is the fiber of `pr₂ : 𝕏 ⇒ 𝕎` over it.

```agda
_ = chain-site
_ = Chain-dynamics.𝕏
_ = Chain-dynamics.pr₂
_ = Chain-dynamics.fiber-over-σ
```

**Thinness and the classifier** (Proposition 1.1 and the $\Omega$
computation of §1.2, chain case). The free category on the chain
graph *is* the finite linear order: paths between layers form a
proposition equivalent to the index ordering. Sieves on a layer are
exactly up-closed families of propositions on the deeper layers —
the honest constructive form of the paper's threshold picture
$(\emptyset, \dots, \star, \dots)$, which is recovered verbatim only
for decidable sieves (over the one-layer chain, sieves form
$\Omega$, not $2$).

```agda
_ = chain-path-is-prop
_ = chain-thin
_ = chain-sieve≃upset
```

## Phase 1, continued: the forked site and its topology

**The forked site** (§1.3 of the paper). A [[network|network-graph]]
is adjacency data from which the paper's graph Γ is *derived*, so
directedness is a theorem and classicality a definition. The forked
graph has typed vertices — ordinary, star, tang — and its edges form
a data family (single-input transmissions, tines, the socket, the
handle), so the arrow inventory the paper gestures at is pattern
matching: nothing leaves a tang, and only tines enter a star.

```agda
_ = network-graph
_ = network-no-loop
_ = fork-site
_ = no-edge-out-of-tang
_ = edge-into-star
```

**The tine coverage** — the branch's first nontrivial
`Coverage`{.Agda}, defined *faithfully* as the coverage generated by
the position-indexed tine families (`from-families`{.Agda}), with
stability — never checked in the paper — proven from the arrow
inventory, and the generated sieves characterised as the nonempty
arrows.

```agda
_ = fork-coverage
_ = into-star-covers
_ = covers-star-is-nonempty
```

**Explicit sheafification** (the paper's §1.3 claim, upgraded to a
theorem with the structural reason isolated): because the site is
free, the tine sieve is *freely* generated, so a patch over it is
exactly a tuple of parts, one per tine. Replacing each star's value
by the product of the input values therefore yields a sheaf, by the
universal property of the product.

```agda
_ = X⋆
_ = X⋆-is-sheaf
```

## What is missing

Next, in order: the unit `X ⇒ X⋆` and the universal property of the
explicit sheafification, with agreement with the HIT `Sheafify`; the
reduction `Sh(C,J) ≃ PSh(C_𝐗)` (Proposition 1.1 in general, and its
corollary); Alexandrov duality for arbitrary posets (Proposition 1.2,
generalized); the tree-structure theorem 1.2; the input–output
relation as `H⁰`; and the discrete backpropagation flow (Theorem 1.1,
reformulated). The threshold description of decidable chain sieves is
stated in prose only; the finite-search equivalence is future work.
The Ran-side Kan extension dualization (`precompose ⊣ Ran`) is
deliberately deferred to its first consumer; over the finite network
sites, direct limits will be finite products.
