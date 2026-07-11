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
open import Neural.Poset.NoLoops
open import Neural.Poset.Reduced
open import Neural.Poset.Thin
open import Neural.Sheaf.StarValue
open import Neural.Topos.Extension
open import Neural.Topos.Equivalence
open import Neural.Network.Activities
open import Neural.Network.Sections
open import Neural.Sheaf.Spontaneous

import Neural.Topos.Quantifiers
import Neural.Topos.Predicates
import Neural.Stack.Grothendieck
import Neural.Stack.Presheaves
import Neural.Stack.Family
import Neural.Stack.Thin

open import Neural.Logic.Hyperdoctrine
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
_ = Neural.Sheaf.Explicit.unit
```

**Proposition 1.1(i), refuted, repaired, and strengthened.** As
literally stated — the reduced category $C_{\mathbf X}$ on non-star
vertices is a poset — the proposition is *false*: in the diamond
network there are two distinct parallel arrows from a tip to the tang
of the fork it feeds, exhibited by `Reduced-not-thin`{.Agda}. The
repair is the paper's own spacelike picture: distinct tips of one
fork must be incomparable in the network. Under `is-spacelike`{.Agda}
we prove more than the paper claims: the *whole* forked site is thin
(every edge type becomes a proposition, and the sixteen-way analysis
of parallel first edges closes using the route classification
`reach`{.Agda} and loop-freeness `no-loop`{.Agda}), antisymmetric by
loop-freeness, hence a poset — with the paper's $\mathbf X$ as the
full subposet on plain vertices.

```agda
_ = Reduced-not-thin
_ = is-spacelike
_ = no-loop
_ = Neural.Poset.Thin.fork-hom-is-prop
_ = Neural.Poset.Thin.fork-poset
_ = Neural.Poset.Thin.reduced-poset
```

**The topos of a DNN** (the corollary of Proposition 1.1, the
headline of chapter 1). A sheaf has no information at a star beyond
the tuple of its tip values — restriction along the tines is an
equivalence (`star-restrict-is-equiv`{.Agda}); presheaves on the
reduced category extend to sheaves (`Ext`{.Agda},
`Ext-is-sheaf`{.Agda}, Proposition 1.1(iii)); and restriction to the
reduced category is fully faithful and split essentially surjective,
hence

$$
\mathrm{Sh}(C, J) \simeq \mathrm{PSh}(C_{\mathbf X})\text{:}
$$

the sheaf topos of a network *is* the presheaf topos on its poset of
layers and joints, with no comparison-lemma machinery — the finite
free structure of the site computes everything.

```agda
_ = star-restrict-is-equiv
_ = Extend.Ext-is-sheaf
_ = Res-is-equivalence
```

**The dynamical object, and the unique-section theorem.** The
presheaf of activities of a general network — transmission along
handles and single-input edges, projections along tines — and the
theorem that gives "computation" its topos-theoretic meaning: global
sections of the dynamical object are exactly tuples of input-layer
activities.

```agda
_ = Network-dynamics.X^
_ = Network-sections.section≃inputs
```

**Spontaneous activity** (§1.5's remark, made concrete): a sheaf on
the diamond network whose tang value admits no equivalence with the
joint input state — the topos contains dynamics that are not
feed-forward.

```agda
_ = spontaneous
```

## Phase 2: the logic of the layers

The Heyting algebra the paper presumes at every object, and the
quantifier strings along morphisms — built at the level of Ω-valued
predicates (natural families of sieves), riding on the sieve
connectives of `Physics.SmoothWorld.Forcing`, with the new
pullback-stability lemmas (including stability of implication).

```agda
_ = Neural.Topos.Predicates.Pred-heyting
_ = Neural.Topos.Quantifiers.∃ᴾ-adj-from
_ = Neural.Topos.Quantifiers.∀ᴾ-adj-to
```

**The hyperdoctrine.** The full first-order signature packaged as a
record — fibred Heyting algebras, substitution as a logical morphism
(the paper's silent hypotheses made fields), and both quantifier
adjoints — inhabited by the Ω-valued predicates over any presheaf
category, with every substitution law holding on the nose.

```agda
_ = Heyting-hyperdoctrine
_ = Pred-hyperdoctrine
```

## Phase 3: stacks over the network

**The thin Grothendieck construction.** The fibrations chapter 3
actually transports logic along have *poset* fibers — propositions
and theories layerwise. For a poset-valued presheaf on any base, the
Grothendieck construction is thinly displayed (a morphism over
$\alpha$ is the inequality $x \le \alpha^\star y$, all coherence
propositional), and reindexing itself provides the cartesian lifts.

```agda
_ = Neural.Stack.Thin.Thin-stack
_ = Neural.Stack.Thin.Thin-stack-fibration
```

**The split Grothendieck construction** (equation 2.2). For a
strictly functorial presheaf of strict categories — the paper's
normative split stacks — the displayed category, total category,
projection, and the canonical cleaving, with every coherence law
closed by a four-lemma transport toolkit over the strict fibre
object sets; and the right-fibration criterion: groupoid fibers make
every morphism cartesian.

```agda
_ = Neural.Stack.Grothendieck.Grothendieck
_ = Neural.Stack.Grothendieck.Grothendieck-fibration
_ = Neural.Stack.Grothendieck.Grothendieck-right-fibration
```

**Compatible families** (equations 2.4–2.6). The category of
fibrewise presheaves with transition maps and cocycle conditions —
the presentation the paper computes in — and the functor exhibiting
each family as a presheaf on the total category.

```agda
_ = Neural.Stack.Family.Families
_ = Neural.Stack.Presheaves.Tot
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
