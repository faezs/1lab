---
description: |
  Conventions for the formalization of Belfiore and Bennequin's "Topos
  and stacks of deep neural networks": universe policy, arrow
  directions, and the normative modelling choices.
---
<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Neural.Base where
```

# Topos of deep neural networks: conventions {defines="neural-conventions"}

The modules under `Neural.*` formalize the mathematical content of
Belfiore and Bennequin's *Topos and stacks of deep neural networks*
(arXiv:2106.14587v3). The roadmap governing the whole development,
including per-chapter mappings, risks, and explicit skips, lives at the
repository root in `TOPOS-OF-DNNS.md`; this module records the
conventions every `Neural.*` module must follow, so they are stated
once and cited by anchor.

## Normative modelling choices

**Universe policy.** Network sites and their fibers live at `lzero`.
Categories of stacks (`Grpd_C`, the semantic pairs `A_C`) live at
`lsuc lzero` and are never asked to be small. The upstream modules
`Cat.Instances.Presheaf.Omega`, `.Exponentials` and the cohesion stack
pin their site to `Precategory ℓ ℓ`, so everything is kept
one-universe. The open coverage of a frame lands one level up
(`Coverage _ (lsuc o)`), so every Alexandrov or frame-site statement
uses the level-polymorphic `Sheaves` from `Cat.Site.Base`, never the
one-universe `Sh[_,_]` aliases.

**Split and strict is normative.** A *stack* on the network in these
modules is a split, strict-groupoid-valued presheaf: groupoids are
precategories that satisfy `is-pregroupoid`{.Agda}, carved out of
strict categories, and the pseudofunctor coherence is definitional
because the data is split. The homotopy-type reading (families of
1-types over the network poset) is developed separately, for toy
networks only, and is labelled a *reading*: no equivalence between the
two models is claimed anywhere, because no strictification theorem is
available (nor is one in the paper).

**No model structures.** The paper's Quillen-model-category
superstructure is deliberately replaced: fibrancy is stated as explicit
lifting or matching-map conditions (`Cat.Morphism.Lifts`), homotopy
categories are zigzag localisations (`Cat.Instances.Localisation`),
and "ideal semantic flows" are unit-isomorphism conditions on
adjunctions. No weak factorization system is ever postulated to exist
where it is not constructed.

**Zero postulates, inhabited interfaces.** Analytic or unproven inputs
(gate nonlinearities, the semantic-transfer hypotheses, information
space axioms) enter as module parameters or record fields, following
`Physics.SmoothWorld`. Every such hypothesis record must ship at least
one nontrivial inhabitant in the module that introduces it, so no
layer of the development is conditional on an interface that could be
empty.

**The golden thread.** The three-layer chain network with finite
fibers (`Neural.Chain`) instantiates every construction — site,
topology, sheafification, subobject classifier, stack, transfer, flow
— before that construction is generalized. It is the permanent
regression test of the development.

## Arrow directions

The single most error-prone convention in the paper: for a network
graph $\Gamma$ (arrows in the direction of information flow, inputs at
the bottom), the associated *site* $C$ is the **opposite** of the free
category on $\Gamma$, so arrows of $C$ run **from deeper layers back
toward the input**; presheaves on $C$ therefore transport activities
*forward* through the network. Every `Neural.*` module states which
direction its arrows run, in prose, at the point of definition, and
names functors so that `X.F₁` acting on a site arrow is forward
propagation.

## Known landmines

Identifier- and universe-level facts, verified against this tree, that
cost a debugging round when hit cold:

- `Cartesian-closed` lives in `Cat.Diagram.Exponential`, not in any
  `Cat.CartesianClosed.Base`.
- The fundamental pregroupoid `Π₁` of a type already exists as
  `Cat.Instances.Discrete.Pre`; extend it, do not rebuild it. Set
  truncation is `Data.Set.Truncation`.
- The Kan-extension layer is left-biased: `Lan⊣precompose` exists,
  `precompose ⊣ Ran` does not; the right-handed statements must be
  produced by op-duality (`Cat.Functor.Kan.Duality`) or, over finite
  sites, built directly as finite products.
- `is-heyting-algebra`{.Agda} demands joins and a bottom (a full
  lattice) — strictly more than a closed monoidal poset. The first
  inhabitants in this development are in `Neural.Order.FrameHeyting`.
- `⋃ˢ` (subset joins) is `opaque`; proofs about it either use its
  universal property or must say `opaque unfolding ⋃ˢ`.
- The simplicial stack (`Cat.Instances.SimplicialSets`, Dold–Kan) is
  pinned to `lzero` with set-level objects; categorical cohomology in
  `Neural.*` uses chains of composable arrows, not simplicial sets.
- 1lab's `Cartesian-fibration` is a *cleaving*: a function assigning
  chosen lifts, not a mere existence statement.
- `prop→is-subterminal-PSh` (note the `is-`) in
  `Cat.Instances.Presheaf.Limits`, whose `clo⊣ev` is the *left*
  adjoint to evaluation only.
```
