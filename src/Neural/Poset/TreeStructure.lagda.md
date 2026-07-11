---
description: |
  Theorem 1.2 of Belfiore–Bennequin: the classification of minimal and
  maximal points of the poset of a DNN, and the tree structure this
  induces — proved edge by edge from the arrow inventory of the forked
  site, with no path induction required.
---

<!--
```agda
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_ ; ∷-head-inj)
open import Data.List.Properties
open import Data.Sum.Base
open import Data.Fin.Base

open import Neural.Graph.Fork

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Poset.TreeStructure where
```

# The tree structure of the poset of a DNN {defines="fork-tree-structure"}

Belfiore–Bennequin's classification of the extremal points of
$\mathbf{X}$ (p.19) reads: *"the minimal elements are of two types:
the outputs layers $x_{n,j}$ and the tips of the forks, i.e. the
points of type $a'$; the maximal elements are also of two types: the
input layers $x_{0,i}$ and the tangs of the forks (i.e. the points
$A$)."* Theorem 1.2 packages this into a shape statement: *"the poset
$\mathbf{X}$ of a DNN is made by a finite number of trees, rooted in
the maximal points and which are joined in the minimal points."*

This module proves the combinatorial content behind both statements,
working with single edges (`F-edge`{.Agda}) rather than paths — the
covering relations of $\mathbf{X}$, not its whole order. Minimality
and maximality of a vertex are properties of the *edges touching it*,
and every one of the arrow-inventory facts below is a short case
analysis on the edge constructor, exactly as the paper's own count of
arrows into and out of each vertex type (p.15–16) is; the difference
is that here the count is a theorem, not a paragraph.

Two book-keeping notions drive the case analysis: a vertex $c$ *feeds
a fork* when it occurs among some fork's inputs (it is a *tip*, type
$a'$, in the paper's vocabulary), and $c$ is *chain-consumed* when
some other vertex takes it as its unique input.

```agda
module _ (N : Network) where
  feeds-fork : Fin (N .size) → Type
  feeds-fork c =
    Σ[ d ∈ Fin (N .size) ] Σ[ f ∈ is-fork N d ]
    Σ[ i ∈ Fin (length (N .inputs d)) ] (N .inputs d ! i ≡ c)

  chain-consumed : Fin (N .size) → Type
  chain-consumed c = Σ[ d ∈ Fin (N .size) ] (N .inputs d ≡ c ∷ [])

  is-input : Fin (N .size) → Type
  is-input c = length (N .inputs c) ≡ 0
```

## Tangs are the sinks, stars have a unique exit

Nothing leaves a tang — this is already `no-edge-out-of-tang`{.Agda}
from [`Neural.Graph.Fork`], the fact that makes tangs maximal. We
simply record it under the name the paper's classification calls for.

[`Neural.Graph.Fork`]: Neural.Graph.Fork.html

```agda
  tang-maximal : ∀ {c f v} → F-edge N (tang c f) v → ⊥
  tang-maximal = no-edge-out-of-tang N
```

Dually, the *only* edge out of a star is its socket — the arrow
inventory of `Neural.Graph.Fork`{.Agda} has exactly one constructor
targeting a `tang` from a `star`, and it fixes the underlying vertex
`c` to be the star's own, leaving only the fork-witness `f'` free.
Since `is-fork`{.Agda} is an inequality of naturals, hence a
proposition, the two candidate exits agree.

```agda
  star-out-unique
    : ∀ {c f} (p q : Σ[ v ∈ F-vtx N ] F-edge N (star c f) v) → p ≡ q
  star-out-unique {c} (_ , socket {f' = f1'}) (_ , socket {f' = f2'}) i =
    tang c (fp i) , socket {f' = fp i}
    where fp = Nat.≤-is-prop f1' f2'
```

## Ordinary vertices: minimal exactly when not chain-consumed

An edge arriving at an `orig`{.Agda} vertex must be a single-input
transmission — `tine`{.Agda} always lands on a `star`{.Agda} and
`socket`{.Agda}/`handle`{.Agda} always land on a `tang`{.Agda}, so
`single`{.Agda} is the only constructor whose target has the shape
`orig c`. Reading off its fields identifies the source and exhibits
$c$ as chain-consumed.

```agda
  into-orig
    : ∀ {v c} → F-edge N v (orig c)
    → Σ[ d ∈ Fin (N .size) ] ((v ≡ orig d) × (N .inputs d ≡ c ∷ []))
  into-orig (single {c = d} q) = d , refl , q
```

So $c$ is minimal (has no incoming edge) whenever it is *not*
chain-consumed, and conversely every chain-consumed vertex fails to be
minimal, the edge witnessing this being the single-input transmission
itself.

```agda
  orig-minimal
    : ∀ {c} → ¬ chain-consumed c → ∀ {v} → F-edge N v (orig c) → ⊥
  orig-minimal ncc e with into-orig e
  ... | d , _ , q = ncc (d , q)

  chain-consumed→not-minimal
    : ∀ {c} → chain-consumed c → Σ[ v ∈ F-vtx N ] F-edge N v (orig c)
  chain-consumed→not-minimal (d , q) = orig d , single q
```

This is the honest form of half the paper's classification: nothing
is said here about tips or outputs, because those are properties of
the *network*, not of the forked site — an `orig` vertex may equally
be an input layer, an output layer, or an internal one, and the site
alone cannot distinguish them. What the site *does* pin down is this
purely structural dichotomy.

## Stars and tangs are never minimal

A fork's star and tang each have at least one incoming edge, so
neither is ever a minimal point of $\mathbf{X}$ — matching the
paper's remark that minimal points are outputs and tips only, never
the fork's own auxiliary vertices. The star's incoming edge is the
tine at the fork's first input position; since `is-fork`{.Agda}
guarantees at least two inputs, position zero is always in range.

```agda
  star-not-minimal
    : ∀ {c} (f : is-fork N c) → Σ[ v ∈ F-vtx N ] F-edge N v (star c f)
  star-not-minimal {c} f = orig (N .inputs c ! i₀) , tine i₀ refl
    where
      0<len : 0 Nat.< length (N .inputs c)
      0<len = Nat.≤-trans Nat.≤-ascend f

      i₀ : Fin (length (N .inputs c))
      i₀ = fin 0 ⦃ 0<len ⦄
```

The tang's incoming edge is its socket, fed from the star of the same
fork — the same `is-fork`{.Agda} witness `f` serves as both the
star's and the tang's fork-witness, since `socket`{.Agda} allows them
to differ but certainly permits them to agree.

```agda
  tang-not-minimal
    : ∀ {c} (f : is-fork N c) → Σ[ v ∈ F-vtx N ] F-edge N v (tang c f)
  tang-not-minimal {c} f = star c f , socket {f' = f}
```

## Ordinary vertices: the exit inventory, and when they are maximal

Three constructors have an `orig c` *source*: `single`{.Agda} (when
$c$ has a unique input), `handle`{.Agda} (when $c$ is a fork, joining
its own tang), and `tine`{.Agda} (when $c$ feeds some other fork —
matching the source `orig c` forces the tine's implicit input-value
to be exactly $c$). Nothing else can leave `orig c`, so every outgoing
edge falls into exactly one of these three cases.

```agda
  orig-out-inventory
    : ∀ {c v} → F-edge N (orig c) v
    → (Σ[ b ∈ Fin (N .size) ] (N .inputs c ≡ b ∷ []))
      ⊎ (is-fork N c) ⊎ (feeds-fork c)
  orig-out-inventory (single {b = b} q)      = inl (b , q)
  orig-out-inventory (handle {f = f})        = inr (inl f)
  orig-out-inventory (tine {c = d} {f = f} i q) = inr (inr (d , f , i , q))
```

Consequently $c$ is maximal (has no outgoing edge) as soon as it is an
input layer (`is-input`{.Agda}, no inputs at all — so no `single`) and
does not feed a fork (kills the `tine` case); the `handle` case is
impossible outright, since a fork needs at least two inputs while an
input layer has none. This is the other half of the paper's
classification — input layers and tangs (`tang-maximal`{.Agda} above)
are maximal — stated for `orig` vertices under the hypotheses that
make the site actually see them as inputs.

```agda
  orig-maximal
    : ∀ {c} → is-input c → ¬ feeds-fork c
    → ∀ {v} → F-edge N (orig c) v → ⊥
  orig-maximal {c} inp nff e with orig-out-inventory e
  ... | inl (b , q)     = Nat.suc≠zero (sym (ap length q) ∙ inp)
  ... | inr (inl f)     = Nat.¬suc≤0 (subst (2 Nat.≤_) inp f)
  ... | inr (inr feeds) = nff feeds
```

## The unique covering successor away from tips

The tree content of Theorem 1.2 is that away from tips (vertices
feeding a fork) every ordinary vertex has *at most one* outgoing
covering edge — branching happens only at tips, exactly the paper's
remark that *"the only possible divergences happen at tips"* (p.20).
We rule out the nine combinations of exit-shapes pairwise: the two
`single` exits agree because their targets' names agree (list
head-injectivity) and the transmission witnesses agree because a list
of vertices is a set; the two `handle` exits agree because
`is-fork`{.Agda} is a proposition; a `single` can never coexist with a
`handle` because a fork needs two inputs while a single-input vertex
has one; and any `tine` exit is excluded outright by the hypothesis
that $c$ does not feed a fork.

```agda
  chain-out-unique
    : ∀ {c} → ¬ feeds-fork c
    → (p q : Σ[ v ∈ F-vtx N ] F-edge N (orig c) v) → p ≡ q
  chain-out-unique {c} nff (_ , single {b = b1} q1) (_ , single {b = b2} q2) i =
    orig (beq i) , single (qpath i)
    where
      beq : b1 ≡ b2
      beq = ∷-head-inj (sym q1 ∙ q2)

      qpath : PathP (λ i → N .inputs c ≡ beq i ∷ []) q1 q2
      qpath = is-prop→pathp (λ i → hlevel 2 (N .inputs c) (beq i ∷ [])) q1 q2

  chain-out-unique nff (_ , single q1) (_ , handle {f = f2}) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (subst (2 Nat.≤_) (ap length q1) f2)))
  chain-out-unique nff (_ , handle {f = f1}) (_ , single q2) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (subst (2 Nat.≤_) (ap length q2) f1)))

  chain-out-unique {c} nff (_ , handle {f = f1}) (_ , handle {f = f2}) i =
    tang c (fp i) , handle {f = fp i}
    where fp = Nat.≤-is-prop f1 f2

  chain-out-unique nff (_ , single q1)      (_ , tine {c = d} {f = f} i q2) =
    absurd (nff (d , f , i , q2))
  chain-out-unique nff (_ , handle {f = f1}) (_ , tine {c = d} {f = f} i q2) =
    absurd (nff (d , f , i , q2))
  chain-out-unique nff (_ , tine {c = d} {f = f} i q1) _ =
    absurd (nff (d , f , i , q1))
```

## Theorem 1.2, packaged

The individual lemmas above are the content; this record only names
the bundle so that "Theorem 1.2" has a single citeable statement.

```agda
  record Theorem-1·2 : Type where
    field
      tangs-maximal      : ∀ {c f v} → F-edge N (tang c f) v → ⊥
      stars-not-minimal  : ∀ {c} (f : is-fork N c)
                          → Σ[ v ∈ F-vtx N ] F-edge N v (star c f)
      tangs-not-minimal  : ∀ {c} (f : is-fork N c)
                          → Σ[ v ∈ F-vtx N ] F-edge N v (tang c f)
      origs-minimal      : ∀ {c} → ¬ chain-consumed c
                          → ∀ {v} → F-edge N v (orig c) → ⊥
      origs-maximal      : ∀ {c} → is-input c → ¬ feeds-fork c
                          → ∀ {v} → F-edge N (orig c) v → ⊥
      unique-star-exit   : ∀ {c f} (p q : Σ[ v ∈ F-vtx N ] F-edge N (star c f) v)
                          → p ≡ q
      unique-chain-exit  : ∀ {c} → ¬ feeds-fork c
                          → (p q : Σ[ v ∈ F-vtx N ] F-edge N (orig c) v) → p ≡ q

  theorem-1·2 : Theorem-1·2
  theorem-1·2 = record
    { tangs-maximal     = tang-maximal
    ; stars-not-minimal = star-not-minimal
    ; tangs-not-minimal = tang-not-minimal
    ; origs-minimal     = orig-minimal
    ; origs-maximal     = orig-maximal
    ; unique-star-exit  = star-out-unique
    ; unique-chain-exit = chain-out-unique
    }
```

## What this is, and is not, honestly

The paper's clean bipartition — minimal points are outputs and tips,
maximal points are inputs and tangs — is stated for the *network's*
distinguished vertices, a piece of data this module does not carry
(the forked site alone cannot tell an input layer from an internal
vertex with no recorded inputs, nor an output layer from an internal
vertex nothing consumes). What holds *unconditionally*, in the
vocabulary of the site alone, is weaker but exact: an ordinary vertex
is minimal iff it is not chain-consumed (`orig-minimal`{.Agda},
`chain-consumed→not-minimal`{.Agda}), and — restricting to vertices
that do not themselves feed a fork — maximal iff it has no single
input (`orig-maximal`{.Agda}, via `is-input`{.Agda}); a vertex that
*does* feed a fork is, in this unsubdivided design, simultaneously a
tip (minimal, in the sense of feeding something) and possibly an
ordinary internal point with its own incoming chain — the paper's
bipartition is recovered exactly on vertices that feed no fork, and
we say so rather than silently assuming subdivision has already
separated tips from everything else.

The forest picture of Theorem 1.2 is then: away from tine edges,
every vertex has out-degree at most one (`star-out-unique`{.Agda} at
stars, `chain-out-unique`{.Agda} at ordinary non-feeding vertices,
and `tang-maximal`{.Agda} — vacuously — at tangs), so following exits
traces a single chain up to a root; tine edges are exactly where a
tip attaches to the star of *every* fork it feeds, joining otherwise
disjoint chains into the "trees rooted in the maximal points and
joined in the minimal points" of the theorem's statement. What is
*not* here: the theorem is proved at the level of covering edges, not
assembled into an explicit finite forest (a well-founded recursion
building the tree from `chain-out-unique`{.Agda} and depth,
terminating by `Neural.Poset.NoLoops`{.Agda}'s loop-freeness) — that
global packaging, and the dual statement about paths rather than
single edges, are left for a successor module.
