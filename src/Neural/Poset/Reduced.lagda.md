---
description: |
  The reduced category of a forked DNN site — the full subcategory on
  non-star vertices — together with a machine-checked counterexample
  showing that Belfiore–Bennequin's Proposition 1.1(i) requires the
  tips of each fork to be spacelike, and the definition of that
  hypothesis.
---
<!--
```agda
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_)
open import Data.Fin.Base

open import Neural.Graph.Fork

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Poset.Reduced where
```

# The reduced category of a network {defines="reduced-category spacelike"}

Proposition 1.1 of Belfiore–Bennequin asserts that the full
subcategory $C_{\mathbf X}$ of the forked site on the vertices that
are *not* stars is a poset. Its objects are the original network
vertices together with the tang vertices $A_c$; the claim is that
between any two of them there is at most one arrow, and that the
resulting preorder is antisymmetric.

```agda
is-plain : ∀ {N} → F-vtx N → Type
is-plain (orig c)   = ⊤
is-plain (star c f) = ⊥
is-plain (tang c f) = ⊤

Reduced : Network → Precategory lzero lzero
Reduced N = Restrict {C = fork-site N} is-plain
```

## The counterexample

As stated, with the site the *free* category on the forked graph,
the proposition is **false**. Take the diamond network: an input
$x$, a vertex $y$ with input $x$, and a fork $c$ with inputs $y$ and
$x$. Then there are two *distinct* parallel arrows $y \to A_c$ in
the reduced category: through $y$'s own tine, and down the single
edge to $x$ and through $x$'s tine.

The paper's prose proof ("a tip cannot diverge to two ordinary
vertices, else a fork would exist") silently excludes this
configuration: it assumes that distinct tips of one fork are never
comparable in the network — in the language of the paper's own §4.1,
that the inputs of each join form a *spacelike* family. The
counterexample below is a machine-checked witness that some such
hypothesis is necessary; the repaired proposition, for spacelike
classical networks, is the positive result this module's successors
prove.

```agda
private
  diamond-inputs : Fin 3 → List (Fin 3)
  diamond-inputs (fin 0)                       = []
  diamond-inputs (fin 1)                       = fin 0 ∷ []
  diamond-inputs (fin 2)                       = fin 1 ∷ fin 0 ∷ []
  diamond-inputs (fin (suc (suc (suc k))) ⦃ b ⦄) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel (Nat.≤-peel b))))

  diamond-depth-<
    : ∀ c (i : Fin (length (diamond-inputs c)))
    → (diamond-inputs c ! i) .lower Nat.< c .lower
  diamond-depth-< (fin 0) i = absurd (Nat.¬suc≤0 (Fin.bounded i))
  diamond-depth-< (fin 1) (fin 0) = Nat.s≤s Nat.0≤x
  diamond-depth-< (fin 1) (fin (suc k) ⦃ b ⦄) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel b))
  diamond-depth-< (fin 2) (fin 0) = Nat.s≤s (Nat.s≤s Nat.0≤x)
  diamond-depth-< (fin 2) (fin 1) = Nat.s≤s Nat.0≤x
  diamond-depth-< (fin 2) (fin (suc (suc k)) ⦃ b ⦄) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
  diamond-depth-< (fin (suc (suc (suc k))) ⦃ b ⦄) i =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel (Nat.≤-peel b))))

diamond : Network
diamond .size    = 3
diamond .inputs  = diamond-inputs
diamond .depth v = v .lower
diamond .depth-< = diamond-depth-<

private
  c-fork : is-fork diamond (fin 2)
  c-fork = Nat.s≤s (Nat.s≤s Nat.0≤x)

  Γd = fork-graph diamond

  route-tine : Path-in Γd (orig (fin 1)) (tang (fin 2) c-fork)
  route-tine =
    cons (tine {f = c-fork} fzero refl)
      (cons (socket {f = c-fork} {f' = c-fork}) nil)

  route-single : Path-in Γd (orig (fin 1)) (tang (fin 2) c-fork)
  route-single =
    cons (single refl)
      (cons (tine {f = c-fork} (fsuc fzero) refl)
        (cons (socket {f = c-fork} {f' = c-fork}) nil))

  path-length : ∀ {v u} → Path-in Γd v u → Nat
  path-length nil        = 0
  path-length (cons _ p) = suc (path-length p)

  routes-differ : route-tine ≡ route-single → ⊥
  routes-differ e = Nat.zero≠suc (Nat.suc-inj (Nat.suc-inj (ap path-length e)))
```

Both endpoints are plain vertices, so these are two distinct
elements of a hom-set of the reduced category:

```agda
Reduced-not-thin
  : ¬ (∀ {x y} → is-prop (Precategory.Hom (Reduced diamond) x y))
Reduced-not-thin thin = routes-differ
  (thin {orig (fin 1) , tt} {tang (fin 2) c-fork , tt}
    route-tine route-single)
```

## The spacelike hypothesis

The repaired hypothesis: a network is **spacelike** when distinct
tips of one fork are unreachable from one another in the underlying
graph — no directed path of the network connects two inputs of the
same join, and no input appears twice (the latter is
[[classicality|network-graph]] at the fork). This is exactly the
paper's picture of the inputs of a join as a "spatial section" of
the network at one time: for the concrete architectures of chapter 4
(chains, RNN lattices, LSTMs) it holds by construction.

```agda
record is-spacelike (N : Network) : Type where
  field
    tips-incomparable
      : ∀ (c : Fin (N .size)) (i j : Fin (length (N .inputs c)))
      → Path-in (network-graph N) (N .inputs c ! i) (N .inputs c ! j)
      → i ≡ j

open is-spacelike public
```

Note that `tips-incomparable`{.Agda} subsumes both conditions: a
duplicated input gives a `nil`{.Agda} path between distinct
positions, and a directed path between distinct tips is likewise
ruled out. Under this hypothesis (and only under it), the successors
of this module prove Proposition 1.1: hom-sets of the reduced
category are propositions, the resulting preorder is antisymmetric,
and $C_{\mathbf X}$ is the poset the paper works with.
