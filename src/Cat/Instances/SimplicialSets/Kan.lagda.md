<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Prelude

open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Fin

import Data.Nat as Nat

open Δ-map
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.SimplicialSets.Kan where
```

# Simplicial abelian groups are Kan complexes

This module proves Moore's theorem: the underlying [[simplicial
set|simplicial-set]] of any [[simplicial abelian
group|simplicial-abelian-group]] satisfies the [[Kan
condition|kan-condition]]. Every horn admits a filler, built
explicitly from the group structure by a two-pass correction
algorithm — no choice, no fibrant replacement. The
[[Eilenberg–MacLane objects|eilenberg-maclane-object]] $K(A,n)$ are
simplicial abelian groups, so this establishes their fibrancy, the
missing homotopical ingredient of the paper's diagram (31).

## Two missing combinatorial lemmas

The [[simplex category]] module records the simplicial identities for
moving a face past a degeneracy when the face index is *at most* the
degeneracy index. The Moore filler's descending pass also moves faces
past degeneracies from *above*, so we first prove the far-side
commutation $\sigma_j \delta_i = \delta_{i-1} \sigma_j$ for $i > j +
1$, at the level of `skip`{.Agda} and `squish`{.Agda} and then of
$\Delta$. We keep these local rather than touching the base modules.

```agda
private
  squish-skip-comm'
    : ∀ {n} (i : Fin (suc (suc n))) (j : Fin (suc n)) → fsuc j ≤ i
    → ∀ x → squish (weaken j) (skip (fsuc i) x) ≡ skip i (squish j x)
  squish-skip-comm' {zero} i j le x with fin-view i | fin-view j | le | fin-view x
  ... | zero   | _      | le | _      = absurd (Nat.¬suc≤0 le)
  ... | suc i' | zero   | le | zero   = refl
  ... | suc i' | zero   | le | suc x' = refl
  ... | suc i' | suc j' | le | _      = absurd (Nat.¬suc≤0 (j' .Fin.bounded))
  squish-skip-comm' {suc m} i j le x with fin-view i | fin-view j | le | fin-view x
  ... | zero   | _      | le | _      = absurd (Nat.¬suc≤0 le)
  ... | suc i' | zero   | le | zero   = refl
  ... | suc i' | zero   | le | suc x' = refl
  ... | suc i' | suc j' | le | zero   = refl
  ... | suc i' | suc j' | le | suc x' =
    ap fsuc (squish-skip-comm' i' j' (Nat.≤-peel le) x')

  avoid-monotone
    : ∀ {n} (i : Fin (suc n)) (x y : Fin (suc n)) {ix : ¬ i ≡ x} {iy : ¬ i ≡ y}
    → x ≤ y → avoid i x ix ≤ avoid i y iy
  avoid-monotone {zero} i x y {ix} {iy} le with fin-view i | fin-view x
  ... | zero   | zero   = absurd (ix refl)
  ... | zero   | suc x' = absurd (Nat.¬suc≤0 (x' .Fin.bounded))
  ... | suc i' | _      = absurd (Nat.¬suc≤0 (i' .Fin.bounded))
  avoid-monotone {suc m} i x y {ix} {iy} le with fin-view i | fin-view x | fin-view y | le
  ... | zero   | zero   | _      | _  = absurd (ix refl)
  ... | zero   | suc x' | zero   | le = absurd (Nat.¬suc≤0 le)
  ... | zero   | suc x' | suc y' | le = Nat.≤-peel le
  ... | suc i' | zero   | zero   | _  = Nat.0≤x
  ... | suc i' | zero   | suc y' | _  = Nat.0≤x
  ... | suc i' | suc x' | zero   | le = absurd (Nat.¬suc≤0 le)
  ... | suc i' | suc x' | suc y' | le =
    Nat.s≤s (avoid-monotone i' x' y' (Nat.≤-peel le))
```

The far-side commutation of a coface past a codegeneracy, as an
equation in $\Delta$:

```agda
δ-σ-comm'
  : ∀ {n} (i : Fin (suc (suc n))) (j : Fin (suc n)) → fsuc j ≤ i
  → σ (weaken j) ∘Δ δ (fsuc i) ≡ δ i ∘Δ σ j
δ-σ-comm' i j le = Δ-map-path (squish-skip-comm' i j le)
```

## Factoring a map that misses a vertex

A map $f : [l] \to [n+1]$ in $\Delta$ whose image avoids the vertex
$j$ factors through the $j$-th coface, by re-indexing every value
past the hole. This is the combinatorial heart of horn filling: an
$l$-simplex of the horn $\Lambda^n_k$ misses some vertex $j \neq k$,
so it is the image of an $l$-simplex of the $j$-th face.

```agda
Δ-unskip
  : ∀ {l n} (j : Fin (suc (suc n))) (f : Δ-map l (suc n))
  → (∀ x → ¬ f .map x ≡ j)
  → Δ-map l n
Δ-unskip j f miss .map x = avoid j (f .map x) λ p → miss x (sym p)
Δ-unskip j f miss .ascending x y le =
  avoid-monotone j (f .map x) (f .map y) (f .ascending x y le)

Δ-unskip-factor
  : ∀ {l n} (j : Fin (suc (suc n))) (f : Δ-map l (suc n))
  → (miss : ∀ x → ¬ f .map x ≡ j)
  → δ j ∘Δ Δ-unskip j f miss ≡ f
Δ-unskip-factor j f miss = Δ-map-path λ x →
  skip-avoid j (f .map x) {λ p → miss x (sym p)}
```

Conversely, the $i$-th coface itself is a horn simplex for every horn
that does not remove the $i$-th face, since `skip`{.Agda} misses $i$.

```agda
δ-is-horn
  : ∀ {n} (k i : Fin (suc (suc n))) → ¬ i ≡ k
  → is-horn {n} {suc n} k (δ i)
δ-is-horn k i i≠k = inc (i , i≠k , λ x → skip-skips i x)
```
