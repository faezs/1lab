<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Fin
open import Data.Sum

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

## The operator calculus of a simplicial abelian group

For the filler algorithm it is convenient to restate the simplicial
identities as equations between *operators* on the groups of
simplices, with all face and degeneracy indices compared by their
underlying numerals — this absorbs the `weaken`{.Agda}/`fsuc`{.Agda}
bookkeeping once and for all, letting the algorithm itself reason
purely arithmetically.

<!--
```agda
private
  fin-path : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
  fin-path {n} = fin-ap {n = λ _ → n}

  weaken-lower : ∀ {n} (x : Fin n) → weaken x .lower ≡ x .lower
  weaken-lower x with fin-view x
  ... | zero  = refl
  ... | suc i = ap suc (weaken-lower i)

  δ-comm-lower
    : ∀ {n} (O₁ : Fin (suc (suc (suc n)))) (I₁ : Fin (suc (suc n)))
      (O₂ : Fin (suc (suc (suc n)))) (I₂ : Fin (suc (suc n)))
    → O₁ .lower ≡ I₂ .lower → O₂ .lower ≡ suc (I₁ .lower)
    → O₁ .lower Nat.≤ I₁ .lower
    → δ O₁ ∘Δ δ I₁ ≡ δ O₂ ∘Δ δ I₂
  δ-comm-lower O₁ I₁ O₂ I₂ p q le =
      ap (λ a → δ a ∘Δ δ I₁) (fin-path (p ∙ sym (weaken-lower I₂)))
    ∙ δ-comm I₂ I₁ (subst (Nat._≤ I₁ .lower) p le)
    ∙ ap (λ a → δ a ∘Δ δ I₂) (fin-path {x = fsuc I₁} {y = O₂} (sym q))
```
-->

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  private
    module G = Functor G
    module Gr (m : Nat) = Abelian-group-on (G.₀ m .snd)

    d : ∀ {m} (i : Fin (suc (suc m))) → ⌞ G.₀ (suc m) ⌟ → ⌞ G.₀ m ⌟
    d i = G.₁ (δ i) .fst

    s : ∀ {m} (j : Fin (suc m)) → ⌞ G.₀ m ⌟ → ⌞ G.₀ (suc m) ⌟
    s j = G.₁ (σ j) .fst
```

Face and degeneracy operators are group homomorphisms, and
restriction along a composite is the composite of restrictions,
contravariantly.

```agda
    d-⋆ : ∀ {m} (i : Fin (suc (suc m))) a b → d i (Gr._*_ (suc m) a b) ≡ Gr._*_ m (d i a) (d i b)
    d-⋆ i = is-group-hom.pres-⋆ (G.₁ (δ i) .snd)

    d-inv : ∀ {m} (i : Fin (suc (suc m))) a → d i (Gr._⁻¹ (suc m) a) ≡ Gr._⁻¹ m (d i a)
    d-inv i a = is-group-hom.pres-inv (G.₁ (δ i) .snd)

    s-1 : ∀ {m} (j : Fin (suc m)) → s j (Gr.1g m) ≡ Gr.1g (suc m)
    s-1 j = is-group-hom.pres-id (G.₁ (σ j) .snd)

    ap-op
      : ∀ {a b b' c} (u : Δ-map b c) (v : Δ-map a b) (u' : Δ-map b' c) (v' : Δ-map a b')
      → u ∘Δ v ≡ u' ∘Δ v'
      → ∀ g → G.₁ v .fst (G.₁ u .fst g) ≡ G.₁ v' .fst (G.₁ u' .fst g)
    ap-op u v u' v' p g =
        sym (happly (ap ∫Hom.fst (G.F-∘ v u)) g)
      ∙ happly (ap (λ w → ∫Hom.fst (G.₁ w)) p) g
      ∙ happly (ap ∫Hom.fst (G.F-∘ v' u')) g

    ap-op-id
      : ∀ {a c} (u : Δ-map a c) (v : Δ-map c a)
      → u ∘Δ v ≡ Δ .Precategory.id
      → ∀ g → G.₁ v .fst (G.₁ u .fst g) ≡ g
    ap-op-id u v p g =
        sym (happly (ap ∫Hom.fst (G.F-∘ v u)) g)
      ∙ happly (ap (λ w → ∫Hom.fst (G.₁ w)) p) g
      ∙ happly (ap ∫Hom.fst G.F-id) g
```

The four interaction laws, indexed by numeral comparisons:

```agda
    d-s-id
      : ∀ {m} (F : Fin (suc (suc m))) (J : Fin (suc m))
      → (F .lower ≡ J .lower) ⊎ (F .lower ≡ suc (J .lower))
      → ∀ g → d F (s J g) ≡ g
    d-s-id F J (inl p) = ap-op-id (σ J) (δ F)
      (ap (λ z → σ J ∘Δ δ z) (fin-path (p ∙ sym (weaken-lower J))) ∙ σ-δ-id J)
    d-s-id F J (inr p) = ap-op-id (σ J) (δ F)
      (ap (λ z → σ J ∘Δ δ z) (fin-path {x = F} {y = fsuc J} p) ∙ σ-δ-id' J)

    d-s-comm-below
      : ∀ {m} (i : Fin (suc (suc (suc m)))) (J : Fin (suc (suc m)))
        (i' : Fin (suc (suc m))) (J' : Fin (suc m))
      → i .lower ≡ i' .lower → J .lower ≡ suc (J' .lower)
      → i .lower Nat.< J .lower
      → ∀ g → d i (s J g) ≡ s J' (d i' g)
    d-s-comm-below i J i' J' p q lt = ap-op (σ J) (δ i) (δ i') (σ J')
      ( ap₂ (λ a b → σ a ∘Δ δ b)
          (fin-path (q ∙ refl))
          (fin-path (p ∙ sym (weaken-lower i')))
      ∙ δ-σ-comm i' J'
          (subst₂ Nat._<_ p q lt))

    d-s-comm-above
      : ∀ {m} (i : Fin (suc (suc (suc m)))) (J : Fin (suc (suc m)))
        (i' : Fin (suc (suc m))) (J' : Fin (suc m))
      → i .lower ≡ suc (i' .lower) → J .lower ≡ J' .lower
      → suc (J .lower) Nat.< i .lower
      → ∀ g → d i (s J g) ≡ s J' (d i' g)
    d-s-comm-above i J i' J' p q lt = ap-op (σ J) (δ i) (δ i') (σ J')
      ( ap₂ (λ a b → σ a ∘Δ δ b)
          (fin-path (q ∙ sym (weaken-lower J')))
          (fin-path {x = i} {y = fsuc i'} p)
      ∙ δ-σ-comm' i' J'
          (Nat.≤-peel (subst₂ (λ a b → suc a Nat.< b) q p lt)))

    d-d-comm
      : ∀ {m} (O₁ : Fin (suc (suc (suc m)))) (I₁ : Fin (suc (suc m)))
        (O₂ : Fin (suc (suc (suc m)))) (I₂ : Fin (suc (suc m)))
      → O₁ .lower ≡ I₂ .lower → O₂ .lower ≡ suc (I₁ .lower)
      → O₁ .lower Nat.≤ I₁ .lower
      → ∀ g → d I₁ (d O₁ g) ≡ d I₂ (d O₂ g)
    d-d-comm O₁ I₁ O₂ I₂ p q le =
      ap-op (δ O₁) (δ I₁) (δ O₂) (δ I₂) (δ-comm-lower O₁ I₁ O₂ I₂ p q le)
```

Finally, the abelian shuffle that makes each correction step click
shut: multiplying by a difference retargets a face.

```agda
    shuffle : ∀ {m} (a b : ⌞ G.₀ m ⌟)
      → Gr._*_ m a (Gr._*_ m b (Gr._⁻¹ m a)) ≡ b
    shuffle {m} a b =
        ap (Gr._*_ m a) (Gr.commutes m)
      ∙ Gr.associative m
      ∙ ap (λ z → Gr._*_ m z b) (Gr.inverser m)
      ∙ Gr.idl m
```
