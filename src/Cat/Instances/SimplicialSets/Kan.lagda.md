<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Diagram.Exponential
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan

open import Data.Set.Coequaliser
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

## From horns to faces

A natural transformation out of a horn is determined by where it
sends the top-dimensional faces $\delta_i$ ($i \neq k$), since every
horn simplex misses a vertex and hence factors through one of them.
We now extract those faces, show that *all* their compatibilities
follow from one naturality lemma, and reduce the Kan condition to
producing a single group element with prescribed faces.

```agda
  private
    yo-b : ∀ {n} → ⌞ G.₀ n ⌟ → Δ[ n ] => (Ab↪Sets F∘ G)
    yo-b b .η l f = G.₁ f .fst b
    yo-b b .is-natural l l' g = funext λ f →
      happly (ap ∫Hom.fst (G.F-∘ g f)) b

    module sSet = Cat.Reasoning sSet

  module Fill {m : Nat} (k : Fin (suc (suc m)))
              (α : Λ[ suc m , k ] => (Ab↪Sets F∘ G)) where
    x : (i : Fin (suc (suc m))) (i≠k : ¬ i ≡ k) → ⌞ G.₀ m ⌟
    x i i≠k = α .η m (δ i , δ-is-horn k i i≠k)

    x-eq
      : ∀ {i j} (p : i ≡ j) (i≠k : ¬ i ≡ k) (j≠k : ¬ j ≡ k)
      → x i i≠k ≡ x j j≠k
    x-eq p i≠k j≠k = ap (α .η m) (Σ-prop-path (λ f → hlevel 1) (ap δ p))

    x-natural
      : ∀ {l} (a b : Fin (suc (suc m))) (a≠k : ¬ a ≡ k) (b≠k : ¬ b ≡ k)
        (u : Δ-map l m) (v : Δ-map l m)
      → δ a ∘Δ u ≡ δ b ∘Δ v
      → G.₁ u .fst (x a a≠k) ≡ G.₁ v .fst (x b b≠k)
    x-natural {l} a b a≠k b≠k u v p =
        sym (happly (α .is-natural m l u) (δ a , δ-is-horn k a a≠k))
      ∙ ap (α .η l) (Σ-prop-path (λ f → hlevel 1) p)
      ∙ happly (α .is-natural m l v) (δ b , δ-is-horn k b b≠k)

    extend
      : (b : ⌞ G.₀ (suc m) ⌟)
      → (∀ i (i≠k : ¬ i ≡ k) → d i b ≡ x i i≠k)
      → ∃[ β ∈ (Δ[ suc m ] => (Ab↪Sets F∘ G)) ]
          (β sSet.∘ horn-inclusion (suc m) k ≡ α)
    extend b faces = inc (yo-b b , ext-p)
      where
      ext-p : yo-b b sSet.∘ horn-inclusion (suc m) k ≡ α
      ext-p = Nat-path λ l → funext λ where
        (f , h) → ∥-∥-rec (G.₀ l .fst .is-tr _ _)
          (λ (j , j≠k , miss) →
            let
              f'  = Δ-unskip j f miss
              fac = Δ-unskip-factor j f miss
            in
              ap (λ w → G.₁ w .fst b) (sym fac)
            ∙ happly (ap ∫Hom.fst (G.F-∘ f' (δ j))) b
            ∙ ap (G.₁ f' .fst) (faces j j≠k)
            ∙ sym (happly (α .is-natural m l f') (δ j , δ-is-horn k j j≠k))
            ∙ ap (α .η l) (Σ-prop-path (λ g → hlevel 1) fac))
          h
```

## The Moore filler

The faces are filled by Moore's two-pass correction algorithm.
Starting from the group unit, the ascending pass walks the faces
below $k$ from the bottom, at each step multiplying by a degenerate
correction $s_j\!\left(x_j \cdot (d_j g)^{-1}\right)$ that fixes face
$j$; the descending pass then walks the faces above $k$ from the
top, correcting with $s_{j-1}$ instead. Fixing is the unit law
$d_j s_j = \mathrm{id}$ (or $d_j s_{j-1} = \mathrm{id}$), and the
previously-fixed faces are undisturbed because the correction's
argument restricts to zero — an interplay of the commutation laws
above with the compatibilities extracted from the horn.

<!--
```agda
  private
    ¬sucx≤x : ∀ {x} → ¬ (suc x Nat.≤ x)
    ¬sucx≤x {zero}  le = Nat.¬suc≤0 le
    ¬sucx≤x {suc x} le = ¬sucx≤x (Nat.≤-peel le)

    le0 : ∀ {x} → x Nat.≤ 0 → x ≡ 0
    le0 {zero}  _  = refl
    le0 {suc x} le = absurd (Nat.¬suc≤0 le)

    ≤1-split : ∀ (x : Nat) → x Nat.≤ 1 → (x ≡ 0) ⊎ (x ≡ 1)
    ≤1-split zero    _  = inl refl
    ≤1-split (suc x) le = inr (ap suc (le0 (Nat.≤-peel le)))

    plus-monus : ∀ a b → a Nat.≤ b → a Nat.+ (b Nat.- a) ≡ b
    plus-monus zero    b       _  = refl
    plus-monus (suc a) zero    le = absurd (Nat.¬suc≤0 le)
    plus-monus (suc a) (suc b) le = ap suc (plus-monus a b (Nat.≤-peel le))

    le-plus : ∀ x y → x Nat.≤ x Nat.+ y
    le-plus zero    y = Nat.0≤x
    le-plus (suc x) y = Nat.s≤s (le-plus x y)

    pred-fin
      : ∀ {n} (F : Fin (suc n)) → 0 Nat.< F .lower
      → Σ[ P ∈ Fin n ] (F .lower ≡ suc (P .lower))
    pred-fin {n} F pos = go (F .lower) (F .Fin.bounded) pos
      where
      go : (l : Nat) → l Nat.< suc n → 0 Nat.< l → Σ[ P ∈ Fin n ] (l ≡ suc (P .lower))
      go zero    _  p = absurd (Nat.¬suc≤0 p)
      go (suc l) bd _ = fin l ⦃ Nat.≤-peel bd ⦄ , refl
```
-->

```agda
  sab-is-kan : is-kan (Ab↪Sets F∘ G)
```

Horns of $\Delta^0$ are empty, so any vertex fills them.

```agda
  sab-is-kan {zero} k α = inc (yo-b (Gr.1g zero) , Nat-path λ l → funext λ where
    (f , h) → absurd (∥-∥-rec (hlevel 1)
      (λ (j , j≠k , _) → j≠k (fin-path
        ( le0 (Nat.≤-peel (j .Fin.bounded))
        ∙ sym (le0 (Nat.≤-peel (k .Fin.bounded))))))
      h))
```

A horn of $\Delta^1$ has a single face — the vertex opposite $k$ —
and a degeneracy of that vertex fills it.

```agda
  sab-is-kan {suc zero} k α with fin-view k
  ... | zero = extend b faces
    where
    open Fill k α
    o≠k : ¬ fsuc fzero ≡ k
    o≠k p = Nat.suc≠zero (ap lower p)
    b = s fzero (x (fsuc fzero) o≠k)
    faces : ∀ i (i≠k : ¬ i ≡ k) → d i b ≡ x i i≠k
    faces i i≠k with ≤1-split (i .lower) (Nat.≤-peel (i .Fin.bounded))
    ... | inl p0 = absurd (i≠k (fin-path p0))
    ... | inr p1 =
        d-s-id i fzero (inr p1) (x (fsuc fzero) o≠k)
      ∙ x-eq (fin-path {x = fsuc fzero} {y = i} (sym p1)) o≠k i≠k
  ... | suc k' = extend b faces
    where
    open Fill k α
    o≠k : ¬ fzero ≡ k
    o≠k p = Nat.zero≠suc (ap lower p)
    b = s fzero (x fzero o≠k)
    faces : ∀ i (i≠k : ¬ i ≡ k) → d i b ≡ x i i≠k
    faces i i≠k with ≤1-split (i .lower) (Nat.≤-peel (i .Fin.bounded))
    ... | inl p0 =
        d-s-id i fzero (inl p0) (x fzero o≠k)
      ∙ x-eq (fin-path {x = fzero} {y = i} (sym p0)) o≠k i≠k
    ... | inr p1 = absurd (i≠k (fin-path
      (p1 ∙ sym (ap suc (le0 (Nat.≤-peel (k' .Fin.bounded)))))))
```

For horns of dimension at least two, the passes run in earnest. The
correction combinator and its two verification lemmas — a fixed face
stays fixed whether approached from below or from above — are shared
between the passes.

```agda
  sab-is-kan {suc (suc m₀)} k α = extend b faces
    where
    open Fill k α

    kb : k .lower Nat.≤ suc (suc m₀)
    kb = Nat.≤-peel (k .Fin.bounded)

    corr
      : (F : Fin (suc (suc (suc m₀)))) (J : Fin (suc (suc m₀)))
        (F≠k : ¬ F ≡ k)
      → ⌞ G.₀ (suc (suc m₀)) ⌟ → ⌞ G.₀ (suc (suc m₀)) ⌟
    corr F J F≠k g =
      Gr._*_ (suc (suc m₀)) g
        (s J (Gr._*_ (suc m₀) (x F F≠k) (Gr._⁻¹ (suc m₀) (d F g))))

    corr-fix
      : ∀ F J (F≠k : ¬ F ≡ k)
      → ((F .lower ≡ J .lower) ⊎ (F .lower ≡ suc (J .lower)))
      → ∀ g → d F (corr F J F≠k g) ≡ x F F≠k
    corr-fix F J F≠k side g =
        d-⋆ F g _
      ∙ ap (Gr._*_ (suc m₀) (d F g)) (d-s-id F J side _)
      ∙ shuffle (d F g) (x F F≠k)

    pres-low
      : (F : Fin (suc (suc (suc m₀)))) (J : Fin (suc (suc m₀)))
        (F≠k : ¬ F ≡ k) (g : ⌞ G.₀ (suc (suc m₀)) ⌟)
      → ∀ i (i≠k : ¬ i ≡ k)
      → i .lower Nat.< J .lower
      → i .lower Nat.< F .lower
      → i .lower Nat.< suc (suc m₀)
      → d i g ≡ x i i≠k
      → d i (corr F J F≠k g) ≡ x i i≠k
    pres-low F J F≠k g i i≠k iJ iF ib val =
        d-⋆ i g _
      ∙ ap (Gr._*_ (suc m₀) (d i g))
          ( d-s-comm-below i J i' J₁ refl pJ iJ _
          ∙ ap (s J₁)
              ( d-⋆ i' (x F F≠k) _
              ∙ ap₂ (Gr._*_ m₀) tv
                  (d-inv i' (d F g) ∙ ap (Gr._⁻¹ m₀) (ddv ∙ ap (d Fp) val))
              ∙ Gr.inverser m₀ )
          ∙ s-1 J₁ )
      ∙ Gr.idr (suc m₀)
      ∙ val
      where
      i' : Fin (suc (suc m₀))
      i' = fin (i .lower) ⦃ ib ⦄
      J₁ : Fin (suc m₀)
      J₁ = pred-fin J (Nat.≤-trans (Nat.s≤s Nat.0≤x) iJ) .fst
      pJ : J .lower ≡ suc (J₁ .lower)
      pJ = pred-fin J (Nat.≤-trans (Nat.s≤s Nat.0≤x) iJ) .snd
      Fp : Fin (suc (suc m₀))
      Fp = pred-fin F (Nat.≤-trans (Nat.s≤s Nat.0≤x) iF) .fst
      pF : F .lower ≡ suc (Fp .lower)
      pF = pred-fin F (Nat.≤-trans (Nat.s≤s Nat.0≤x) iF) .snd
      le' : i .lower Nat.≤ Fp .lower
      le' = Nat.≤-peel (subst (suc (i .lower) Nat.≤_) pF iF)
      tv : d i' (x F F≠k) ≡ d Fp (x i i≠k)
      tv = x-natural F i F≠k i≠k (δ i') (δ Fp)
             (sym (δ-comm-lower i Fp F i' refl pF le'))
      ddv : d i' (d F g) ≡ d Fp (d i g)
      ddv = sym (d-d-comm i Fp F i' refl pF le' g)

    pres-high
      : (F : Fin (suc (suc (suc m₀)))) (J : Fin (suc (suc m₀)))
        (F≠k : ¬ F ≡ k) (g : ⌞ G.₀ (suc (suc m₀)) ⌟)
      → ∀ i (i≠k : ¬ i ≡ k)
      → suc (J .lower) Nat.< i .lower
      → F .lower Nat.< i .lower
      → d i g ≡ x i i≠k
      → d i (corr F J F≠k g) ≡ x i i≠k
    pres-high F J F≠k g i i≠k JJi Fi val =
        d-⋆ i g _
      ∙ ap (Gr._*_ (suc m₀) (d i g))
          ( d-s-comm-above i J i₁ Jd pi refl JJi _
          ∙ ap (s Jd)
              ( d-⋆ i₁ (x F F≠k) _
              ∙ ap₂ (Gr._*_ m₀) tv
                  (d-inv i₁ (d F g) ∙ ap (Gr._⁻¹ m₀) (ddv ∙ ap (d I₂x) val))
              ∙ Gr.inverser m₀ )
          ∙ s-1 Jd )
      ∙ Gr.idr (suc m₀)
      ∙ val
      where
      i₁ : Fin (suc (suc m₀))
      i₁ = pred-fin i (Nat.≤-trans (Nat.s≤s Nat.0≤x) Fi) .fst
      pi : i .lower ≡ suc (i₁ .lower)
      pi = pred-fin i (Nat.≤-trans (Nat.s≤s Nat.0≤x) Fi) .snd
      I₂x : Fin (suc (suc m₀))
      I₂x = fin (F .lower) ⦃ Nat.≤-trans Fi (Nat.≤-peel (i .Fin.bounded)) ⦄
      Jd : Fin (suc m₀)
      Jd = fin (J .lower)
        ⦃ Nat.≤-peel (Nat.≤-trans JJi (Nat.≤-peel (i .Fin.bounded))) ⦄
      le' : F .lower Nat.≤ i₁ .lower
      le' = Nat.≤-peel (subst (suc (F .lower) Nat.≤_) pi Fi)
      tv : d i₁ (x F F≠k) ≡ d I₂x (x i i≠k)
      tv = x-natural F i F≠k i≠k (δ i₁) (δ I₂x)
             (δ-comm-lower F i₁ i I₂x refl pi le')
      ddv : d i₁ (d F g) ≡ d I₂x (d i g)
      ddv = d-d-comm F i₁ i I₂x refl pi le' g
```

The ascending pass.

```agda
    asc : (c : Nat) → c Nat.≤ k .lower
        → Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
            (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< c → d i g ≡ x i i≠k)
    asc zero _ = Gr.1g (suc (suc m₀)) , λ i i≠k lt → absurd (Nat.¬suc≤0 lt)
    asc (suc c) le = step (asc c (Nat.≤-trans Nat.≤-ascend le))
      where
      bJ : suc c Nat.≤ suc (suc m₀)
      bJ = Nat.≤-trans le kb
      Ff : Fin (suc (suc (suc m₀)))
      Ff = fin c ⦃ Nat.≤-sucr bJ ⦄
      Jf : Fin (suc (suc m₀))
      Jf = fin c ⦃ bJ ⦄
      F≠k : ¬ Ff ≡ k
      F≠k p = ¬sucx≤x (subst (λ z → suc c Nat.≤ z) (sym (ap lower p)) le)

      step
        : Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
            (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< c → d i g ≡ x i i≠k)
        → Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
            (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< suc c → d i g ≡ x i i≠k)
      step (g , fix) = corr Ff Jf F≠k g , fix'
        where
        fix' : ∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< suc c
             → d i (corr Ff Jf F≠k g) ≡ x i i≠k
        fix' i i≠k lt with Nat.≤-split (i .lower) c
        ... | inl i<c = pres-low Ff Jf F≠k g i i≠k i<c i<c
              (Nat.≤-trans i<c (Nat.≤-trans (Nat.<-weaken le) kb))
              (fix i i≠k i<c)
        ... | inr (inl c<i) = absurd (¬sucx≤x (Nat.≤-trans c<i (Nat.≤-peel lt)))
        ... | inr (inr i≡c) =
            ap (λ z → d z (corr Ff Jf F≠k g)) (fin-path {x = i} {y = Ff} i≡c)
          ∙ corr-fix Ff Jf F≠k (inl refl) g
          ∙ x-eq (fin-path {x = Ff} {y = i} (sym i≡c)) F≠k i≠k
```

The descending pass, running on fuel from the top face down to the
face just above $k$.

```agda
    desc : (fuel c : Nat) → c Nat.+ fuel ≡ suc (suc (suc m₀))
         → k .lower Nat.< c
         → Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
             ( (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< k .lower → d i g ≡ x i i≠k)
             × (∀ i (i≠k : ¬ i ≡ k) → c Nat.≤ i .lower → d i g ≡ x i i≠k))
    desc zero c eq k<c =
        asc (k .lower) Nat.≤-refl .fst
      , asc (k .lower) Nat.≤-refl .snd
      , λ i i≠k ge → absurd (¬sucx≤x (Nat.≤-trans (i .Fin.bounded)
          (subst (Nat._≤ i .lower) (sym (Nat.+-zeror c) ∙ eq) ge)))
    desc (suc fuel) zero eq k<c = absurd (Nat.¬suc≤0 k<c)
    desc (suc fuel) (suc c₀) eq k<c = step (desc fuel (suc (suc c₀))
        (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.≤-sucr k<c))
      where
      bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
      bF = subst (suc (suc c₀) Nat.≤_)
             (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
             (Nat.s≤s (le-plus (suc c₀) fuel))
      Ff : Fin (suc (suc (suc m₀)))
      Ff = fin (suc c₀) ⦃ bF ⦄
      Jf : Fin (suc (suc m₀))
      Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄
      F≠k : ¬ Ff ≡ k
      F≠k p = ¬sucx≤x (subst (λ z → suc (k .lower) Nat.≤ z) (ap lower p) k<c)

      step
        : Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
            ( (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< k .lower → d i g ≡ x i i≠k)
            × (∀ i (i≠k : ¬ i ≡ k) → suc (suc c₀) Nat.≤ i .lower → d i g ≡ x i i≠k))
        → Σ[ g ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
            ( (∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< k .lower → d i g ≡ x i i≠k)
            × (∀ i (i≠k : ¬ i ≡ k) → suc c₀ Nat.≤ i .lower → d i g ≡ x i i≠k))
      step (g , bel , abv) = corr Ff Jf F≠k g , bel' , abv'
        where
        bel' : ∀ i (i≠k : ¬ i ≡ k) → i .lower Nat.< k .lower
             → d i (corr Ff Jf F≠k g) ≡ x i i≠k
        bel' i i≠k i<k = pres-low Ff Jf F≠k g i i≠k
          (Nat.≤-trans i<k (Nat.≤-peel k<c))
          (Nat.≤-sucr (Nat.≤-trans i<k (Nat.≤-peel k<c)))
          (Nat.≤-trans i<k kb)
          (bel i i≠k i<k)
        abv' : ∀ i (i≠k : ¬ i ≡ k) → suc c₀ Nat.≤ i .lower
             → d i (corr Ff Jf F≠k g) ≡ x i i≠k
        abv' i i≠k ge with Nat.≤-split (i .lower) (suc c₀)
        ... | inl lt = absurd (¬sucx≤x (Nat.≤-trans lt ge))
        ... | inr (inl gt) = pres-high Ff Jf F≠k g i i≠k gt gt (abv i i≠k gt)
        ... | inr (inr i≡F) =
            ap (λ z → d z (corr Ff Jf F≠k g)) (fin-path {x = i} {y = Ff} i≡F)
          ∙ corr-fix Ff Jf F≠k (inr refl) g
          ∙ x-eq (fin-path {x = Ff} {y = i} (sym i≡F)) F≠k i≠k
```

Assembling the passes: run the descent down to $k + 1$, and read off
all the faces by trichotomy.

```agda
    filled = desc (suc (suc (suc m₀)) Nat.- suc (k .lower)) (suc (k .lower))
      (plus-monus (suc (k .lower)) (suc (suc (suc m₀))) (Nat.s≤s kb))
      Nat.≤-refl

    b = filled .fst

    faces : ∀ i (i≠k : ¬ i ≡ k) → d i b ≡ x i i≠k
    faces i i≠k with Nat.≤-split (i .lower) (k .lower)
    ... | inl i<k       = filled .snd .fst i i≠k i<k
    ... | inr (inl k<i) = filled .snd .snd i i≠k k<i
    ... | inr (inr i≡k) = absurd (i≠k (fin-path i≡k))
```

## Eilenberg–MacLane objects are fibrant

The [[Eilenberg–MacLane objects|eilenberg-maclane-object]] $K(A,n)$
are (underlying simplicial sets of) simplicial abelian groups, so
Moore's theorem specialises immediately: they are Kan complexes. This
is the fibrancy that makes the mapping-space definition of
[[cohomology|eilenberg-maclane-object]] homotopically meaningful —
the missing ingredient of the paper's diagram (31).

```agda
K-is-kan : (A : Abelian-group lzero) (n : Nat) → is-kan (K-sset A n)
K-is-kan A n = sab-is-kan (K A n)
```

## Mapping spaces into simplicial abelian groups

The internal mapping space $\mathrm{Maps}(X, Y)$ of simplicial sets
is Kan whenever $Y$ is — but the general proof needs the theory of
anodyne extensions. For the mapping spaces this development actually
uses — those into $K(A,n)$ — there is a purely algebraic route:
when the target is a simplicial *abelian group*, the mapping space
is again a simplicial abelian group, with all operations pointwise,
so Moore's theorem applies directly.

<!--
```agda
private module SC = Cartesian-closed sSet-closed
```
-->

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) (X : ⌞ sSet ⌟) where
  private
    module G = Functor G
    module Gr (m : Nat) = Abelian-group-on (G.₀ m .snd)

    Y : ⌞ sSet ⌟
    Y = Ab↪Sets F∘ G

  Maps-ab : Functor (Δ ^op) (Ab lzero)
  Maps-ab .F₀ n = SC.[ X , Y ] .F₀ n , make-abelian-group.to-abelian-group-on mk where
    mk : make-abelian-group ⌞ SC.[ X , Y ] .F₀ n ⌟
    mk .make-abelian-group.ab-is-set = SC.[ X , Y ] .F₀ n .is-tr
    mk .make-abelian-group.mul α β = NT
      (λ m p → Gr._*_ m (α .η m p) (β .η m p))
      (λ a b f → funext λ p →
          ap₂ (Gr._*_ b)
            (happly (α .is-natural a b f) p)
            (happly (β .is-natural a b f) p)
        ∙ sym (is-group-hom.pres-⋆ (G.₁ f .snd) _ _))
    mk .make-abelian-group.inv α = NT
      (λ m p → Gr._⁻¹ m (α .η m p))
      (λ a b f → funext λ p →
          ap (Gr._⁻¹ b) (happly (α .is-natural a b f) p)
        ∙ sym (is-group-hom.pres-inv (G.₁ f .snd)))
    mk .make-abelian-group.1g = NT
      (λ m p → Gr.1g m)
      (λ a b f → funext λ p → sym (is-group-hom.pres-id (G.₁ f .snd)))
    mk .make-abelian-group.idl α = Nat-path λ m → funext λ p → Gr.idl m
    mk .make-abelian-group.assoc α β γ = Nat-path λ m → funext λ p → Gr.associative m
    mk .make-abelian-group.invl α = Nat-path λ m → funext λ p → Gr.inversel m
    mk .make-abelian-group.comm α β = Nat-path λ m → funext λ p → Gr.commutes m
  Maps-ab .F₁ f .fst = SC.[ X , Y ] .F₁ f
  Maps-ab .F₁ f .snd .is-group-hom.pres-⋆ α β = Nat-path λ m → funext λ p → refl
  Maps-ab .F-id = ext λ α i g x' →
    ap (α .η i) (Σ-pathp (Δ .Precategory.idl _) refl)
  Maps-ab .F-∘ f g = ext λ α i h x' →
    ap (α .η i) (Σ-pathp (sym (Δ .Precategory.assoc g f h)) refl)
```

The underlying simplicial set of this simplicial abelian group *is*
the exponential, so the mapping space is a Kan complex.

```agda
  Maps-ab-underlying : (Ab↪Sets F∘ Maps-ab) ≡ SC.[ X , Y ]
  Maps-ab-underlying = Functor-path (λ n → refl) (λ f → refl)

  Maps-into-ab-is-kan : is-kan SC.[ X , Y ]
  Maps-into-ab-is-kan = subst is-kan Maps-ab-underlying (sab-is-kan Maps-ab)
```

In particular, the mapping spaces defining
[[cohomology|eilenberg-maclane-object]] are Kan complexes: the
homotopies that $H[X,n]\langle A \rangle$ quotients by are honest
homotopies in a fibrant object.

```agda
Maps-K-is-kan
  : (X : ⌞ sSet ⌟) (A : Abelian-group lzero) (n : Nat)
  → is-kan SC.[ X , K-sset A n ]
Maps-K-is-kan X A n = Maps-into-ab-is-kan (K A n) X
```

## The group structure on connected components

The set of [[connected components|simplicial-set]] of a simplicial
abelian group is itself an abelian group: the operations descend to
the coequaliser because multiplying a boundary by a degenerate
simplex is again a boundary — if $h$ connects $d_0 h$ to $d_1 h$,
then $h \cdot s_0 b$ connects $d_0 h \cdot b$ to $d_1 h \cdot b$.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  private
    module G = Functor G
    module G0 = Abelian-group-on (G.₀ 0 .snd)
    module G1 = Abelian-group-on (G.₀ 1 .snd)

    d₀ d₁ : ⌞ G.₀ 1 ⌟ → ⌞ G.₀ 0 ⌟
    d₀ = G.₁ (δ fzero) .fst
    d₁ = G.₁ (δ (fsuc fzero)) .fst

    s₀ : ⌞ G.₀ 0 ⌟ → ⌞ G.₀ 1 ⌟
    s₀ = G.₁ (σ fzero) .fst

    unit-law : (i : Fin 2) → σ fzero ∘Δ δ i ≡ Δ .Precategory.id → ∀ b
             → G.₁ (δ i) .fst (s₀ b) ≡ b
    unit-law i p b =
        sym (happly (ap ∫Hom.fst (G.F-∘ (δ i) (σ fzero))) b)
      ∙ happly (ap (λ w → ∫Hom.fst (G.₁ w)) p) b
      ∙ happly (ap ∫Hom.fst G.F-id) b

    d₀-s₀ : ∀ b → d₀ (s₀ b) ≡ b
    d₀-s₀ = unit-law fzero (σ-δ-id fzero)

    d₁-s₀ : ∀ b → d₁ (s₀ b) ≡ b
    d₁-s₀ = unit-law (fsuc fzero) (σ-δ-id' fzero)

    inc₀ : ⌞ G.₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ G)
    inc₀ = inc

    connect
      : (dh : ⌞ G.₀ 1 ⌟ → ⌞ G.₀ 0 ⌟)
        (hom : is-group-hom (Abelian→Group-on (G.₀ 1 .snd)) (Abelian→Group-on (G.₀ 0 .snd)) dh)
      → (ds : ∀ b → dh (s₀ b) ≡ b)
      → ∀ a h → dh (G1._*_ h (s₀ a)) ≡ G0._*_ (dh h) a
    connect dh hom ds a h =
        is-group-hom.pres-⋆ hom h (s₀ a)
      ∙ ap (G0._*_ (dh h)) (ds a)

  π₀-ab : Abelian-group lzero
  π₀-ab = to-ab mk where
    mk : make-abelian-group (π₀ˢ (Ab↪Sets F∘ G))
    mk .make-abelian-group.ab-is-set = squash
    mk .make-abelian-group.mul = Coeq-rec₂ squash ci r1 r2 where
      ci : ⌞ G.₀ 0 ⌟ → ⌞ G.₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ G)
      ci a b = inc (G0._*_ a b)
      r1 : ∀ a h → ci (d₀ h) a ≡ ci (d₁ h) a
      r1 a h =
          sym (ap inc₀ (connect d₀ (G.₁ (δ fzero) .snd) d₀-s₀ a h))
        ∙ Coeq.glue (G1._*_ h (s₀ a))
        ∙ ap inc₀ (connect d₁ (G.₁ (δ (fsuc fzero)) .snd) d₁-s₀ a h)
      r2 : ∀ a h → ci a (d₀ h) ≡ ci a (d₁ h)
      r2 a h =
          sym (ap inc₀
            ( is-group-hom.pres-⋆ (G.₁ (δ fzero) .snd) (s₀ a) h
            ∙ ap (λ z → G0._*_ z (d₀ h)) (d₀-s₀ a)))
        ∙ Coeq.glue (G1._*_ (s₀ a) h)
        ∙ ap inc₀
            ( is-group-hom.pres-⋆ (G.₁ (δ (fsuc fzero)) .snd) (s₀ a) h
            ∙ ap (λ z → G0._*_ z (d₁ h)) (d₁-s₀ a))
    mk .make-abelian-group.inv = Coeq-rec ci r' where
      ci : ⌞ G.₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ G)
      ci a = inc (G0._⁻¹ a)
      r' : ∀ h → ci (d₀ h) ≡ ci (d₁ h)
      r' h =
          sym (ap inc₀ (is-group-hom.pres-inv (G.₁ (δ fzero) .snd)))
        ∙ Coeq.glue (G1._⁻¹ h)
        ∙ ap inc₀ (is-group-hom.pres-inv (G.₁ (δ (fsuc fzero)) .snd))
    mk .make-abelian-group.1g = inc G0.1g
    mk .make-abelian-group.idl = Coeq-elim-prop (λ _ → hlevel 1)
      λ a → ap inc₀ (G0.idl)
    mk .make-abelian-group.assoc =
      Coeq-elim-prop (λ _ → hlevel 1) λ a →
      Coeq-elim-prop (λ _ → hlevel 1) λ b →
      Coeq-elim-prop (λ _ → hlevel 1) λ c →
      ap inc₀ G0.associative
    mk .make-abelian-group.invl = Coeq-elim-prop (λ _ → hlevel 1)
      λ a → ap inc₀ G0.inversel
    mk .make-abelian-group.comm =
      Coeq-elim-prop (λ _ → hlevel 1) λ a →
      Coeq-elim-prop (λ _ → hlevel 1) λ b →
      ap inc₀ G0.commutes
```

Combining with the mapping-space structure: **cohomology is an
abelian group**, the group structure it classically inherits from
the target $K(A,n)$.

```agda
H-Ab
  : (X : ⌞ sSet ⌟) (n : Nat) (A : Abelian-group lzero)
  → Abelian-group-on H[ X , n ]⟨ A ⟩
H-Ab X n A = subst Abelian-group-on
  (ap π₀ˢ (Maps-ab-underlying (K A n) X))
  (π₀-ab (Maps-ab (K A n) X) .snd)
```

## Functoriality

Cohomology is contravariantly functorial: a map of simplicial sets
$w : X' \to X$ pulls mapping spaces back by precomposition, the
pullback is a homomorphism degreewise since the operations are
pointwise in the target, and everything descends to $\pi_0$.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  private
    module G = Functor G
    module Gr (m : Nat) = Abelian-group-on (G.₀ m .snd)

  Maps-ab-precompose
    : {X X' : ⌞ sSet ⌟} (w : X' => X)
    → Maps-ab G X => Maps-ab G X'
  Maps-ab-precompose {X} {X'} w .η n .fst nt = NT
    (λ m p → nt .η m (p .fst , w .η m (p .snd)))
    (λ a b f → funext λ p →
        ap (λ z → nt .η b (p .fst ∘Δ f , z)) (happly (w .is-natural a b f) (p .snd))
      ∙ happly (nt .is-natural a b f) (p .fst , w .η a (p .snd)))
  Maps-ab-precompose w .η n .snd .is-group-hom.pres-⋆ α β =
    Nat-path λ m → funext λ p → refl
  Maps-ab-precompose w .is-natural n n' g = ext λ nt m h x' → refl

module _ {G G' : Functor (Δ ^op) (Ab lzero)} (α : G => G') where
  private
    module G = Functor G
    module G' = Functor G'

    inc' : ⌞ G'.₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ G')
    inc' = inc

  π₀-ab-map : Ab lzero .Precategory.Hom (π₀-ab G) (π₀-ab G')
  π₀-ab-map .fst = Coeq-rec ci r where
    ci : ⌞ G.₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ G')
    ci a = inc (α .η 0 .fst a)
    r : ∀ h → ci (G.₁ (δ fzero) .fst h) ≡ ci (G.₁ (δ (fsuc fzero)) .fst h)
    r h =
        ap inc' (happly (ap ∫Hom.fst (α .is-natural 1 0 (δ fzero))) h)
      ∙ Coeq.glue (α .η 1 .fst h)
      ∙ sym (ap inc' (happly (ap ∫Hom.fst (α .is-natural 1 0 (δ (fsuc fzero)))) h))
  π₀-ab-map .snd .is-group-hom.pres-⋆ =
    Coeq-elim-prop (λ _ → hlevel 1) λ a →
    Coeq-elim-prop (λ _ → hlevel 1) λ b →
    ap inc' (is-group-hom.pres-⋆ (α .η 0 .snd) a b)
```

Assembling: for every abelian group $A$ and degree $n$, cohomology
is a functor $\mathrm{sSet}^{\mathrm{op}} \to \mathrm{Ab}$, whose
value at $X$ has underlying set $H[X,n]\langle A\rangle$.

```agda
H-functor : (A : Abelian-group lzero) (n : Nat) → Functor (sSet ^op) (Ab lzero)
H-functor A n .F₀ X = π₀-ab (Maps-ab (K A n) X)
H-functor A n .F₁ w = π₀-ab-map (Maps-ab-precompose (K A n) w)
H-functor A n .F-id {X} = ext λ nt →
  ap inc-X (Nat-path λ m → funext λ p → refl)
  where
  inc-X : ⌞ Maps-ab (K A n) X .F₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ Maps-ab (K A n) X)
  inc-X = inc
H-functor A n .F-∘ {x} {y} {z} w v = ext λ nt →
  ap inc-z (Nat-path λ m → funext λ p → refl)
  where
  inc-z : ⌞ Maps-ab (K A n) z .F₀ 0 ⌟ → π₀ˢ (Ab↪Sets F∘ Maps-ab (K A n) z)
  inc-z = inc

H-functor-carrier
  : (A : Abelian-group lzero) (n : Nat) (X : ⌞ sSet ⌟)
  → ⌞ H-functor A n .F₀ X ⌟ ≡ H[ X , n ]⟨ A ⟩
H-functor-carrier A n X = ap π₀ˢ (Maps-ab-underlying (K A n) X)
```
