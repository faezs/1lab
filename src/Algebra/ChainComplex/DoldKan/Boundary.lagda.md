<!--
```agda
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan.Normalization
open import Algebra.ChainComplex.DoldKan.Fundamental
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin
open import Data.Sum

import Data.Nat as Nat

open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Boundary where
```

# The boundary formula for fundamental classes

This module assembles the telescoping lemmas and the vanishing
theorem $N \cap D = 0$ into the boundary formula for the fundamental
classes,

$$
d_0\, e_{k+1} \;=\; \sum_{i=0}^{k+1} (-1)^i\, \delta_i \cdot e_k,
$$

the combinatorial engine of the Dold–Kan counit. The strategy: both
sides are normalized, their difference is a sum of degeneracies by
the telescoping expansion, so it vanishes.

## Abelian bookkeeping

<!--
```agda
private
  module abl {ℓ} {T : Type ℓ} (AG : Abelian-group-on T) where
    private module A = Abelian-group-on AG

    shuffle4 : ∀ a b u v → A._*_ (A._*_ a b) (A._*_ u v) ≡ A._*_ (A._*_ a u) (A._*_ b v)
    shuffle4 a b u v =
        sym A.associative
      ∙ ap (A._*_ a) (A.associative ∙ ap (λ z → A._*_ z v) A.commutes ∙ sym A.associative)
      ∙ A.associative

    inv-distr : ∀ a b → A._⁻¹ (A._*_ a b) ≡ A._*_ (A._⁻¹ a) (A._⁻¹ b)
    inv-distr a b =
        sym A.idl
      ∙ ap (λ z → A._*_ z (A._⁻¹ (A._*_ a b))) lem
      ∙ sym A.associative
      ∙ ap (A._*_ (A._*_ (A._⁻¹ a) (A._⁻¹ b))) A.inverser
      ∙ A.idr
      where
      lem : A.1g ≡ A._*_ (A._*_ (A._⁻¹ a) (A._⁻¹ b)) (A._*_ a b)
      lem = sym A.inversel
          ∙ ap (λ z → A._*_ z b)
              ( sym A.idr
              ∙ ap (A._*_ (A._⁻¹ b)) (sym A.inversel)
              ∙ A.associative
              ∙ ap (λ z → A._*_ z a) A.commutes)
          ∙ sym A.associative

    cancel-eq : ∀ a b → A._*_ a (A._⁻¹ b) ≡ A.1g → a ≡ b
    cancel-eq a b p =
        sym A.idr
      ∙ ap (A._*_ a) (sym A.inversel)
      ∙ A.associative
      ∙ ap (λ z → A._*_ z b) p
      ∙ A.idl

  ¬sucx≤x : ∀ {x} → ¬ (suc x Nat.≤ x)
  ¬sucx≤x {zero}  le = Nat.¬suc≤0 le
  ¬sucx≤x {suc x} le = ¬sucx≤x (Nat.≤-peel le)

  le0 : ∀ {x} → x Nat.≤ 0 → x ≡ 0
  le0 {zero}  _  = refl
  le0 {suc x} le = absurd (Nat.¬suc≤0 le)

  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)
```
-->

## Closure properties of degenerate representations

Bounded-degenerate representations are closed under the group unit,
padding to a larger bound, sums, inverses, single degeneracies, and
pushforward along maps of simplicial abelian groups.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  module _ {m : Nat} where
    private
      module Gsm = Abelian-group-on (G .F₀ (suc m) .snd)
      module Gm  = Abelian-group-on (G .F₀ m .snd)
      module A+  = abl (G .F₀ (suc m) .snd)
      module Am  = abl (G .F₀ m .snd)

    deg-unit : (j : Nat) → j Nat.< suc m → Deg G {m} j Gsm.1g
    deg-unit zero _ = Gm.1g , sym (is-group-hom.pres-id (G .F₁ (σ fzero) .snd))
    deg-unit (suc j) b =
        b , Gm.1g , Gsm.1g , deg-unit j (Nat.<-weaken b)
      , ( sym Gsm.idr
        ∙ ap (Gsm._*_ Gsm.1g)
            (sym (is-group-hom.pres-id (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-pad
      : (j : Nat) (b : suc j Nat.< suc m) {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} (suc j) x
    deg-pad j b {x} dx =
        b , Gm.1g , x , dx
      , ( sym Gsm.idr
        ∙ ap (Gsm._*_ x)
            (sym (is-group-hom.pres-id (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-pad-≤
      : (j j' : Nat) → j Nat.≤ j' → j' Nat.< suc m
      → {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j' x
    deg-pad-≤ j zero le b {x} dx =
      subst (λ z → Deg G {m} z x) (le0 le) dx
    deg-pad-≤ j (suc j') le b {x} dx with Nat.≤-split j (suc j')
    ... | inl j<sj' = deg-pad j' b (deg-pad-≤ j j' (Nat.≤-peel j<sj') (Nat.<-weaken b) dx)
    ... | inr (inl sj'<j) = absurd (¬sucx≤x (Nat.≤-trans sj'<j le))
    ... | inr (inr j≡sj') = subst (λ z → Deg G {m} z x) j≡sj' dx

    deg-sum
      : (j : Nat) {x y : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j y → Deg G {m} j (Gsm._*_ x y)
    deg-sum zero {x} {y} (a , p) (b , q) =
        Gm._*_ a b
      , ( ap₂ Gsm._*_ p q
        ∙ sym (is-group-hom.pres-⋆ (G .F₁ (σ fzero) .snd) a b))
    deg-sum (suc j) {x} {y} (b , a , x' , dx' , p) (b' , c , y' , dy' , q) =
        b , Gm._*_ a c , Gsm._*_ x' y'
      , deg-sum j dx' dy'
      , ( ap₂ Gsm._*_ p (q ∙ ap (Gsm._*_ y')
            (ap (λ z → s z c) (fin-path' {x = fin (suc j) ⦃ b' ⦄} {y = fin (suc j) ⦃ b ⦄} refl)))
        ∙ A+.shuffle4 x' _ y' _
        ∙ ap (Gsm._*_ (Gsm._*_ x' y'))
            (sym (is-group-hom.pres-⋆ (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd) a c)))
      where
      fin-path' : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
      fin-path' {n} = fin-ap {n = λ _ → n}

    deg-inv
      : (j : Nat) {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j (Gsm._⁻¹ x)
    deg-inv zero {x} (a , p) =
        Gm._⁻¹ a
      , ( ap Gsm._⁻¹ p
        ∙ sym (is-group-hom.pres-inv (G .F₁ (σ fzero) .snd)))
    deg-inv (suc j) {x} (b , a , x' , dx' , p) =
        b , Gm._⁻¹ a , Gsm._⁻¹ x'
      , deg-inv j dx'
      , ( ap Gsm._⁻¹ p
        ∙ A+.inv-distr x' _
        ∙ ap (Gsm._*_ (Gsm._⁻¹ x'))
            (sym (is-group-hom.pres-inv (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-single
      : (i : Nat) (bi : i Nat.< suc m) (y : ⌞ G .F₀ m ⌟)
      → Deg G {m} i (s (fin i ⦃ bi ⦄) y)
    deg-single zero bi y = y , refl
    deg-single (suc i) bi y =
        bi , y , Gsm.1g , deg-unit i (Nat.<-weaken bi)
      , sym Gsm.idl
```

Pushforward: maps of simplicial abelian groups preserve
bounded-degenerate representations.

```agda
module _ {G G' : Functor (Δ ^op) (Ab lzero)} (α : G => G') where
  private
    module S  = Simplicial-operators G
    module S' = Simplicial-operators G'

  deg-push
    : {m : Nat} (j : Nat) {x : ⌞ G .F₀ (suc m) ⌟}
    → Deg G {m} j x → Deg G' {m} j (α .η (suc m) .fst x)
  deg-push {m} zero {x} (a , p) =
      α .η m .fst a
    , ( ap (α .η (suc m) .fst) p
      ∙ happly (ap ∫Hom.fst (α .is-natural m (suc m) (σ fzero))) a)
  deg-push {m} (suc j) {x} (b , a , x' , dx' , p) =
      b , α .η m .fst a , α .η (suc m) .fst x'
    , deg-push j dx'
    , ( ap (α .η (suc m) .fst) p
      ∙ is-group-hom.pres-⋆ (α .η (suc m) .snd) x' _
      ∙ ap (Abelian-group-on._*_ (G' .F₀ (suc m) .snd) (α .η (suc m) .fst x'))
          (happly (ap ∫Hom.fst (α .is-natural m (suc m) (σ (fin (suc j) ⦃ b ⦄)))) a))
```

## The defect of the pass is degenerate

Successive partial passes on the same simplex differ by a sum of
degeneracies: each correction step subtracts a single degeneracy.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  pass-defect
    : {m₀ : Nat} (fuel c₀ : Nat)
      (eq : suc c₀ Nat.+ fuel ≡ suc (suc (suc m₀)))
      (x : ⌞ G .F₀ (suc (suc m₀)) ⌟)
    → Deg G {suc m₀} (suc m₀)
        (Abelian-group-on._*_ (G .F₀ (suc (suc m₀)) .snd)
          (normalize-desc G fuel (suc c₀) eq (Nat.s≤s Nat.0≤x) x .fst)
          (Abelian-group-on._⁻¹ (G .F₀ (suc (suc m₀)) .snd) x))
  pass-defect {m₀} zero c₀ eq x =
    subst (Deg G {suc m₀} (suc m₀)) (sym Gsm.inverser)
      (deg-unit G (suc m₀) Nat.≤-refl)
    where module Gsm = Abelian-group-on (G .F₀ (suc (suc m₀)) .snd)
  pass-defect {m₀} (suc fuel) c₀ eq x =
    subst (Deg G {suc m₀} (suc m₀)) path combined
    where
    module Gsm = Abelian-group-on (G .F₀ (suc (suc m₀)) .snd)
    module A+ = abl (G .F₀ (suc (suc m₀)) .snd)

    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄

    y : ⌞ G .F₀ (suc (suc m₀)) ⌟
    y = normalize-desc G fuel (suc (suc c₀))
          (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x .fst

    corr : ⌞ G .F₀ (suc (suc m₀)) ⌟
    corr = s Jf (d Ff y)

    rec : Deg G {suc m₀} (suc m₀) (Gsm._*_ y (Gsm._⁻¹ x))
    rec = pass-defect fuel (suc c₀) (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) x

    corr-deg : Deg G {suc m₀} (suc m₀) (Gsm._⁻¹ corr)
    corr-deg = deg-inv G (suc m₀)
      (deg-pad-≤ G c₀ (suc m₀) (Nat.≤-peel (Nat.≤-peel bF)) Nat.≤-refl
        (deg-single G c₀ (Nat.≤-peel bF) (d Ff y)))

    combined : Deg G {suc m₀} (suc m₀)
      (Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ x)) (Gsm._⁻¹ corr))
    combined = deg-sum G (suc m₀) rec corr-deg

    path : Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ x)) (Gsm._⁻¹ corr)
         ≡ Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ corr)) (Gsm._⁻¹ x)
    path = sym Gsm.associative
         ∙ ap (Gsm._*_ y) Gsm.commutes
         ∙ Gsm.associative
```
