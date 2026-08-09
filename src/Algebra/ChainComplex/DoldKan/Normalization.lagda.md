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

open import Data.Fin
open import Data.Sum

import Data.Nat as Nat

open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Normalization where
```

# Normalized degenerate simplices vanish

This module proves the irreducible half of the **normalization
theorem**: in a simplicial abelian group, a simplex that is both
*normalized* — all its faces but the zeroth vanish — and
*degenerate* — a sum of images of degeneracy operators — is zero.
(The other half, that every simplex splits into a normalized part
and a degenerate part, is already witnessed by the [[normalization
operator|moore-complex]].)

The proof is an induction over the degeneracy indices used: the top
index is killed by a unit law, and the resulting correction operator
$E = \mathrm{id} \cdot (s d)^{-1}$ — a homomorphism, being a
pointwise product of homomorphisms — pushes the representation down
one index, term by term.

<!--
```agda
private
  fin-path : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
  fin-path {n} = fin-ap {n = λ _ → n}

  weaken-lower : ∀ {n} (x : Fin n) → weaken x .lower ≡ x .lower
  weaken-lower x with fin-view x
  ... | zero  = refl
  ... | suc i = ap suc (weaken-lower i)
```
-->

## The missing commutation

The operator calculus records how faces move past degeneracies; for
the correction operator we also need degeneracies moving past each
other, in numeral-indexed form.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  s-s-comm
    : ∀ {n} (A : Fin (suc (suc n))) (B : Fin (suc n))
      (A' : Fin (suc (suc n))) (B' : Fin (suc n))
    → A .lower ≡ suc (B' .lower) → A' .lower ≡ B .lower
    → B .lower Nat.≤ B' .lower
    → ∀ w → s A (s B w) ≡ s A' (s B' w)
  s-s-comm A B A' B' p q le w = ap-op (σ B) (σ A) (σ B') (σ A')
    ( ap (λ z → σ B ∘Δ σ z) (fin-path {x = A} {y = fsuc B'} p)
    ∙ sym (σ-comm B B' le)
    ∙ ap (λ z → σ B' ∘Δ σ z)
        (fin-path {x = weaken B} {y = A'} (weaken-lower B ∙ sym q)))
    w
```

## Bounded-degenerate representations

`Deg j x` witnesses that $x$ is a sum $\sum_{i \le j} s_i y_i$ of
degeneracies with indices at most $j$, as a recursive structure.

```agda
  module _ {m : Nat} where
    private
      module Gm = Abelian-group-on (G .F₀ (suc m) .snd)

    Deg : Nat → ⌞ G .F₀ (suc m) ⌟ → Type
    Deg zero x = Σ[ y ∈ ⌞ G .F₀ m ⌟ ] (x ≡ s fzero y)
    Deg (suc j) x =
      Σ[ b ∈ (suc j Nat.< suc m) ]
      Σ[ y ∈ ⌞ G .F₀ m ⌟ ]
      Σ[ x' ∈ ⌞ G .F₀ (suc m) ⌟ ]
      (Deg j x' × (x ≡ Gm._*_ x' (s (fin (suc j) ⦃ b ⦄) y)))
```

## The correction operator

For a fixed index $J$, the correction $E_J\,x = x \cdot
(s_J\, d_{J+1}\, x)^{-1}$ is a pointwise product of homomorphisms,
hence a homomorphism; and it maps a degeneracy $s_i y$ ($i \le J$)
to the degeneracy $s_i(y \cdot (s_J d_{J+1} y)^{-1})$ one level
down, by the far-side commutations.

```agda
  module _ {m' : Nat} (J : Nat) (bJ : suc J Nat.< suc (suc m')) where
    private
      m : Nat
      m = suc m'
      module Gsm = Abelian-group-on (G .F₀ (suc m) .snd)
      module Hsm = Abelian-group-on
        (Abelian-group-on-hom (G .F₀ (suc m)) (G .F₀ (suc m)))

      SJ : Fin (suc m)
      SJ = fin (suc J) ⦃ bJ ⦄
      DJ : Fin (suc (suc m))
      DJ = fin (suc (suc J)) ⦃ Nat.s≤s bJ ⦄

    E-hom : Ab lzero .Precategory.Hom (G .F₀ (suc m)) (G .F₀ (suc m))
    E-hom = Hsm._*_ (Ab lzero .Precategory.id)
      (Hsm._⁻¹ (Ab lzero .Precategory._∘_ (G .F₁ (σ SJ)) (G .F₁ (δ DJ))))

    E : ⌞ G .F₀ (suc m) ⌟ → ⌞ G .F₀ (suc m) ⌟
    E = E-hom .fst

    E-single
      : (i : Nat) (bi : i Nat.< suc m) → i Nat.≤ J
      → (y : ⌞ G .F₀ m ⌟)
      → E (s (fin i ⦃ bi ⦄) y)
      ≡ s (fin i ⦃ bi ⦄)
          (Abelian-group-on._*_ (G .F₀ m .snd) y
            (Abelian-group-on._⁻¹ (G .F₀ m .snd)
              (s (fin J ⦃ Nat.≤-peel bJ ⦄)
                (d (fin (suc J) ⦃ Nat.s≤s (Nat.≤-peel bJ) ⦄) y))))
    E-single i bi le y =
        ap (Gsm._*_ (s Si y)) (ap Gsm._⁻¹
          ( ap (s SJ)
              (d-s-comm-above DJ Si D' S' refl refl (Nat.s≤s (Nat.s≤s le)) y)
          ∙ s-s-comm SJ S' Si S'' refl refl le (d D' y)))
      ∙ ap (Gsm._*_ (s Si y))
          (sym (is-group-hom.pres-inv (G .F₁ (σ Si) .snd)))
      ∙ sym (is-group-hom.pres-⋆ (G .F₁ (σ Si) .snd) y _)
      where
      Si : Fin (suc m)
      Si = fin i ⦃ bi ⦄
      D' : Fin (suc m)
      D' = fin (suc J) ⦃ Nat.s≤s (Nat.≤-peel bJ) ⦄
      S' : Fin m
      S' = fin i ⦃ Nat.≤-trans (Nat.s≤s le) (Nat.≤-peel bJ) ⦄
      S'' : Fin m
      S'' = fin J ⦃ Nat.≤-peel bJ ⦄
```

The correction preserves bounded-degenerate representations.

```agda
    E-deg : (j : Nat) → j Nat.≤ J → ∀ x → Deg {m = m} j x → Deg {m = m} j (E x)
    E-deg zero le x (y , p) =
        Abelian-group-on._*_ (G .F₀ m .snd) y
          (Abelian-group-on._⁻¹ (G .F₀ m .snd)
            (s (fin J ⦃ Nat.≤-peel bJ ⦄)
              (d (fin (suc J) ⦃ Nat.s≤s (Nat.≤-peel bJ) ⦄) y)))
      , (ap E p ∙ E-single 0 (Nat.s≤s Nat.0≤x) Nat.0≤x y)
    E-deg (suc j) le x (b , y , x' , rep' , p) =
        b
      , Abelian-group-on._*_ (G .F₀ m .snd) y
          (Abelian-group-on._⁻¹ (G .F₀ m .snd)
            (s (fin J ⦃ Nat.≤-peel bJ ⦄)
              (d (fin (suc J) ⦃ Nat.s≤s (Nat.≤-peel bJ) ⦄) y)))
      , E x'
      , E-deg j (Nat.≤-trans Nat.≤-ascend le) x' rep'
      , ( ap E p
        ∙ is-group-hom.pres-⋆ (E-hom .snd) x' (s (fin (suc j) ⦃ b ⦄) y)
        ∙ ap (Gsm._*_ (E x')) (E-single (suc j) b le y))
```

## The vanishing theorem

```agda
  normalized-degenerate-vanish
    : {m : Nat} (x : ⌞ G .F₀ (suc m) ⌟)
    → (∀ i → 1 Nat.≤ i .lower → d i x ≡ Abelian-group-on.1g (G .F₀ m .snd))
    → (j : Nat) → Deg {m = m} j x
    → x ≡ Abelian-group-on.1g (G .F₀ (suc m) .snd)
  normalized-degenerate-vanish {m} x nx zero (y , p) =
      p
    ∙ ap (s fzero) y≡1
    ∙ is-group-hom.pres-id (G .F₁ (σ fzero) .snd)
    where
    y≡1 : y ≡ Abelian-group-on.1g (G .F₀ m .snd)
    y≡1 = sym (d-s-id (fin 1) fzero (inr refl) y)
        ∙ ap (d (fin 1)) (sym p)
        ∙ nx (fin 1) (Nat.s≤s Nat.0≤x)
  normalized-degenerate-vanish {zero} x nx (suc j) (b , _) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel b))
  normalized-degenerate-vanish {suc m'} x nx (suc j) (b , y , x' , rep' , p) =
    normalized-degenerate-vanish x nx j deg-x
    where
    module Gsm = Abelian-group-on (G .F₀ (suc (suc m')) .snd)
    module Gm = Abelian-group-on (G .F₀ (suc m') .snd)

    Sj : Fin (suc (suc m'))
    Sj = fin (suc j) ⦃ b ⦄
    Dj : Fin (suc (suc (suc m')))
    Dj = fin (suc (suc j)) ⦃ Nat.s≤s b ⦄

    dx'y : Gm._*_ (d Dj x') y ≡ Gm.1g
    dx'y = sym ( d-⋆ Dj x' (s Sj y)
               ∙ ap (Gm._*_ (d Dj x')) (d-s-id Dj Sj (inr refl) y))
         ∙ ap (d Dj) (sym p)
         ∙ nx Dj (Nat.s≤s Nat.0≤x)

    y-val : y ≡ Gm._⁻¹ (d Dj x')
    y-val =
        sym Gm.idl
      ∙ ap (λ z → Gm._*_ z y) (sym Gm.inversel)
      ∙ sym Gm.associative
      ∙ ap (Gm._*_ (Gm._⁻¹ (d Dj x'))) dx'y
      ∙ Gm.idr

    x≡Ex' : x ≡ E j b x'
    x≡Ex' = p
      ∙ ap (Gsm._*_ x')
          ( ap (s Sj) y-val
          ∙ is-group-hom.pres-inv (G .F₁ (σ Sj) .snd))

    deg-x : Deg {m = suc m'} j x
    deg-x = subst (Deg j) (sym x≡Ex')
      (E-deg j b j Nat.≤-refl x' rep')
```
