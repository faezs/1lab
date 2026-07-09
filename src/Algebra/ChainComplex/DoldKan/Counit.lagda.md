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
open import Algebra.ChainComplex.DoldKan.Boundary
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin
open import Data.Sum

import Algebra.ChainComplex.Moore
import Cat.Reasoning
import Data.Nat as Nat

open Chain-complex
open Chain-map
open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Counit where
```

# The Dold–Kan counit is a chain map

With the [[boundary formula|moore-complex]] for the fundamental
classes in hand, the levelwise counit — evaluation at the
fundamental class — commutes with the boundaries: the boundary of
the fundamental class is the alternating sum of coface
pushforwards, a *normalized* simplex of $\Gamma(C)$ kills every
positive pushforward, and what survives is exactly the chain
square.

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
  module ChC = Cat.Reasoning (Ch lzero)

  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)
```
-->

## Normality of the alternating sum, uniformly

```agda
Σnorm : (n fuel j : Nat) (eq : j Nat.+ fuel ≡ suc (suc n))
      → MC.norm ℤ⟨ Δ[ suc n ] ⟩ n (Σalt n fuel j eq)
Σnorm zero fuel j eq = lift tt
Σnorm (suc n₁) fuel j eq = λ i →
  Σalt-norm n₁ fuel j eq (fsuc i) (Nat.s≤s Nat.0≤x)
```

## The square

```agda
module _ (C : Chain-complex lzero) where
  private
    module Cc (n : Nat) = Abelian-group-on (C .ob n .snd)
    module ΓC = Functor (Γ C)

  private
    kill
      : (n : Nat) (φ : ⌞ MC.Moore (Γ C) .ob (suc n) ⌟)
        (fuel j : Nat) (eq : j Nat.+ fuel ≡ suc (suc n))
      → 1 Nat.≤ j
      → φ .fst .map n .∫Hom.fst (Σalt n fuel j eq , Σnorm n fuel j eq)
      ≡ Cc.1g n
    kill n φ fuel zero eq le = absurd (Nat.¬suc≤0 le)
    kill n φ zero (suc j₁) eq le =
        ap (φ .fst .map n .∫Hom.fst)
          (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc n ] ⟩ n) refl)
      ∙ is-group-hom.pres-id (φ .fst .map n .∫Hom.snd)
    kill n φ (suc fuel) (suc j₁) eq le =
        ap (φ .fst .map n .∫Hom.fst)
          (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc n ] ⟩ n) refl)
      ∙ is-group-hom.pres-⋆ (φ .fst .map n .∫Hom.snd) push-elem inv-tail-elem
      ∙ ap₂ (Cc._*_ n)
          push-dies
          ( is-group-hom.pres-inv (φ .fst .map n .∫Hom.snd) {x = tail-elem}
          ∙ ap (Cc._⁻¹ n)
              (kill n φ fuel (suc (suc j₁))
                (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq) (Nat.s≤s Nat.0≤x))
          ∙ abl-inv-1g)
      ∙ Cc.idr n
      where
      bj : suc j₁ Nat.< suc (suc n)
      bj = subst (suc (suc j₁) Nat.≤_) (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq)
             (Nat.s≤s (le-plus (suc j₁) fuel))

      push-elem : ⌞ NΔ (suc n) .ob n ⌟
      push-elem = NΔ-map (δ (fin (suc j₁) ⦃ bj ⦄)) .map n .∫Hom.fst
        (fundamental n)

      tail-elem : ⌞ NΔ (suc n) .ob n ⌟
      tail-elem =
          Σalt n fuel (suc (suc j₁)) (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq)
        , Σnorm n fuel (suc (suc j₁)) (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq)

      inv-tail-elem : ⌞ NΔ (suc n) .ob n ⌟
      inv-tail-elem = Abelian-group-on._⁻¹ (NΔ (suc n) .ob n .snd) tail-elem

      abl-inv-1g : Cc._⁻¹ n (Cc.1g n) ≡ Cc.1g n
      abl-inv-1g = sym (Cc.idl n) ∙ Cc.inverser n

      bj' : j₁ Nat.< suc n
      bj' = Nat.≤-peel bj

      push-dies : φ .fst .map n .∫Hom.fst push-elem ≡ Cc.1g n
      push-dies =
        happly (ap (λ w → w .map n .∫Hom.fst) (φ .snd (fin j₁ ⦃ bj' ⦄)))
          (fundamental n)
```

The chain square, and with it the counit.

```agda
  dk-counit : Chain-map (MC.Moore (Γ C)) C
  dk-counit .map n = dk-counit-level C n
  dk-counit .comm n (φ , nrm) =
      ap (λ w → w .map n .∫Hom.fst (fundamental n)) lhs-red
    ∙ split
    ∙ sym ( sym (φ .comm n (fundamental (suc n)))
          ∙ ap (φ .map n .∫Hom.fst)
              (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc n ] ⟩ n)
                (∂-fundamental n))
          ∙ split')
    where
    lhs-red
      : MC.Moore (Γ C) .∂ᶜ n .∫Hom.fst (φ , nrm) .fst
      ≡ ChC._∘_ φ (NΔ-map (δ fzero))
    lhs-red = refl

    head-elem : ⌞ NΔ (suc n) .ob n ⌟
    head-elem = NΔ-map (δ (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄)) .map n .∫Hom.fst
      (fundamental n)

    eq₁ : 1 Nat.+ suc n ≡ suc (suc n)
    eq₁ = sym (Nat.+-sucr 0 (suc n)) ∙ refl

    tail₁ : ⌞ NΔ (suc n) .ob n ⌟
    tail₁ =
        Σalt n (suc n) 1 eq₁
      , Σnorm n (suc n) 1 eq₁

    split
      : ChC._∘_ φ (NΔ-map (δ fzero)) .map n .∫Hom.fst (fundamental n)
      ≡ φ .map n .∫Hom.fst head-elem
    split = ap (φ .map n .∫Hom.fst)
      (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc n ] ⟩ n) refl)

    split'
      : φ .map n .∫Hom.fst
          (Σalt n (suc (suc n)) 0 refl , Σnorm n (suc (suc n)) 0 refl)
      ≡ φ .map n .∫Hom.fst head-elem
    split' =
        ap (φ .map n .∫Hom.fst)
          (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc n ] ⟩ n) refl)
      ∙ is-group-hom.pres-⋆ (φ .map n .∫Hom.snd) head-elem
          (Abelian-group-on._⁻¹ (NΔ (suc n) .ob n .snd) tail₁)
      ∙ ap (Cc._*_ n (φ .map n .∫Hom.fst head-elem))
          ( is-group-hom.pres-inv (φ .map n .∫Hom.snd) {x = tail₁}
          ∙ ap (Cc._⁻¹ n)
              (kill n (φ , nrm) (suc n) 1 eq₁ (Nat.s≤s Nat.0≤x))
          ∙ (sym (Cc.idl n) ∙ Cc.inverser n))
      ∙ Cc.idr n
```
