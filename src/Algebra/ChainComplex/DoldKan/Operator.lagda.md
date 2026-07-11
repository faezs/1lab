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

import Data.Nat as Nat

open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Operator where
```

# The normalization operator is a homomorphism

The [[descending correction pass|moore-complex]] was built
elementwise, together with its normalization guarantee. For the
normalization *theorem* — the decomposition of a simplicial abelian
group into its Moore complex and its degenerate part — we need the
same operator packaged as a **group homomorphism**: each correction
step $x \mapsto x \cdot (s_j d_{j+1} x)^{-1}$ is a pointwise
product of homomorphisms, hence a homomorphism, and the pass is
their finite composite.

<!--
```agda
private
  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)
```
-->

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  private
    module Ab' = Precategory (Ab lzero)

  corr-hom
    : {m₀ : Nat}
      (F : Fin (suc (suc (suc m₀)))) (J : Fin (suc (suc m₀)))
    → Ab'.Hom (G.₀ (suc (suc m₀))) (G.₀ (suc (suc m₀)))
  corr-hom {m₀} F J = Hsm._*_ Ab'.id
    (Hsm._⁻¹ (Ab'._∘_ (G.₁ (σ J)) (G.₁ (δ F))))
    where
    module Hsm = Abelian-group-on
      (Abelian-group-on-hom (G.₀ (suc (suc m₀))) (G.₀ (suc (suc m₀))))
```

The pass composes the corrections with exactly the fuel-indexed
control flow of the elementwise construction, so that agreement is
a computation.

```agda
  T-desc
    : {m₀ : Nat} (fuel c : Nat)
    → c Nat.+ fuel ≡ suc (suc (suc m₀)) → 0 Nat.< c
    → Ab'.Hom (G.₀ (suc (suc m₀))) (G.₀ (suc (suc m₀)))
  T-desc zero c eq pos = Ab'.id
  T-desc (suc fuel) zero eq pos = absurd (Nat.¬suc≤0 pos)
  T-desc {m₀} (suc fuel) (suc c₀) eq pos = Ab'._∘_
    (corr-hom Ff Jf)
    (T-desc fuel (suc (suc c₀))
      (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x))
    where
    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄

  T-desc-agree
    : {m₀ : Nat} (fuel c : Nat)
      (eq : c Nat.+ fuel ≡ suc (suc (suc m₀))) (pos : 0 Nat.< c)
    → (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
    → T-desc fuel c eq pos .∫Hom.fst x
    ≡ normalize-desc G fuel c eq pos x .fst
  T-desc-agree zero c eq pos x = refl
  T-desc-agree (suc fuel) zero eq pos x = absurd (Nat.¬suc≤0 pos)
  T-desc-agree {m₀} (suc fuel) (suc c₀) eq pos x =
    ap (corr-hom Ff Jf .∫Hom.fst)
      (T-desc-agree fuel (suc (suc c₀))
        (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x)
    where
    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄
```

The full pass, its homomorphism structure now manifest, inherits
the normalization guarantee from the elementwise construction.

```agda
  T-op
    : {m₀ : Nat}
    → Ab'.Hom (G.₀ (suc (suc m₀))) (G.₀ (suc (suc m₀)))
  T-op {m₀} = T-desc (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x)

  T-normalized
    : {m₀ : Nat} (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
    → ∀ i → 1 Nat.≤ i .lower
    → d i (T-op {m₀} .∫Hom.fst x) ≡ Gr.1g (suc m₀)
  T-normalized {m₀} x i ge =
      ap (d i) (T-desc-agree (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) x)
    ∙ normalize-desc G (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) x .snd i ge
```

## The pass changes nothing but degeneracies

Each correction multiplies by the inverse of a degeneracy image, so
the difference between an element and its normalization is
*degenerate*, with an explicit bounded representation.

<!--
```agda
  private
    module _ {m₀ : Nat} where
      private
        module Gsm = Abelian-group-on (G.₀ (suc (suc m₀)) .snd)

      shuf : (p q r t : ⌞ G.₀ (suc (suc m₀)) ⌟)
           → Gsm._*_ (Gsm._*_ p q) (Gsm._*_ r t)
           ≡ Gsm._*_ (Gsm._*_ p r) (Gsm._*_ q t)
      shuf p q r t =
          sym Gsm.associative
        ∙ ap (Gsm._*_ p) (Gsm.associative
            ∙ ap (λ z → Gsm._*_ z t) (Gsm.commutes {x = q} {y = r})
            ∙ sym Gsm.associative)
        ∙ Gsm.associative

      inv-unique : (x y : ⌞ G.₀ (suc (suc m₀)) ⌟)
                 → Gsm._*_ x y ≡ Gsm.1g → y ≡ Gsm._⁻¹ x
      inv-unique x y p =
          sym Gsm.idl
        ∙ ap (λ z → Gsm._*_ z y) (sym Gsm.inversel)
        ∙ sym Gsm.associative
        ∙ ap (Gsm._*_ (Gsm._⁻¹ x)) p
        ∙ Gsm.idr

      inv-distr : (x y : ⌞ G.₀ (suc (suc m₀)) ⌟)
                → Gsm._⁻¹ (Gsm._*_ x y) ≡ Gsm._*_ (Gsm._⁻¹ x) (Gsm._⁻¹ y)
      inv-distr x y = sym (inv-unique (Gsm._*_ x y) _
        ( shuf x y (Gsm._⁻¹ x) (Gsm._⁻¹ y)
        ∙ ap₂ Gsm._*_ (Gsm.inverser {x = x}) (Gsm.inverser {x = y})
        ∙ Gsm.idl))

      inv-inv : (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
              → Gsm._⁻¹ (Gsm._⁻¹ x) ≡ x
      inv-inv x = sym (inv-unique (Gsm._⁻¹ x) x Gsm.inversel)

      deg-bound
        : (j : Nat) {x : ⌞ G.₀ (suc (suc m₀)) ⌟}
        → Deg G {suc m₀} j x → j Nat.< suc (suc m₀)
      deg-bound zero _ = Nat.s≤s Nat.0≤x
      deg-bound (suc j) (b , _) = b
```
-->

```agda
  T-diff
    : {m₀ : Nat} (fuel c : Nat)
      (eq : c Nat.+ fuel ≡ suc (suc (suc m₀))) (pos : 0 Nat.< c)
    → (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
    → Deg G {suc m₀} (suc m₀)
        (Abelian-group-on._*_ (G.₀ (suc (suc m₀)) .snd) x
          (Abelian-group-on._⁻¹ (G.₀ (suc (suc m₀)) .snd)
            (T-desc fuel c eq pos .∫Hom.fst x)))
  T-diff {m₀} zero c eq pos x =
    subst (Deg G {suc m₀} (suc m₀)) (sym (Gsm.inverser {x = x}))
      (deg-unit G (suc m₀) Nat.≤-refl)
    where module Gsm = Abelian-group-on (G.₀ (suc (suc m₀)) .snd)
  T-diff (suc fuel) zero eq pos x = absurd (Nat.¬suc≤0 pos)
  T-diff {m₀} (suc fuel) (suc c₀) eq pos x =
    subst (Deg G {suc m₀} (suc m₀)) (sym main-path)
      (deg-sum G (suc m₀)
        (T-diff fuel (suc (suc c₀))
          (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x)
        (deg-pad-≤ G c₀ (suc m₀)
          (Nat.≤-peel (Nat.≤-peel bF)) Nat.≤-refl
          (deg-single G c₀ (Nat.≤-peel bF) (d Ff tin))))
    where
    module Gsm = Abelian-group-on (G.₀ (suc (suc m₀)) .snd)

    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄

    tin : ⌞ G.₀ (suc (suc m₀)) ⌟
    tin = T-desc fuel (suc (suc c₀))
      (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x)
      .∫Hom.fst x

    S : ⌞ G.₀ (suc (suc m₀)) ⌟
    S = s Jf (d Ff tin)

    main-path
      : Gsm._*_ x (Gsm._⁻¹ (Gsm._*_ tin (Gsm._⁻¹ S)))
      ≡ Gsm._*_ (Gsm._*_ x (Gsm._⁻¹ tin)) S
    main-path =
        ap (Gsm._*_ x) (inv-distr tin (Gsm._⁻¹ S))
      ∙ ap (λ z → Gsm._*_ x (Gsm._*_ (Gsm._⁻¹ tin) z)) (inv-inv S)
      ∙ Gsm.associative
```

## Fixing the normalized, killing the degenerate

Together with the [[vanishing theorem|moore-complex]] for
normalized degenerate simplices, the difference representation
pins the operator down completely: it *fixes* every normalized
element, and *annihilates* every degenerate one.

```agda
  T-fix
    : {m₀ : Nat} (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
    → (∀ i → 1 Nat.≤ i .lower → d i x ≡ Gr.1g (suc m₀))
    → T-op {m₀} .∫Hom.fst x ≡ x
  T-fix {m₀} x nx = sym
    ( sym Gsm.idr
    ∙ ap (Gsm._*_ x) (sym (Gsm.inversel {x = tx}))
    ∙ Gsm.associative
    ∙ ap (λ z → Gsm._*_ z tx) vanish
    ∙ Gsm.idl)
    where
    module Gsm = Abelian-group-on (G.₀ (suc (suc m₀)) .snd)

    tx : ⌞ G.₀ (suc (suc m₀)) ⌟
    tx = T-op {m₀} .∫Hom.fst x

    D∆ : ⌞ G.₀ (suc (suc m₀)) ⌟
    D∆ = Gsm._*_ x (Gsm._⁻¹ tx)

    D-norm : ∀ i → 1 Nat.≤ i .lower → d i D∆ ≡ Gr.1g (suc m₀)
    D-norm i ge =
        d-⋆ i x (Gsm._⁻¹ tx)
      ∙ ap (Abelian-group-on._*_ (G.₀ (suc m₀) .snd) (d i x)) (d-inv i tx)
      ∙ ap₂ (Abelian-group-on._*_ (G.₀ (suc m₀) .snd))
          (nx i ge)
          (ap (Abelian-group-on._⁻¹ (G.₀ (suc m₀) .snd))
            (T-normalized x i ge))
      ∙ Gr.inverser (suc m₀)

    vanish : D∆ ≡ Gsm.1g
    vanish = normalized-degenerate-vanish G {m = suc m₀} D∆ D-norm
      (suc m₀)
      (T-diff (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) x)

  T-kill
    : {m₀ : Nat} (x : ⌞ G.₀ (suc (suc m₀)) ⌟) (j : Nat)
    → Deg G {suc m₀} j x
    → T-op {m₀} .∫Hom.fst x ≡ Gr.1g (suc (suc m₀))
  T-kill {m₀} x j dx = normalized-degenerate-vanish G {m = suc m₀} tx
    (λ i ge → T-normalized x i ge) (suc m₀) tx-deg
    where
    module Gsm = Abelian-group-on (G.₀ (suc (suc m₀)) .snd)

    tx : ⌞ G.₀ (suc (suc m₀)) ⌟
    tx = T-op {m₀} .∫Hom.fst x

    D∆ : ⌞ G.₀ (suc (suc m₀)) ⌟
    D∆ = Gsm._*_ x (Gsm._⁻¹ tx)

    tx-path : tx ≡ Gsm._*_ (Gsm._⁻¹ D∆) x
    tx-path = sym
      ( ap (λ z → Gsm._*_ z x) (inv-distr x (Gsm._⁻¹ tx))
      ∙ ap (λ z → Gsm._*_ (Gsm._*_ (Gsm._⁻¹ x) z) x) (inv-inv tx)
      ∙ ap (λ z → Gsm._*_ z x) (Gsm.commutes {x = Gsm._⁻¹ x} {y = tx})
      ∙ sym Gsm.associative
      ∙ ap (Gsm._*_ tx) (Gsm.inversel {x = x})
      ∙ Gsm.idr)

    tx-deg : Deg G {suc m₀} (suc m₀) tx
    tx-deg = subst (Deg G {suc m₀} (suc m₀)) (sym tx-path)
      (deg-sum G (suc m₀)
        (deg-inv G (suc m₀)
          (T-diff (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) x))
        (deg-pad-≤ G j (suc m₀)
          (Nat.≤-peel (deg-bound j dx)) Nat.≤-refl dx))
```
