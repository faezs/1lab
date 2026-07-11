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
