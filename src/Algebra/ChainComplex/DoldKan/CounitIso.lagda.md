<!--
```agda
open import Cat.Instances.Simplex.Factorisation
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.Simplex.Classify
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
open import Algebra.ChainComplex.DoldKan.Operator
open import Algebra.ChainComplex.DoldKan.Boundary
open import Algebra.ChainComplex.DoldKan.Counit
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
module Algebra.ChainComplex.DoldKan.CounitIso where
```

# Towards the counit isomorphism

The [[Dold–Kan counit|dold-kan]] evaluates a normalized simplicial
map at the fundamental class. To see that this is an isomorphism we
corestrict the [[normalization operator|moore-complex]] to the
Moore subgroup — its image is normalized by construction — and use
it to reduce every question about a chain map's values to its
values on free generators, where the [[classification of
operators|kahler-differentials]] takes over.

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
```
-->

## Corestricting the operator

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  private
    module Ab' = Precategory (Ab lzero)
    module Nsub (n : Nat) =
      Abelian-group-on (MC.Moore G .ob n .snd)

  Tsub : (j : Nat) → Ab'.Hom (G.₀ j) (MC.Moore G .ob j)
  Tsub zero .∫Hom.fst x = x , lift tt
  Tsub zero .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G 0) refl
  Tsub (suc zero) .∫Hom.fst x =
    T₁ G .∫Hom.fst x , λ i → T₁-normalized G x i
  Tsub (suc zero) .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G 1)
      (is-group-hom.pres-⋆ (T₁ G .∫Hom.snd) x y)
  Tsub (suc (suc m₀)) .∫Hom.fst x =
      T-op G .∫Hom.fst x
    , λ i → T-normalized G x (fsuc i) (Nat.s≤s Nat.0≤x)
  Tsub (suc (suc m₀)) .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G (suc (suc m₀)))
      (is-group-hom.pres-⋆ (T-op G .∫Hom.snd) x y)
```

On elements that are already normalized — in particular on the
Moore subgroup itself — the corestriction is the identity.

```agda
  Tsub-fix
    : (j : Nat) (x : ⌞ MC.Moore G .ob j ⌟)
    → Tsub j .∫Hom.fst (x .fst) ≡ x
  Tsub-fix zero x = Σ-prop-path (MC.norm-is-prop G 0) refl
  Tsub-fix (suc zero) x = Σ-prop-path (MC.norm-is-prop G 1)
    (T₁-fix G (x .fst) (x .snd))
  Tsub-fix (suc (suc m₀)) x =
    Σ-prop-path (MC.norm-is-prop G (suc (suc m₀)))
      (T-fix G (x .fst) ge-form)
    where
    ge-form : ∀ i → 1 Nat.≤ i .lower
            → d i (x .fst) ≡ Gr.1g (suc m₀)
    ge-form i ge =
        ap (λ w → d w (x .fst))
          (fin-ap {n = λ _ → suc (suc (suc m₀))}
            {x = i} {y = fsuc (pred-eq .fst)}
            (pred-eq .snd))
      ∙ x .snd (pred-eq .fst)
      where
      pred-eq : Σ[ i₁ ∈ Fin (suc (suc m₀)) ]
                  (i .lower ≡ suc (i₁ .lower))
      pred-eq = go (i .lower) refl ge (i .Fin.bounded)
        where
        go : (l : Nat) → l ≡ i .lower → 1 Nat.≤ l
           → suc (i .lower) Nat.≤ suc (suc (suc m₀))
           → Σ[ i₁ ∈ Fin (suc (suc m₀)) ]
               (i .lower ≡ suc (i₁ .lower))
        go zero p ge' bd = absurd (Nat.¬suc≤0 ge')
        go (suc l) p ge' bd =
            fin l ⦃ Nat.≤-peel (subst (λ z → suc z Nat.≤ suc (suc (suc m₀))) (sym p) bd) ⦄
          , sym p
```
