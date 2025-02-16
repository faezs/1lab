```
module Cat.Instances.Species where

open import Cat.Functor.Base
open import Cat.Instances.Core
open import Cat.Instances.FinSets
open import Cat.Functor.WideSubcategory
open import Cat.Prelude

open import Algebra.Group.Instances.Symmetric
open import Algebra.Group.Action
open import 1Lab.Prelude

FinSetSpecies : Functor (Core (FinSets)) FinSets
FinSetSpecies .Functor.F₀ = λ z → z
FinSetSpecies .Functor.F₁ = λ z → z .Wide-hom.hom
FinSetSpecies .Functor.F-id = λ i x₁ → x₁
FinSetSpecies .Functor.F-∘ = λ f g i x₁ → f .hom (g .hom x₁)

-- let Aⁿ be the set of cyclic orderings
-- of [1..n]
open import Data.List

-- Helper function to rotate a list by n positions
rotate : ∀ {A : Type} → Nat → List A → List A
rotate zero xs = xs
rotate (suc n) [] = []
rotate (suc n) (x ∷ xs) = rotate n xs <> (x ∷ [])

upto : Nat → List Nat
upto zero = 0 ∷ []
upto (suc n) = (suc n) ∷ upto n

-- Helper function to get all rotations of a list
allRotations : ∀ {A : Type}  → List A → List (List A)
allRotations xs = Map.map Map-List (λ (n : Nat) → rotate n xs) (upto ∘ length $ xs)


cyclicOrderings : Nat -> List (List Nat)
cyclicOrderings = allRotations {Nat} ∘ upto

```
```
open import Algebra.Ring
module TensorSpecies {ℓ} ⦃ R' : Ring ℓ ⦄ where
  open Precategory
  open Algebra.Ring
  open import 1Lab.Underlying

  R = ⌞ R' ⌟

  -- The Integral Transform
  ·→·→·C :  ∀ {a b} → Precategory a b


  -- Instead of a Ring we need a fibred bundle over R with a product path from

  data Domain :  Type ℓ where
    W : Domain
    X : Domain
    Y : Domain
    Z : Domain


  Ringed : Domain → Type ℓ
  Ringed W = R
  Ringed X = R
  Ringed Y = R
  Ringed Z = R

  Species = Functor (Core FinSets) FinSets

  NatSpecies : Species
  NatSpecies = record
    { F₀ = λ z → z
    ; F₁ = λ {x} {y} z z₁ → z .hom z₁
    ; F-id = λ i x → x
    ; F-∘ = λ f g i x → f .hom (g .hom x) }

  open import 1Lab.Equiv
  open import 1Lab.Equiv.Fibrewise
  open import Cat.Functor.Base
  open Ring-on (R' .snd) renaming (_+_ to _+R+_)




  -- fibre : (A → B) → B → Type _
  -- fibre {A = A} f y = Σ[ x ∈ A ] f x ≡ y

  -- we need a fibred bundle over (X, R)
  F = fibre {_} {Domain} {_} (λ x → Ringed x)
  NatF : F R
  NatF = W , (λ i → ∣ R' .fst ∣)
  -- fiberwiseProduct : ?

  data EinΣ' {I : Type} {F : I → I → R} : Type ℓ where
    -- trace
    ii→ : (Σ[ i ∈ I × I ] R → R) → EinΣ'
    -- diagonal
    ii→i : (Σ[ i ∈ I ] R → Σ[ i ∈ I ] R) → EinΣ'
    -- outer product
    i,j→ij : (Σ[ i ∈ I ] R × Σ[ j ∈ I ] R → Σ[ i ∈ I ] Σ[ j ∈ I ] R ) → EinΣ'
    -- sum over first axis
    ij→j : (Σ[ i ∈ I ] Σ[ j ∈ I ] R → Σ[ j ∈ I ] R) → EinΣ'
    -- matrix transpose
    ij→ji : (Σ[ i ∈ I ] Σ[ j ∈ I ] R → Σ[ j ∈ I ] Σ[ i ∈ I ] R) → EinΣ'
    -- matrix multiplication
    ij,jk→ik : (Σ[ i ∈ I ] Σ[ j ∈ I ] R × Σ[ j ∈ I ] Σ[ k ∈ I ] R
             → Σ[ i ∈ I ] Σ[ k ∈ I ] R)
             → EinΣ'

  trace : Σ[ i ∈ Nat ] R → R
  trace (zero , r) = r
  trace (suc i , r) = r +R+ trace (i , r)

  fiberwiseProduct : {I : Type ℓ} → (I → I → Type ℓ) → (I → I → Type ℓ)
  fiberwiseProduct {I} F = λ x y → Σ[ i ∈ I ] (F i x × F i y)

  _·→·→·_ : EinΣ' → EinΣ' → Type ℓ
  _·→·→·_ = λ x y → fiberwiseProduct (λ x y → ∣ R' .fst ∣) x y





  cast : Nat → R
  cast zero = Ring-on.0r (R' .snd)
  cast (suc z) = 1r +R+ (cast z)

  EinΣ = EinΣ' {Nat} {λ x y → cast (x + y)}
  open import Data.Nat

  idEΣ : EinΣ
  idEΣ = ii→ (λ z → Ring-on.1r (R' .snd))

  evalE : EinΣ → F R
  evalE (ii→ x) = {!x .snd!}
  evalE (ii→i x) = W , (λ i → ∣ R' .fst ∣)
  evalE (i,j→ij x) = W , (λ i → ∣ R' .fst ∣)
  evalE (ij→j x) = {!!} , {!!}
  evalE (ij→ji x) = {!!}
  evalE (ij,jk→ik x) = {!!}


  instance

    EinΣC : Precategory ℓ ℓ
    EinΣC = record
             { Ob = EinΣ
             ; Hom = _·→·→·_
             ; Hom-set = {!!}
             ; id = λ {x} → {!!}
             ; _∘_ = λ {x} {y} {z} x y → {!!}
             ; idr = {!!}
             ; idl = {!!}
             ; assoc = {!!}
             }
          where
            open Ring-on (R' .snd)

  EinΣR : EinΣC .Ob → R
  EinΣR = λ z → Ring-on.1r (R' .snd)


  -- instance
  --   einsumFunctor : Functor (EinΣC) (F Domain)
  --   einsumFunctor = ?



  ·→·→·-hom : EinΣ → EinΣ → Type (lsuc ℓ)
  ·→·→·-hom a b = Type ℓ

  ·→·→·C = precat where
    open Precategory
    precat = {!!}
```
