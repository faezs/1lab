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

  -- The Integral Transformb


  -- Instead of a Ring we need a fibred bundle over R with a product path from

  Domain = Ob FinSets

  W X Y Z : Domain
  W = zero
  X = suc W
  Y = suc X
  Z = suc Y


  Ringed : Ob FinSets → Type ℓ
  Ringed W = R

  SpeciesF = Functor (Core FinSets) FinSets



  -- zeroS : SpeciesF
  -- zeroS = record { F₀ = 1Lab.Prelude.id ; F₁ = {!!} ; F-id = {!!} ; F-∘ = {!!} }

  -- decategorify : {F : SpeciesF} {X : Type} → (Ob FinSets) → ∥ Ob FinSets ∥₀ ≡ Nat
  -- decategorify zero = {!!}
  -- decategorify (suc x) = {!!}

  -- -- The integral transform is a polynomial span of the domain
  -- -- module IntegralTransform {d : Domain} {r : Ringed d} where
  Species : Type (lsuc lzero)
  Species = Σ (Type lzero) (λ x → Ob FinSets)





  -- NatSpecies : Species
  -- NatSpecies = record
  --   { F₀ = λ z → z
  --   ; F₁ = λ {x} {y} z z₁ → z .hom z₁
  --   ; F-id = λ i x → x
  --   ; F-∘ = λ f g i x → f .hom (g .hom x) }

  open import 1Lab.Equiv
  open import 1Lab.Equiv.Fibrewise
  open import Cat.Functor.Base
  open Ring-on (R' .snd) renaming (_+_ to _+R+_)




  -- fibre : (A → B) → B → Type _
  -- fibre {A = A} f y = Σ[ x ∈ A ] f x ≡ y

  -- we need a fibred bundle over (X, R)
  F = fibre {_} {Domain} {_} (λ x → Ringed x)

  NatF : F R
  NatF = W , (λ i → R)
  -- fiberwiseProduct : ?

  _^_ : (a b : Ob (Core FinSets)) (c : Hom (Core FinSets) a b) → Nat → (a ^ n) ? (b ^ n)
  c ^ i = length (c .Ob)

  open import Algebra.Ring.Module.Vec
  open import Algebra.Ring.Module
  instance
    d-variables : ∀ {d : Ob FinSets} → Functor ((Core FinSets) ^ d) (R-Mod R' ℓ)
    d-variables = record { F₀ = λ x → {!!}
                         ; F₁ = {!!}
                         ; F-id = {!!}
                         ; F-∘ = {!!} }

  -- This is a 3 Variable Species where each variable is a Projection Functor
  open import Data.Fin
  Ix : (n : Nat) → Type ℓ
  Ix i = (Fin i) → R

  Ix' : (n m : Nat) → Type ℓ
  Ix' i j = Ix i × Ix j

  Ix'' : (n m o : Nat) → Type ℓ
  Ix'' i j k = Ix' i j × Ix k


  data EinΣ {i j k : Nat} {I : Ix i} {J : Ix j} {K : Ix k} : Type ℓ where
    -- trace
    ii→ : (Ix' i i → R) → EinΣ
    -- diagonal
    ii→i : (Ix' i i → Ix i) → EinΣ
    -- outer product
    i,j→ij : (Ix' i j → Ix' i j) → EinΣ
    -- sum over first axis
    ij→j : Ix' i j → Ix j → EinΣ
    -- matrix transpose
    ij→ji : (Ix' i j → Ix' j i) → EinΣ
    -- matrix multiplication
    ij,jk→ik : (Ix' i j × Ix' j k)
             → Ix' i k
             → EinΣ

  trace : Σ[ i ∈ Nat ] R → R
  trace (zero , r) = r
  trace (suc i , r) = r +R+ trace (i , r)

  matmul : ∀ {i j k : Nat} → (Σ[ i' ∈ Ix i ] Σ[ j' ∈ Ix j ] R × Σ[ j'' ∈ Ix j ] Σ[ k' ∈ Ix k ] R)
                           → Σ[ i' ∈ Ix i ] Σ[ k' ∈ Ix k ] R
  matmul (i , (j , (r , (j' , k , r')))) = {!!} , {!,!} , {!!}


  eval : ∀ {i j k : Nat} {I : Ix i} {J : Ix j} {K : Ix k} → EinΣ {i} {j} {k} {I} {J} {K} → ⊤
  eval = {!!}


  _×F_ : ∀ {I I' : Type ℓ} → (F : I → I → R) (G : I' → I' → R) → ((I × I') → (I × I') → R × R)
  (F ×F G)  (x , y) (x' , y') = F x x' , G y y'

--   _·→_·→_·→_ : ∀ {I I'} {F F'} → EinΣ' {I} {F} → EinΣ' {I'} {F'} → Type ℓ
--   i ·→ x ·→ y ·→ z = ?





--   cast : Nat → R
--   cast zero = Ring-on.0r (R' .snd)
--   cast (suc z) = 1r +R+ (cast z)

--   EinΣ = EinΣ' {Nat} {λ x y → cast (x + y)}
--   open import Data.Nat

--   idEΣ : EinΣ
--   idEΣ = ii→ (λ z → Ring-on.1r (R' .snd))

--   evalE : EinΣ → F R
--   evalE (ii→ x) = {!!}
--   evalE (ii→i x) = W , (λ i → ∣ R' .fst ∣)
--   evalE (i,j→ij x) = W , (λ i → ∣ R' .fst ∣)
--   evalE (ij→j x) = {!!} , {!!}
--   evalE (ij→ji x) = {!!}
--   evalE (ij,jk→ik x) = {!!}


--   instance

--     EinΣC : Precategory ℓ ℓ
--     EinΣC = record
--              { Ob = EinΣ
--              ; Hom = _·→·→·_
--              ; Hom-set = {!!}
--              ; id = λ {x} → {!!}
--              ; _∘_ = λ {x} {y} {z} x y → {!!}
--              ; idr = {!!}
--              ; idl = {!!}
--              ; assoc = {!!}
--              }
--           where
--             open Ring-on (R' .snd)

--   EinΣR : EinΣC .Ob → R
--   EinΣR = λ z → Ring-on.1r (R' .snd)


--   -- instance
--   --   einsumFunctor : Functor (EinΣC) (F Domain)
--   --   einsumFunctor = ?



--   ·→·→·-hom : EinΣ → EinΣ → Type (lsuc ℓ)
--   ·→·→·-hom a b = Type ℓ

--   ·→·→·C :  ∀ {a b} → Precategory a b
--   ·→·→·C = precat where
--     open Precategory
--     precat = {!!}
-- ```
