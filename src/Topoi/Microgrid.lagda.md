<!--
{-# OPTIONS -v refl:20 #-}
{-# OPTIONS --without-K --exact-split --rewriting #-}
```agda
open import 1Lab.Prelude hiding (_∘_)
open import Data.Nat
open import Cat.Functor.Hom
open import Cat.Prelude hiding (Nat-is-set)
open import Cat.Instances.MarkedGraphs
open import Data.Bool

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

open import Algebra.Ring
open import Algebra.Ring.Module
open import Algebra.Ring.Module.Vec


open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection.Record
open import 1Lab.HLevel.Universe
open import 1Lab.Extensionality
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
--open import 1Lab.Underlying hiding (Σ-syntax)
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)
```
-->


```agda

module Topoi.Microgrid  (R'' : Ring lzero) (L : Module R'' lzero) (E : Module R'' lzero) where

open import Data.Sum



open import Algebra.Group.Ab


open module Ra = Ring-on (R'' .snd)
open module ML = Module-on (L .snd)

R = ⌞ R''  ⌟

M = ⌞ L  ⌟

R-is-set = +-group .is-abelian-group.has-is-set




R3 = Nat × Nat × Nat

Rⁿ : ∀ (n : Nat) → Type lzero
Rⁿ n = R

Rⁿ-Mod : ∀ (n : Nat) → Module R'' lzero
Rⁿ-Mod n = Fin-vec-module R'' n


open import Data.Fin

record Storage : Type where
  constructor storage
  field
    capacity : R
    storing : R
    input : R
    output : R

unquoteDecl storage-iso = declare-record-iso storage-iso (quote Storage)

storage-is-set : is-set Storage
storage-is-set = Iso→is-hlevel 2 storage-iso
  (Σ-is-hlevel 2 R-is-set λ _ →
    Σ-is-hlevel 2 R-is-set λ _ →
      Σ-is-hlevel 2 R-is-set λ _ →
        R-is-set)



instance
  appendStorage : Append Storage
  appendStorage = record
    { mempty = storage 0r 0r 0r 0r
    ; _<>_ = λ (storage c s i o) (storage c' s' i' o') →
        storage (c Ra.+ c') (s Ra.+ s') (i Ra.+ i') (o Ra.+ o')
    }

record Generator : Type where
  constructor gen
  field
    capacity : R
    producing : R

unquoteDecl generator-iso = declare-record-iso generator-iso (quote Generator)

generator-is-set : is-set Generator
generator-is-set = Iso→is-hlevel 2 generator-iso (Σ-is-hlevel 2 R-is-set λ _ → R-is-set)

instance
  genMonoid : Append Generator
  genMonoid = record
    { mempty = gen 0r 0r
    ; _<>_ = λ (gen c p) (gen c' p') → gen (c Ra.+ c') (p Ra.+ p')
    }

record Consumption : Type where
  constructor consume
  field
    consume : R

unquoteDecl consumption-iso = declare-record-iso consumption-iso (quote Consumption)

consumption-is-set : is-set Consumption
consumption-is-set = Iso→is-hlevel 2 consumption-iso R-is-set

instance
  consumeMonoid : Append Consumption
  consumeMonoid = record
    { mempty = consume 0r
    ; _<>_ = λ (consume c) (consume c') → consume (c Ra.+ c')
    }

record Node : Type lzero where
  constructor node
  field
    nodeId : Nat
    genₙ : Generator
    storageₙ : Storage
    consumeₙ : Consumption

unquoteDecl node-iso = declare-record-iso node-iso (quote Node)


node-is-set : is-set Node
node-is-set = Iso→is-hlevel 2 node-iso
      (Σ-is-hlevel 2 Nat-is-set λ _ →
        Σ-is-hlevel 2 generator-is-set λ _ →
        Σ-is-hlevel 2 storage-is-set λ _ →
        consumption-is-set)

instance
  H-Level-Node : ∀ {n} → H-Level Node (2 Data.Nat.+ n)
  H-Level-Node = basic-instance 2 node-is-set

zeroNode : Node
zeroNode = node 0 mempty mempty mempty

nodeAppend : Node -> Node -> Node
nodeAppend (node i g u s) (node i' g' u' s') = node (max i i') (g <> g') (u <> u') (s <> s')

instance
  appendNode : Append Node
  appendNode = record
    { mempty = zeroNode
    ; _<>_ = nodeAppend
    }

_⇒mor_ : Node → Node → Type lzero
_⇒mor_ x y = Nat


origin : R3
origin = zero , (zero , zero)

cong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (x y : A) → x ≡ y → f x ≡ f y
cong f x y p = λ i → f (p i)

microgrid-graph : Marked-graph (lzero) lzero
microgrid-graph = record
  { graph = record
      { Vertex = Node
      ; Edge = _⇒mor_
      ; Vertex-is-set = node-is-set
      ; Edge-is-set = Nat-is-set
      }
  ; Marked = λ x x₁ → el ⊤ (λ x₂ y i → tt)
  }


-- Now that we have a notion of graph, lets have its category
microgrid-cat : Precategory (lzero) (lzero ⊔ lzero)
microgrid-cat = Marked-path-category (microgrid-graph)

open import Cat.Instances.Sheaves 
open import Cat.Site.Base 
open import Cat.Diagram.Sieve
open import Data.Power
open import Cat.Instances.Free

-- now we need a coverage
open Precategory microgrid-cat
open Path-in
cellular-cover : (c : ⌞ microgrid-cat ⌟ ) → Cover microgrid-cat c _
cellular-cover c .Cover.index = Nat
cellular-cover c .Cover.domain = λ (b : Nat) → c
cellular-cover (node nodeId genₙ storageₙ consumeₙ) .Cover.map zero =
  glue (cons nodeId nil , cons nodeId nil , reflexive) i1
cellular-cover (node nodeId genₙ storageₙ consumeₙ) .Cover.map (suc n) =
  glue (cons nodeId nil , cons nodeId nil , reflexive) i0

cellular-sieve : (c : ⌞ microgrid-cat ⌟ ) →  Sieve microgrid-cat c
cellular-sieve c = cover→sieve (cellular-cover c)

mg-coverage : Coverage microgrid-cat (lzero)
mg-coverage .covers = λ z → ∣ R'' .fst ∣
mg-coverage .cover = λ c → maximal'
mg-coverage .stable {U} {V} = λ R₁ f → inc (1r , (λ {V = V₁} h _ → tt))


sh = Sh[ microgrid-cat , mg-coverage ]

open import Cat.Functor.Base
open import Topoi.Base


mc-topos : Topos _ (PSh _  microgrid-cat)
mc-topos = Presheaf microgrid-cat


open import Algebra.Group


-- Here we want to assign modules to vertices and linear maps to edges.
-- But we also want transition maps
-- a : {n : Nat} → Sheaf mg-coverage (lsuc lzero)
-- a {n} = f , is-sh
--   where
--     open Module-on
--     h : is-hlevel (Module R'' lzero) 2
--     h = ?
--     f : Functor (microgrid-cat ^op) (Sets (lsuc lzero))
--     f .Functor.F₀ (node nodeId genₙ storageₙ consumeₙ) = el (Module R'' lzero) h
--     f .Functor.F₁ x y = {!!} , {!!}
--     f .Functor.F-id = {!!}
--     f .Functor.F-∘ = {!!}
--     is-sh : is-sheaf mg-coverage f
--     is-sh  .whole = λ S p → p .part (inc nil) tt
--     is-sh  .glues = λ S p f₁ hf → {!!}
--     is-sh  .separate = λ c x → {!!}

-- open import Cat.Displayed.Total

-- microgrid-sheaf : Functor microgrid-cat (R-Mod R'' lzero)
-- microgrid-sheaf = f
--   where
--     -- Helper to get a module based on node structure
--     node→mod : Node → Module R'' lzero
--     node→mod (node i g s c) = Rⁿ-Mod 3  -- Using dimension 3 for (gen, stor, cons)


--     edge→mod : ∀ {a b : Node} → Hom a b → Linear-map (node→mod a) (node→mod b)
--     edge→mod {a} {b}  = λ f → record { map = λ x x₁ → 1r ; lin = {!!} }

--     f : Functor (microgrid-cat) (R-Mod R'' lzero)
--     f .Functor.F₀ n = node→mod n

--     -- Morphisms go to linear maps
--     f .Functor.F₁ {x} {y} mor .Total-hom.hom = {!!}
--     f .Functor.F₁ {x} {y} mor .Total-hom.preserves = {!!}

--     f .Functor.F-id = {!!}
--     f .Functor.F-∘ = {!!}


```

```agda



module New {ℓ  ℓ' : Level} where
  open import 1Lab.Path
  open import 1Lab.HLevel
  open import 1Lab.Type
  open import 1Lab.Type.Sigma
  open import 1Lab.Equiv
  open import 1Lab.Equiv.Fibrewise
  open import 1Lab.HLevel
  open import 1Lab.Univalence
  open import 1Lab.Path.Groupoid
  open import 1Lab.Path.Cartesian
  open import Cat.Reasoning
  open import 1Lab.Path.Reasoning

  -- Fibration structure
  record Fibration {ℓ ℓ'} (E : Type ℓ) (B : Type ℓ') : Type ((lsuc ℓ) ⊔ ℓ') where
    field
      π : E → B
      total-fib : Type ℓ
      π-fib : (b : B) → Type ℓ
      is-fib : (b : B) → π-fib b ≃ (1Lab.Type.Σ[ e ∈ E ] π e ≡ b)
  open Fibration

  -- Base category of computational types
  record CompType : Type₁ where
    field
      carrier : Type
      is-computable : carrier → Type
      is-finite : Type

  -- Bundle of parameters with sharing structure
  record ParamBundle (B : Type) : Type₁ where
    field
      -- Total space of parameters
      Eₚ : Type
      -- Projection with fibration structure
      bundle : Fibration Eₚ B
      -- Local trivialization
      local-frame : (b : B) → bundle .π-fib b ≃ CompType
      -- Parameter sharing evidence
      sharing : (b₁ b₂ : B) → bundle .π-fib b₁ ≃ bundle .π-fib b₂
  open ParamBundle

  -- Twisted transport structure
  record Transport {B : Type} (P : ParamBundle B) : Type₁ where
    field
      -- Connection form
      connection : (b : B) → P .bundle .π-fib b → P .bundle .π-fib b
      -- Transport along paths
      transportₚ : {b₁ b₂ : B} → b₁ ≡ b₂
               → P .bundle .π-fib b₁ → P .bundle .π-fib b₂
      -- Transport preserves sharing
      transport-share : {b₁ b₂ : B} (p : b₁ ≡ b₂)
                     → (f₁ : P .bundle .π-fib b₁) (f₂ : P .bundle .π-fib b₂)
                     → transportₚ p f₁ ≡ f₂
                     → P .sharing b₁ b₂ .fst f₁ ≡ f₂
  open Transport

  -- Neural twisted bundle
  record NeuralTwist (B : Type) : Type₁ where
    field
      -- Parameter structure
      params : ParamBundle B
      -- Transport structure
      trans : Transport params
      -- Forward map
      forward : (b : B) → params .bundle .π-fib b → CompType
      -- Forward preserves sharing
      forward-share : (b₁ b₂ : B)
                   → (f₁ : params .bundle .π-fib b₁)
                   → (f₂ : params .bundle .π-fib b₂)
                   → params .sharing b₁ b₂ .fst f₁ ≡ f₂
                   → forward b₁ f₁ ≡ forward b₂ f₂
  open NeuralTwist

  -- Holonomy computation
  module Holonomy {B : Type} (N : NeuralTwist B) where
    -- Path transport
    transport-pathₚ : {b₁ b₂ : B} → b₁ ≡ b₂
                  → N .params .bundle .π-fib b₁
                  → N .params .bundle .π-fib b₂
    transport-pathₚ = N .trans .transportₚ

    -- Holonomy around loop
    holonomy : {b : B} → (p : b ≡ b)
             → N .params .bundle .π-fib b
             → N .params .bundle .π-fib b
    holonomy p f = transport-pathₚ p f

  --   -- Holonomy preserves sharing
  --   holonomy-share : {b : B} → (p : b ≡ b)
  --              → (f₁ f₂ : N .params .bundle .π-fib b)
  --              → N .params .sharing b b .fst f₁ ≡ f₂
  --              → holonomy p f₁ ≡ holonomy p f₂
  --   holonomy-share {b = b} p f₁ f₂ h = {!!}


  -- -- Example instantiation
  -- module Example where
  --   -- Base space of patches
  --   data Patchₙ : Type where
  --     p₁ p₂ p₃ p₄ : Patchₙ

  --   -- Parameter type
  --   record Params : Type (lsuc ℓ) where
  --     field
  --       weights : CompType
  --       bias : CompType

  --   -- Build neural twisted bundle
  --   neural-bundle : NeuralTwist Patchₙ
  --   neural-bundle = record { params = {!!}
  --                          ; trans = {!!}
  --                          ; forward = {!!}
  --                          ; forward-share = {!!}
  --                          } -- Implementation here




module Cellular-Sheaf where
  -- 1. Stalks using proper Fin-vec structure
  Stalk : Module R'' lzero
  Stalk = Fin-vec-module R'' 2

  -- 2. Edge spaces also as proper Fin-vecs
  F-edge : Ob -> Ob → Module R'' lzero
  F-edge v u = Fin-vec-module R'' 4

  -- 3. Restriction maps using Linear-map structure
  F-restrict : (v u : Ob) → Hom v u
            → Linear-map Stalk (F-edge v u)
  F-restrict v u e = record { map = {!!} ; lin = {!!} }

  F-restrict-opp : (v u : Ob) → Hom v u
                → Linear-map Stalk (F-edge v u)
  F-restrict-opp v u e = record { map = {!!} ; lin = {!!} }

  -- 4. 0-cochains
  C⁰ : Type lzero
  C⁰ = (v : ⌞ microgrid-cat ⌟) →  ⌞ Stalk ⌟

  -- -- 5. Global sections
  -- H⁰ : Type lzero
  -- H⁰ = 1Lab.Type.Σ[ x ∈ C⁰ ]
  --      ((v u : ⌞ microgrid-cat ⌟) → (e : v u) →
  --        F-restrict v u e .map (x v) ≡ F-restrict-opp u v e .map (x u))


```
