module Cat.Instances.OpenMechanicalSystems where

open import 1Lab.Reflection.Induction

open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Instances.Graphs
open import Cat.Functor.Adjoint
open import Cat.Instances.Free
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Strict

import Cat.Functor.Reasoning
import Cat.Reasoning


{-
We have two descriptions of open mechanical systems:
 - Lagrangian
 - Hamiltonian
The morphisms in these categories are spans or cospans with additional structure.


So naturally we have the Legendre transformation as a functor between them.

In order to solve the systems, we need to solve differential equations that describe paths
on general Riemannian and symplectic manifolds.

The state space in the legrangian description is a riemannian manifold,
and the state space in the hamiltonian description is a symplectic manifold.

a path in the state space models the motion of the system.

the state space of any subsystem is a quotient space of the entire state space.

for lagrangian systems, the quotient maps are surjective Riemannian submersions.
for hamiltonian systems, the quotient maps are surjective Poisson maps between symplectic manifolds.



The goal here is to construct said categories and functor.

TODO:
  Define smooth manifolds and their morphisms.

-}


record RiemannianManifold : Type where

-- data OpenMechanicalSystem (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where

record OpenMechanicalSystem (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    graph : Graph o ℓ


--   open Graph graph public

--   field
--     Marked : ∀ {x y} → Path-in graph x y → Path-in graph x y → Ω
