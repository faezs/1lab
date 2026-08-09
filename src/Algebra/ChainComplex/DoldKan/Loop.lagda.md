<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Instances.Functor
open import Cat.Functor.Base
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan.Functorial
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

import Cat.Reasoning

open Chain-complex
open Chain-map
open Functor
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Loop where
```

# The loop-space property of Eilenberg–MacLane objects

The defining structural property of the [[Eilenberg–MacLane
objects|eilenberg-maclane]] is that each is the *loop space* of the
next: $\mathbf{B}^n A \simeq \Omega\, \mathbf{B}^{n+1} A$. Under the
[[Dold–Kan correspondence|dold-kan]], the loop-space functor on
simplicial abelian groups is presented by the **shift** of chain
complexes — forgetting degree zero and reindexing — so the property
becomes a computation with complexes concentrated in a single
degree: shifting the complex concentrated in degree $n+1$ gives, on
the nose, the complex concentrated in degree $n$, and the
now-functorial $\Gamma$ transports the isomorphism to the
simplicial world.

```agda
Ω-chain : ∀ {ℓ} → Chain-complex ℓ → Chain-complex ℓ
Ω-chain C .ob n = C .ob (suc n)
Ω-chain C .∂ᶜ n = C .∂ᶜ (suc n)
Ω-chain C .∂ᶜ-∂ᶜ n = C .∂ᶜ-∂ᶜ (suc n)
```

<!--
```agda
private
  module ChC = Cat.Reasoning (Ch lzero)
  module sAb = Cat.Reasoning Cat[ Δ ^op , Ab lzero ]
```
-->

Because the concentrated complex is defined by recursion on the
degree, the shift of the $(n+1)$-concentrated complex is
*definitionally* the $n$-concentrated complex, level by level and
boundary by boundary; the isomorphism is the identity in every
degree.

```agda
loop-concentrated
  : (A : Abelian-group lzero) (n : Nat)
  → ChC.Isomorphism (Ω-chain (concentrated A (suc n))) (concentrated A n)
loop-concentrated A n = ChC.make-iso to from invl invr where
  to : Chain-map (Ω-chain (concentrated A (suc n))) (concentrated A n)
  to .map k = Ab lzero .Precategory.id
  to .comm k x = refl

  from : Chain-map (concentrated A n) (Ω-chain (concentrated A (suc n)))
  from .map k = Ab lzero .Precategory.id
  from .comm k x = refl

  invl : to ChC.∘ from ≡ ChC.id
  invl = Chain-map-path λ k → ext λ x → refl

  invr : from ChC.∘ to ≡ ChC.id
  invr = Chain-map-path λ k → ext λ x → refl
```

Applying $\Gamma$ gives the loop-space property itself, as an
isomorphism of simplicial abelian groups. What is chain-level about
this presentation is only the *model* of $\Omega$: identifying
$\Gamma$ of the shift with the simplicial loop space of the
underlying Kan complex is part of the full Dold–Kan equivalence.

```agda
K-loop
  : (A : Abelian-group lzero) (n : Nat)
  → sAb.Isomorphism (Γ (Ω-chain (concentrated A (suc n)))) (K A n)
K-loop A n = F-map-iso Γ-functor (loop-concentrated A n)
```
