<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Instances.Functor
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

import Cat.Reasoning

open Chain-map
open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Functorial where
```

# The inverse Dold–Kan construction is a functor

The [[inverse Dold–Kan construction|dold-kan]] was built one chain
complex at a time. But its very presentation — $\Gamma(C)_n$ is the
group of chain maps $N\bZ[\Delta^n] \to C$ — makes it functorial in
$C$ for free: a chain map $f : C \to D$ acts by postcomposition, and
every law is an associativity or unit law of the category of chain
complexes.

<!--
```agda
private
  module ChC = Cat.Reasoning (Ch lzero)
```
-->

```agda
Γ-functor : Functor (Ch lzero) Cat[ Δ ^op , Ab lzero ]
Γ-functor .F₀ = Γ
Γ-functor .F₁ f .η n .∫Hom.fst φ = f ChC.∘ φ
Γ-functor .F₁ f .η n .∫Hom.snd .is-group-hom.pres-⋆ φ ψ =
  Chain-map-path λ k → ext λ x p →
    is-group-hom.pres-⋆ (f .map k .∫Hom.snd) _ _
Γ-functor .F₁ f .is-natural n n' g = ext λ φ →
  ChC.assoc f φ (NΔ-map g)
Γ-functor .F-id = ext λ n φ → ChC.idl φ
Γ-functor .F-∘ f g = ext λ n φ → sym (ChC.assoc f g φ)
```
