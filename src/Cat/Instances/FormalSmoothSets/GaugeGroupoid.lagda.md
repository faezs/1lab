<!--
```agda
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Instances.Functor
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Group.Ab

open import Algebra.ChainComplex.DoldKan.Functorial
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

import Cat.Instances.FormalSmoothSets

open Functor
```
-->

```agda
module Cat.Instances.FormalSmoothSets.GaugeGroupoid (R : CRing lzero) where
```

<!--
```agda
open Cat.Instances.FormalSmoothSets R
open import Cat.Instances.FormalSmoothSets.Deligne R
```
-->

# The smooth groupoid of gauge fields {defines="gauge-groupoid"}

Composing the [[Deligne complex|deligne-complex]] with the
functorial [[inverse Dold–Kan construction|dold-kan]] produces, one
probe at a time, the simplicial abelian group of gauge fields on
that probe: its vertices are $1$-forms, its edges are gauge
transformations by functions, and the gauge transformations
themselves carry a discrete integer ambiguity. This is the moduli
stack $\mathbf{B}U(1)_\mathrm{conn}$ of electromagnetism, presented
as a simplicial presheaf on the site of thickened affine spaces.

```agda
BU1-conn : Functor (ThCartSp ^op) Cat[ Δ ^op , Ab lzero ]
BU1-conn = Γ-functor F∘ Deligne²

BU1-conn-sset : Functor (ThCartSp ^op) Cat[ Δ ^op , Sets lzero ]
BU1-conn-sset = postcompose Ab↪Sets F∘ BU1-conn
```

Because it is valued in simplicial abelian *groups*, [[Moore's
theorem|kan-complex]] applies probe-wise: every value of the
presheaf is a Kan complex, so the object is fibrant in the way that
matters for computing with it — every probe-wise horn has a filler.

```agda
BU1-conn-kan : (U : ThAff) → is-kan (BU1-conn-sset .F₀ U)
BU1-conn-kan U = sab-is-kan (BU1-conn .F₀ U)
```
