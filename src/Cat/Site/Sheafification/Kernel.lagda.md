<!--
```agda
open import Cat.Site.Sheafification
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Data.Set.Coequaliser

import Cat.Site.Sheafification.Plus
import Cat.Site.Sheafification.Glue

open Functor
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Kernel
  {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  (A : Functor (C ^op) (Sets ℓ))
  where
```

<!--
```agda
open Precategory C
open Sheafification J A

private
  module S = Small J
  module P = Cat.Site.Sheafification.Plus J A
  module G = Cat.Site.Sheafification.Glue J
  module PC (U : ⌞ C ⌟) = Congruence (P.Loc-congruence U)
```
-->

# The kernel of the sheafification unit {defines="sheafification-kernel"}

This module assembles the [[separated quotient|separated-quotient]]
and the [[plus-construction|plus-construction-gluing]] into the
theorem the whole development has been aiming at: the unit of the
higher-inductive [[sheafification]] identifies two sections **if and
only if** they are [[locally equal|separated-quotient]] — over an
arbitrary coverage, with no choice principles.

The detecting sheaf is the plus-construction of the separated
quotient: a sheaf receiving $A$ through a map whose kernel is, by
construction, exactly saturated local equality.

```agda
A₁⁺ : Functor (C ^op) (Sets ℓ)
A₁⁺ = G.B⁺ P.A₁ P.A₁-is-separated

A₁⁺-is-sheaf : is-sheaf J A₁⁺
A₁⁺-is-sheaf = G.B⁺-is-sheaf P.A₁ P.A₁-is-separated

φ : A => A₁⁺
φ .η U x = G.unit⁺ P.A₁ P.A₁-is-separated (inc x)
φ .is-natural U V f = funext λ x →
  G.unit⁺-natural P.A₁ P.A₁-is-separated f (inc x)
```

By the universal property of the sheafification, $\varphi$ extends
along the unit; naturality of the extension turns a path of units
into a path of $\varphi$-images, injectivity of the
plus-construction's unit turns that into a path in the quotient, and
effectivity of the quotient turns *that* into a local equality.

```agda
private
  r : Sheafify => A₁⁺
  r = S.univ A₁⁺ A₁⁺-is-sheaf φ

encode
  : ∀ {U} {x y : A ʻ U}
  → Path (Sheafify₀ U) (inc x) (inc y)
  → P.Loc-eq x y
encode {U} {x} {y} p = PC.effective U
  (G.unit⁺-injective P.A₁ P.A₁-is-separated
    (ap (r .η U) p))
```

Together with the decode direction proven alongside the quotient,
the path space of the unit is completely characterised:

```agda
unit-kernel
  : ∀ {U} (x y : A ʻ U)
  → (Path (Sheafify₀ U) (inc x) (inc y)) ≃ P.Loc-eq x y
unit-kernel x y = prop-ext (squash _ _) P.squash
  encode P.loc-eq→inc-path
```

This closes the path-space problem for the one-step
higher-inductive sheafification. What remains for the `Topos`{.Agda}
instance is the deduction of pullback preservation from this
characterisation — locally, every element of a sheafification is an
inclusion, and the kernel theorem descends equality in the base of
a pullback to *local, on-the-nose* equality, where pairs can be
formed and glued — followed by the packaging of left exactness.
