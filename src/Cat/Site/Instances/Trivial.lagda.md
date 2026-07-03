<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open is-precat-iso
open Coverage
open Functor
```
-->

```agda
module Cat.Site.Instances.Trivial {o ℓ} (C : Precategory o ℓ) where
```

# The trivial coverage {defines="trivial-coverage"}

Every category carries the **trivial coverage**, with no covering
families at all. Gluing is then vacuous: *every* presheaf is a sheaf,
and the sheaf topos is the presheaf topos. This is not a degenerate
curiosity: the simplicial and infinitesimal directions of the sites
of physics carry exactly this coverage — their probes are not glued
from smaller probes.

```agda
Trivial-coverage : Coverage C lzero
Trivial-coverage .covers _ = Lift lzero ⊥
Trivial-coverage .cover c = absurd (c .Lift.lower)
Trivial-coverage .stable c f = absurd (c .Lift.lower)

trivial-is-sheaf
  : ∀ {ℓs} (F : Functor (C ^op) (Sets ℓs))
  → is-sheaf Trivial-coverage F
trivial-is-sheaf F = from-is-sheaf₁ λ c → absurd (c .Lift.lower)
```

Consequently the forgetful functor from trivial-coverage sheaves to
presheaves is an isomorphism of precategories: it is the inclusion of
a full subcategory on a propositional condition that always holds.

```agda
forget-trivial-is-precat-iso
  : ∀ {ℓs} → is-precat-iso (forget-sheaf Trivial-coverage ℓs)
forget-trivial-is-precat-iso .has-is-ff = id-equiv
forget-trivial-is-precat-iso .has-is-iso = is-iso→is-equiv λ where
  .is-iso.from F → F , trivial-is-sheaf F
  .is-iso.rinv F → refl
  .is-iso.linv (F , p) → Σ-prop-path (λ _ → hlevel 1) refl
```
