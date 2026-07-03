<!--
```agda
open import Cat.Instances.SimplicialSets.Nerve
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Instances.Product
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

open import Algebra.Monoid

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.SimplicialPresheaves
  (C : Precategory lzero lzero)
  where
```

# Simplicial presheaves {defines="simplicial-presheaf"}

The paper's (36) forms, from a site of geometric probes and the site
of simplices, the presheaves on their *product*: a **simplicial
presheaf** assigns a set of plots to every pair (geometric shape,
gauge shape), restricting contravariantly in both. These are the
ambient objects for higher gauge theory prior to any localisation:
smooth higher groupoids are the fibrantly-resolved among them.

```agda
sPSh : Precategory (lsuc lzero) lzero
sPSh = PSh lzero (C ×ᶜ Δ)
```

Every simplicial set gives a simplicial presheaf constant in the
geometric direction, by restricting along the projection.

```agda
constᵟ : ⌞ sSet ⌟ → ⌞ sPSh ⌟
constᵟ K = K F∘ Functor.op (Snd {C = C} {D = Δ})
```

Dually, every presheaf on the geometric site gives a simplicial
presheaf constant in the gauge direction — a *simplicially discrete*
object.

```agda
constᵍ : ⌞ PSh lzero C ⌟ → ⌞ sPSh ⌟
constᵍ K = K F∘ Functor.op (Fst {C = C} {D = Δ})
```

The paper's (37): plots of shape $(U, \Delta^2)$ of the (constant)
delooping of a monoid are exactly pairs of elements — the higher
gauge structure of the delooping is visible at every geometric
stage. This is the Yoneda lemma composed with the [[nerve
computation|simplicial-delooping]] of the previous section.

```agda
plots-Δ²-BM
  : ∀ {M : Type} (mm : Monoid-on M) (U : ⌞ C ⌟)
  → (よ₀ (C ×ᶜ Δ) (U , 2) => constᵟ (nerve-B mm))
  ≃ (M × M)
plots-Δ²-BM mm U =
  Equiv.inverse (yo (constᵟ (nerve-B mm)) , yo-is-equiv (constᵟ (nerve-B mm)))
  ∙e nerve-B₂≃M×M mm
```

The genuinely higher content of (36) — the *local* homotopy theory
of simplicial presheaves, in which (37) holds after fibrant
resolution for arbitrary coefficients — is the simplicial
localisation that remains future work.
