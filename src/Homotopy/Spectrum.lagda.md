<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Loopspace
open import Homotopy.Base
```
-->

```agda
module Homotopy.Spectrum where
```

# Spectra {defines="spectrum prespectrum omega-spectrum"}

In the homotopy-theoretic dictionary, *linearity* is infinite
deloopability: an abelian-group-like object is a pointed space $E_0$
together with a delooping $E_1$, a delooping $E_2$ of that, and so on
— equivalently, a sequence of pointed spaces with maps

$$
E_0 \to \Omega E_1 \to \Omega^2 E_2 \to \cdots
$$

This is a **prespectrum**; it is an **$\Omega$-spectrum** when the
structure maps are equivalences, so that every $E_n$ is a delooping
of the entire tower below it. Spectra are where the *quantum*, or
stable, aspect of physics takes place: cocycles valued in spectra
are generalized cohomology classes.

```agda
record Prespectrum ℓ : Type (lsuc ℓ) where
  no-eta-equality
  field
    space : Nat → Type∙ ℓ
    σ∙    : ∀ n → space n →∙ Ω¹ (space (suc n))

is-Ω-spectrum : ∀ {ℓ} → Prespectrum ℓ → Type ℓ
is-Ω-spectrum E = ∀ n → is-equiv (E .Prespectrum.σ∙ n .fst)

is-Ω-spectrum-is-prop
  : ∀ {ℓ} (E : Prespectrum ℓ) → is-prop (is-Ω-spectrum E)
is-Ω-spectrum-is-prop E = hlevel 1
```

The [[suspension–loop space adjunction|loop space]] provides the maps
in the other direction, $\Sigma E_n \to E_{n+1}$, and the delooping
of an abelian group begins such a tower at height one; continuing it
to all heights — the Eilenberg–MacLane spectrum — requires the higher
deloopings $K(A, n)$, which the 1Lab does not yet have. The site
$\rm{Lin}$ of negative-dimensional spheres, presenting *parameterized*
spectra as a gros higher topos, is likewise future work.

## Parameterized spectra

A **parameterized spectrum** over a base $B$ is a family of spectra,
one for each point. In the language of homotopy type theory this is
simply a function into the type of (pre)spectra — the families that
the paper presents as presheaves on the site $\rm{Lin}$ of
negative-dimensional spheres. The site presentation, together with
its stable localisation making these a higher *tangent topos*, is
future work; the objects themselves are already available.

```agda
Prespectrum-over : ∀ {ℓb} (B : Type ℓb) (ℓ : Level) → Type (ℓb ⊔ lsuc ℓ)
Prespectrum-over B ℓ = B → Prespectrum ℓ

is-Ω-spectrum-over
  : ∀ {ℓb ℓ} {B : Type ℓb} → Prespectrum-over B ℓ → Type (ℓb ⊔ ℓ)
is-Ω-spectrum-over E = ∀ b → is-Ω-spectrum (E b)
```
