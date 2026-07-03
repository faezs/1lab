<!--
```agda
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Nat.Base
open import Data.Sum

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.NegativeSpheres where
```

# The site of negative-dimensional spheres {defines="negative-sphere lin-site"}

The last column of the paper's probe table: the probes of *stable*,
or quantum, geometry are the "negative-dimensional spheres"
$\mathbb{S}^{-d}$. What structure do these have as a *site*? Each
sphere contains the point as a retract — a basepoint inclusion and a
projection composing to the identity — and beyond the maps factoring
through the point, a sphere has only its identity. The category
$\rm{Lin}$ generated this way has, between spheres of distinct
dimensions, *only* the trivial map: negative spheres are connected
by nothing but their common basepoint.

```agda
data Sphere : Type where
  pt : Sphere
  𝕊⁻ : Nat → Sphere

Lin-hom : Sphere → Sphere → Type
Lin-hom pt     pt     = ⊤
Lin-hom pt     (𝕊⁻ e) = ⊤
Lin-hom (𝕊⁻ d) pt     = ⊤
Lin-hom (𝕊⁻ d) (𝕊⁻ e) = ⊤ ⊎ (d ≡ e)
```

In the hom-set between spheres, `inl`{.Agda} is the map through the
basepoint and `inr`{.Agda} is the identity, tagged with the proof
that the dimensions agree. Composition annihilates everything except
matched identities.

```agda
Lin : Precategory lzero lzero
Lin .Ob = Sphere
Lin .Hom = Lin-hom
Lin .Hom-set pt     pt     _ _ = hlevel 1
Lin .Hom-set pt     (𝕊⁻ e) _ _ = hlevel 1
Lin .Hom-set (𝕊⁻ d) pt     _ _ = hlevel 1
Lin .Hom-set (𝕊⁻ d) (𝕊⁻ e) = hlevel 2
Lin .id {pt}   = tt
Lin .id {𝕊⁻ d} = inr refl
Lin ._∘_ {x} {y} {z} = cmp x y z where
  cmp : ∀ x y z → Lin-hom y z → Lin-hom x y → Lin-hom x z
  cmp pt     y pt     f g = tt
  cmp (𝕊⁻ d) y pt     f g = tt
  cmp pt     y (𝕊⁻ e) f g = tt
  cmp (𝕊⁻ d) pt     (𝕊⁻ e) f       g       = inl tt
  cmp (𝕊⁻ d) (𝕊⁻ w) (𝕊⁻ e) (inl _) g       = inl tt
  cmp (𝕊⁻ d) (𝕊⁻ w) (𝕊⁻ e) (inr p) (inl _) = inl tt
  cmp (𝕊⁻ d) (𝕊⁻ w) (𝕊⁻ e) (inr p) (inr q) = inr (q ∙ p)
Lin .idr {pt}   {pt}   f       = refl
Lin .idr {pt}   {𝕊⁻ e} f       = refl
Lin .idr {𝕊⁻ d} {pt}   f       = refl
Lin .idr {𝕊⁻ d} {𝕊⁻ e} (inl _) = refl
Lin .idr {𝕊⁻ d} {𝕊⁻ e} (inr p) = ap inr (∙-idl p)
Lin .idl {pt}   {pt}   f       = refl
Lin .idl {pt}   {𝕊⁻ e} f       = refl
Lin .idl {𝕊⁻ d} {pt}   f       = refl
Lin .idl {𝕊⁻ d} {𝕊⁻ e} (inl _) = refl
Lin .idl {𝕊⁻ d} {𝕊⁻ e} (inr p) = ap inr (∙-idr p)
Lin .assoc {pt}   {y}    {z}     {pt}   f g h = refl
Lin .assoc {𝕊⁻ a} {y}    {z}     {pt}   f g h = refl
Lin .assoc {pt}   {pt}   {pt}    {𝕊⁻ e} f g h = refl
Lin .assoc {pt}   {pt}   {𝕊⁻ w}  {𝕊⁻ e} f g h = refl
Lin .assoc {pt}   {𝕊⁻ x} {pt}    {𝕊⁻ e} f g h = refl
Lin .assoc {pt}   {𝕊⁻ x} {𝕊⁻ w}  {𝕊⁻ e} f g h = refl
Lin .assoc {𝕊⁻ a} {pt}   {pt}    {𝕊⁻ e} f g h = refl
Lin .assoc {𝕊⁻ a} {pt}   {𝕊⁻ w}  {𝕊⁻ e} (inl _) g h = refl
Lin .assoc {𝕊⁻ a} {pt}   {𝕊⁻ w}  {𝕊⁻ e} (inr p) g h = refl
Lin .assoc {𝕊⁻ a} {𝕊⁻ x} {pt}    {𝕊⁻ e} f g h = refl
Lin .assoc {𝕊⁻ a} {𝕊⁻ x} {𝕊⁻ w}  {𝕊⁻ e} (inl _) g h = refl
Lin .assoc {𝕊⁻ a} {𝕊⁻ x} {𝕊⁻ w}  {𝕊⁻ e} (inr p) (inl _) h = refl
Lin .assoc {𝕊⁻ a} {𝕊⁻ x} {𝕊⁻ w}  {𝕊⁻ e} (inr p) (inr q) (inl _) = refl
Lin .assoc {𝕊⁻ a} {𝕊⁻ x} {𝕊⁻ w}  {𝕊⁻ e} (inr p) (inr q) (inr r) =
  ap inr (sym (∙-assoc r q p))
```

A presheaf on $\rm{Lin}$ is a family of sets, one for each negative
sphere, each of them *pointed over* the common value at the point:
restricting along the basepoint inclusion projects down, restricting
along the retraction is a section of it. These are the
parameterized-pointed-object precursors of the paper's
[[parameterized spectra|spectrum]].

```agda
LinSpc : Precategory (lsuc lzero) lzero
LinSpc = PSh lzero Lin

module _ (X : Functor (Lin ^op) (Sets lzero)) where
  private module X = Functor X

  to-base : ∀ d → ⌞ X.₀ (𝕊⁻ d) ⌟ → ⌞ X.₀ pt ⌟
  to-base d = X.₁ {𝕊⁻ d} {pt} tt

  of-base : ∀ d → ⌞ X.₀ pt ⌟ → ⌞ X.₀ (𝕊⁻ d) ⌟
  of-base d = X.₁ {pt} {𝕊⁻ d} tt

  base-section : ∀ d x → to-base d (of-base d x) ≡ x
  base-section d x =
    sym (happly (X.F-∘ {pt} {𝕊⁻ d} {pt} tt tt) x) ∙ happly X.F-id x
```

The paper's tangent higher topos of parameterized spectra arises
from these presheaves by *stable* localisation — inverting the maps
that induce equivalences of spectra, so that each fibre becomes an
$\Omega$-spectrum rather than a bare tower — which, along with the
smash monoidal structure making quantization a linear functor,
remains future work.
