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
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Displayed.Total

open import Algebra.ChainComplex.DoldKan.Functorial
open import Algebra.ChainComplex.DoldKan.Fundamental
open import Algebra.ChainComplex.DoldKan.Boundary
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Set.Coequaliser
open import Data.Fin

import Cat.Instances.FormalSmoothSets
import Algebra.Ring.Kahler.Exterior
import Algebra.Ring.Kahler
import Algebra.ChainComplex.Moore

open Chain-complex
open Chain-map
open Functor
```
-->

```agda
module Cat.Instances.FormalSmoothSets.GaugeGroupoid (R : CRing lzero) where
```

<!--
```agda
open Cat.Instances.FormalSmoothSets R
open Algebra.Ring.Kahler.Exterior R
open Algebra.Ring.Kahler R
open import Cat.Instances.FormalSmoothSets.Deligne R

private
  module MC = Algebra.ChainComplex.Moore
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

## The B-field

The same composite applied to the [[degree-$3$ Deligne
complex|deligne-complex]] produces the smooth $2$-groupoid
$\mathbf{B}^2 U(1)_\mathrm{conn}$ of $B$-fields — the higher gauge
fields sourced by strings: a $2$-form potential, gauge
transformations by $1$-forms, gauge-of-gauge transformations by
functions, and the integral ambiguity at the bottom.

```agda
B²U1-conn : Functor (ThCartSp ^op) Cat[ Δ ^op , Ab lzero ]
B²U1-conn = Γ-functor F∘ Deligne³

B²U1-conn-sset : Functor (ThCartSp ^op) Cat[ Δ ^op , Sets lzero ]
B²U1-conn-sset = postcompose Ab↪Sets F∘ B²U1-conn

B²U1-conn-kan : (U : ThAff) → is-kan (B²U1-conn-sset .F₀ U)
B²U1-conn-kan U = sab-is-kan (B²U1-conn .F₀ U)
```

## The field strength

The physical content of the presentation is that the **curvature**
$F = \mathrm{d}A$ of a gauge field descends to gauge equivalence
classes: two gauge-equivalent connections have the same field
strength. In simplicial terms, $\pi_0$ of the gauge groupoid is the
group of connections modulo gauge transformations, and the exterior
derivative — evaluated at the fundamental vertex — respects the
identification, because an edge witnesses that its endpoints differ
by an exact form, which [[gauge invariance|kahler-2-forms]] kills.
The bridge between the simplicial and the differential worlds is
the boundary formula for the fundamental $1$-class: its two vertex
evaluations differ by exactly the derivative the chain square
provides.

```agda
module _ (U : ThAff) where
  private
    C : Chain-complex lzero
    C = Del²-at U

    module ΓC = Functor (Γ C)
    module N1 = Abelian-group-on (NΔ 1 .ob 0 .snd)
    module W = Abelian-group-on (Ω¹-ab U .snd)

    instance
      H-Level-Ω² : ∀ {n} → H-Level (Ω² (O U) (struct U)) (2 + n)
      H-Level-Ω² = basic-instance 2 squash²

    ev : ⌞ Γ C .F₀ 0 ⌟ → ⌞ Ω¹-ab U ⌟
    ev φ = φ .map 0 .∫Hom.fst (fundamental 0)

    vtx : (j : Fin 2) → ⌞ NΔ 1 .ob 0 ⌟
    vtx j = NΔ-map (δ j) .map 0 .∫Hom.fst (fundamental 0)

    ∂e₁ : ⌞ NΔ 1 .ob 0 ⌟
    ∂e₁ = MC.Moore ℤ⟨ Δ[ 1 ] ⟩ .∂ᶜ 0 .∫Hom.fst (fundamental 1)

    split-∂
      : ∂e₁
      ≡ N1._*_ (vtx fzero)
          (N1._⁻¹ (N1._*_ (vtx (fsuc fzero)) (N1._⁻¹ N1.1g)))
    split-∂ = Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ 1 ] ⟩ 0)
      (∂-fundamental 0)

  curvature
    : Ab lzero .Precategory.Hom (π₀-ab (Γ C)) (Ω²-ab U)
  curvature .∫Hom.fst = Coeq-rec ci r where
    ci : ⌞ Γ C .F₀ 0 ⌟ → ⌞ Ω²-ab U ⌟
    ci φ = d¹ (ev φ)

    r : (h : ⌞ Γ C .F₀ 1 ⌟)
      → ci (ΓC.₁ (δ fzero) .∫Hom.fst h)
      ≡ ci (ΓC.₁ (δ (fsuc fzero)) .∫Hom.fst h)
    r h = ap d¹ step2 ∙ ap d¹ (+ω-comm (dₖ g) w₁) ∙ gauge w₁ g
      where
      h₀ : ⌞ NΔ 1 .ob 0 ⌟ → ⌞ Ω¹-ab U ⌟
      h₀ = h .map 0 .∫Hom.fst

      hom₀ = h .map 0 .∫Hom.snd

      g : ⌞ O-ab U ⌟
      g = h .map 1 .∫Hom.fst (fundamental 1)

      w₀ w₁ : ⌞ Ω¹-ab U ⌟
      w₀ = h₀ (vtx fzero)
      w₁ = h₀ (vtx (fsuc fzero))

      inv1g : W._⁻¹ W.1g ≡ W.1g
      inv1g = sym W.idl ∙ W.inverser

      step1 : dₖ g ≡ W._*_ w₀ (W._⁻¹ w₁)
      step1 =
          sym (h .comm 0 (fundamental 1))
        ∙ ap h₀ split-∂
        ∙ is-group-hom.pres-⋆ hom₀ (vtx fzero) _
        ∙ ap (W._*_ w₀)
            ( is-group-hom.pres-inv hom₀
            ∙ ap W._⁻¹
                ( is-group-hom.pres-⋆ hom₀ (vtx (fsuc fzero))
                    (N1._⁻¹ N1.1g)
                ∙ ap (W._*_ w₁)
                    ( is-group-hom.pres-inv hom₀
                    ∙ ap W._⁻¹ (is-group-hom.pres-id hom₀)
                    ∙ inv1g)
                ∙ W.idr))

      step2 : w₀ ≡ W._*_ (dₖ g) w₁
      step2 =
          sym W.idr
        ∙ ap (W._*_ w₀) (sym W.inversel)
        ∙ W.associative
        ∙ ap (λ z → W._*_ z w₁) (sym step1)
  curvature .∫Hom.snd .is-group-hom.pres-⋆ =
    Coeq-elim-prop (λ _ → Π-is-hlevel 1 (λ _ → squash² _ _)) λ a →
    Coeq-elim-prop (λ _ → squash² _ _) λ b → refl
```
