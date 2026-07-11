<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Algebra.Ring.Commutative
open import Algebra.Ring using (is-ring-hom)

open import Cat.Instances.Presheaf.Concrete
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Fin using (Fin ; fzero ; fin-view ; Fin-view ; Fin-absurd)

import Algebra.Ring.DualNumbers as Dual
import Algebra.Ring.Polynomial
import Algebra.Ring.Kahler.Exterior
import Algebra.Ring.Kahler
import Cat.Reasoning

open is-ring-hom
open Precategory
open Functor
```
-->

```agda
module Cat.Instances.FormalSmoothSets.DeRham {ℓ} (R : CRing ℓ) where
```

<!--
```agda
open import Cat.Instances.FormalSmoothSets R

open Algebra.Ring.Polynomial R
open Algebra.Ring.Kahler R

private
  module CR = Cat.Reasoning (CRings ℓ)
```
-->

# The de Rham classifier is not concrete {defines="de-rham-classifier"}

The paper's key example of a smooth set that is *not* determined by
its points is the classifier of differential 1-forms: it has a single
point, and yet its plots by $\bA^n$ are all the 1-forms on $\bA^n$.
Constructively, the 1-forms on a probe are the [[Kähler
differentials|kahler-differentials]] of its function algebra, and
functoriality is pushforward along algebra maps.

```agda
Ω¹-dR : ⌞ FrmlSmthSet ⌟
Ω¹-dR .F₀ U = el (Ω¹ (O U) (struct U)) squashω
Ω¹-dR .F₁ h = Ω¹-map (h .ThHom.fun) (h .ThHom.commutes)
Ω¹-dR .F-id {U} = funext (Ω¹-map-id _)
Ω¹-dR .F-∘ f g = funext
  (Ω¹-map-∘ (f .ThHom.fun) (g .ThHom.fun)
    (f .ThHom.commutes) (g .ThHom.commutes) _)
```

**One point.** Over the terminal probe, every polynomial is a
constant, so every differential vanishes: the classifier has a
contractible set of points.

```agda
private
  d-zero
    : (p : ⌞ O∙ 0 0 ⌟)
    → Path (Ω¹ (O∙ 0 0) (structO 0 0)) (dₖ p) 0ω
  d-zero = Poly-elim-prop _ (λ _ → squashω _ _)
    (λ v → absurd (Fin-absurd (v .Lift.lower)))
    (λ a → d-const a)
    (λ x ihx y ihy → d-+ x y ∙ ap₂ _+ω_ ihx ihy ∙ +ω-idl 0ω)
    (λ x ihx y ihy →
        d-leibniz x y
      ∙ ap₂ _+ω_ (ap (x ·ω_) ihy ∙ ·ω-absorb x)
                 (ap (y ·ω_) ihx ∙ ·ω-absorb y)
      ∙ +ω-idl 0ω)
    (λ x ih →
        sym (+ω-idl (dₖ (negₚ x)))
      ∙ ap (_+ω dₖ (negₚ x)) (sym ih)
      ∙ sym (d-+ x (negₚ x))
      ∙ ap dₖ (+ₚ-invr x)
      ∙ d-const R.0r)
    where module R = CRing-on (R .snd)

Ω¹-dR-point : is-contr ∣ Ω¹-dR .F₀ (𝔸 0 0) ∣
Ω¹-dR-point .centre = 0ω
Ω¹-dR-point .paths = Ω¹-elim-prop (O∙ 0 0) (structO 0 0)
  (λ x → 0ω ≡ x) (λ _ → squashω _ _)
  (λ p → sym (d-zero p))
  (λ a x ih → sym (·ω-absorb a) ∙ ap (a ·ω_) ih)
  (λ x ihx y ihy → sym (+ω-idl 0ω) ∙ ap₂ _+ω_ ihx ihy)
  refl
  (λ x ih →
      sym (+ω-invr 0ω)
    ∙ +ω-idl (-ω 0ω)
    ∙ ap -ω_ ih)
```

**Many plots.** On the line, the differential of the coordinate is
not zero — provided $R$ itself is nontrivial. The witness is the
*derivative*: evaluation into the [[dual numbers|dual-numbers]] over
$R[x]$ at $x \mapsto x + \epsilon$ reads off first-order Taylor
coefficients, and gives a linear functional on differentials sending
$\mathrm{d}x$ to $1$.

<!--
```agda
private
  R[x] : CRing ℓ
  R[x] = R[ Lift ℓ (Fin 1) ]

  module Rx = CRing-on (R[x] .snd)
  module R' = CRing-on (R .snd)

  xᵖ : ⌞ R[x] ⌟
  xᵖ = var (lift fzero)

  E : CR.Hom R[x] (Dual.R[ε] R[x])
  E = extend (Dual.ι-dual R[x] CR.∘ con-hom) (λ _ → xᵖ , con R'.1r)

  δ : ⌞ R[x] ⌟ → ⌞ R[x] ⌟
  δ p = (E .∫Hom.fst p) .snd

  fin1 : (w : Fin 1) → w ≡ fzero
  fin1 w with fin-view w
  ... | Fin-view.zero = refl
  ... | Fin-view.suc i = absurd (Fin-absurd i)

  E-fst : ∀ p → (E .∫Hom.fst p) .fst ≡ p
  E-fst p = happly (ap (λ e → e .∫Hom.fst) q) p where
    q : Dual.aug-dual R[x] CR.∘ E ≡ CR.id
    q = extend-unique con-hom (λ v → var v)
          (Dual.aug-dual R[x] CR.∘ E)
          (λ a → refl)
          (λ v → ap (λ z → var (lift z)) (sym (fin1 (v .Lift.lower))))
      ∙ sym (extend-unique con-hom (λ v → var v) CR.id
          (λ a → refl) (λ v → refl))
```
-->

```agda
  ev-d : Ω¹ R[x] con-hom → ⌞ R[x] ⌟
  ev-d (dₖ p) = δ p
  ev-d (a ·ω x) = a Rx.* ev-d x
  ev-d (x +ω y) = ev-d x Rx.+ ev-d y
  ev-d 0ω = Rx.0r
  ev-d (-ω x) = Rx.- ev-d x

  ev-d (+ω-idl x i) = Rx.+-idl {ev-d x} i
  ev-d (+ω-invr x i) = Rx.+-invr {ev-d x} i
  ev-d (+ω-assoc x y z i) =
    Rx.+-associative {ev-d x} {ev-d y} {ev-d z} i
  ev-d (+ω-comm x y i) = Rx.+-commutes {ev-d x} {ev-d y} i
  ev-d (·ω-distl a x y i) = Rx.*-distribl {a} {ev-d x} {ev-d y} i
  ev-d (·ω-distr a b x i) = Rx.*-distribr {ev-d x} {a} {b} i
  ev-d (·ω-assoc a b x i) = Rx.*-associative {a} {b} {ev-d x} i
  ev-d (·ω-idl x i) = Rx.*-idl {ev-d x} i
  ev-d (d-+ a b i) = δ (a +ₚ b)
  ev-d (d-leibniz a b i) =
    ( ap₂ Rx._+_
        (ap (Rx._* δ b) (E-fst a))
        (ap (δ a Rx.*_) (E-fst b) ∙ Rx.*-commutes {δ a} {b})) i
  ev-d (d-const r i) = Rx.0r
  ev-d (squashω x y p q i j) = Rx.has-is-set
    (ev-d x) (ev-d y) (λ i → ev-d (p i)) (λ i → ev-d (q i)) i j
```

If $\mathrm{d}x = 0$ then $1 = 0$ in $R[x]$, hence in $R$ after
evaluating the variable anywhere; so over a nontrivial ring the
classifier of 1-forms has a plot that the underlying point-set cannot
see, and is not concrete: the diffeological spaces sit *strictly*
inside the formal smooth sets.

```agda
Ω¹-dR-not-concrete
  : ¬ (CRing-on.1r (R .snd) ≡ CRing-on.0r (R .snd))
  → ¬ is-concrete ThCartSp pt-terminal Ω¹-dR
Ω¹-dR-not-concrete nontriv conc = nontriv 1≡0 where
  dx≡0 : Path (Ω¹ R[x] con-hom) (dₖ xᵖ) 0ω
  dx≡0 = conc (𝔸 1 0) $ funext λ p →
    is-contr→is-prop Ω¹-dR-point _ _

  1x≡0x : con R'.1r ≡ con R'.0r
  1x≡0x = ap ev-d dx≡0

  1≡0 : R'.1r ≡ R'.0r
  1≡0 = ap (λ p → extendᵖ CR.id (λ _ → R'.0r) p) 1x≡0x
```

## The differential as a map of smooth sets

The classifier story continues one degree up: the [[second exterior
power|kahler-2-forms]] also assembles into a smooth set, and the
exterior derivative — being natural in the probe — becomes an
honest *morphism of smooth sets* $\mathrm{d} : \Omega^1 \to
\Omega^2$. This is the map that sends a gauge potential to its
field strength, at the level of classifying objects.

<!--
```agda
open Algebra.Ring.Kahler.Exterior R
```
-->

```agda
Ω²-dR : ⌞ FrmlSmthSet ⌟
Ω²-dR .F₀ U = el (Ω² (O U) (struct U)) squash²
Ω²-dR .F₁ h = Ω²-map (h .ThHom.fun) (h .ThHom.commutes)
Ω²-dR .F-id {U} = funext (Ω²-map-id _)
Ω²-dR .F-∘ f g = funext
  (Ω²-map-∘ (f .ThHom.fun) (g .ThHom.fun)
    (f .ThHom.commutes) (g .ThHom.commutes) _)

d-dR : FrmlSmthSet .Precategory.Hom Ω¹-dR Ω²-dR
d-dR ._=>_.η U = d¹
d-dR ._=>_.is-natural U V h = funext λ ω →
  sym (d¹-natural (h .ThHom.fun) (h .ThHom.commutes) ω)
```
