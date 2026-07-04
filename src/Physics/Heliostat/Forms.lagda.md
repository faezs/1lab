<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative

open import Data.Fin using (Fin ; fzero ; fsuc)

import Algebra.Ring.Kahler.Exterior
import Algebra.Ring.Kahler
import Algebra.Ring.Polynomial
```
-->

```agda
module Physics.Heliostat.Forms where
```

# The sag potential as a Kähler 1-form {defines="sag-field-strength sag-gauge-invariance"}

The [[heliostat|higher-topos-theory-in-physics]]'s real reflector is a
paraboloid concentrator, and the [[optics module|kahler-differentials]]
reads its surface as the graph $z = q(x^2 + y^2)$ of the **sag**: the
depth by which the dish falls away from its rim, the depth-of-cut a
machinist grinds. The optics module extracts the surface *normal* from
that graph as a genuine [[Kock–Lawvere|kock-lawvere]] derivative, and
finds its tangential part to be $-2q(x, y)$ — the slope of the dish. Here
we tell the same story in the *differential* column, in the language
[[Maxwell|maxwell-field-strength]] uses for the vector potential: the sag
is a scalar potential, its gradient is a [[Kähler differential|kahler-differentials]]
$1$-form $A_{\mathrm{sag}} = \mathrm{d}(\mathrm{sag})$ — the "optical
field strength" of the sag — and the honest degree-two fact about it is
that this field is *conservative*: its exterior derivative vanishes,
because a paraboloid is a gradient graph and a gradient has no curl. This
is $\mathrm{d}\circ\mathrm{d} = 0$, the exact same identity that made
Maxwell's $F = \mathrm{d}A$ gauge invariant, read one potential down.

```agda
module sag-forms {ℓ} (R : CRing ℓ) (Q : ⌞ R ⌟) where
  open Algebra.Ring.Polynomial R
  open Algebra.Ring.Kahler R
  open Algebra.Ring.Kahler.Exterior R
```

<!--
```agda
  private
    Plane : CRing ℓ
    Plane = R[ Lift ℓ (Fin 2) ]

    module R' = CRing-on (R .snd)
    module Rp = CRing-on (Plane .snd)
```
-->

As in Maxwell, the aperture plane has two coordinate functions $x, y$,
the free generators of the polynomial ring on two variables; the scalar
$Q$ is the paraboloid's curvature (one over four times the focal length),
supplied as a constant of the base ring and injected into the plane's
function ring as `con Q`{.Agda}.

```agda
  x̂ ŷ : ⌞ Plane ⌟
  x̂ = var (lift fzero)
  ŷ = var (lift (fsuc fzero))
```

## The sag potential

The sag is the rotationally symmetric quadratic $\mathrm{sag} = Q\,(x^2 +
y^2)$: the paraboloid's height above the aperture plane, a polynomial in
the two coordinates. It is a *scalar* — an element of the plane's function
ring — playing exactly the role of an electrostatic potential $V$, of
which the field will be the gradient.

```agda
  sag : ⌞ Plane ⌟
  sag = con Q *ₚ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))
```

## The optical field strength (the sag 1-form)

The gradient of the sag is its Kähler differential, the $1$-form
$A_{\mathrm{sag}} = \mathrm{d}(\mathrm{sag})$. Where Maxwell wrote his
potential as a bare $x\,\mathrm{d}y$, ours is the differential of a genuine
potential function — the "field strength of the sag" in the sense that it
records how the surface height varies across the aperture.

```agda
  A-sag : Ω¹ Plane con-hom
  A-sag = dₖ sag
```

## The slope-form identity

Computing that gradient in coordinates is the differential-forms shadow of
the optics module's normal computation. The Leibniz rule
`d-leibniz`{.Agda} pulls the curvature `con Q`{.Agda} out — its own
differential dying by `d-const`{.Agda}, since a constant of the base ring
has vanishing gradient — and expands $\mathrm{d}(x^2)$ into $2x\,\mathrm{d}x$
exactly as the physicist writes $\mathrm{d}V = 2x\,\mathrm{d}x$: two copies
of $x\,\mathrm{d}x$ from the two factors of $x \cdot x$, recollected by
`·ω-distr`{.Agda} into $(x + x)\,\mathrm{d}x$. The result is the slope
$1$-form whose $x$- and $y$-components are $2Q x$ and $2Q y$ — precisely
the $-2q(x, y)$ tangential part of the surface normal, up to the sign
convention distinguishing outward normal from upward sag.

```agda
  slope-form
    : A-sag
    ≡ ((con Q *ₚ (x̂ +ₚ x̂)) ·ω dₖ x̂) +ω ((con Q *ₚ (ŷ +ₚ ŷ)) ·ω dₖ ŷ)
  slope-form =
    A-sag
      ≡⟨⟩
    dₖ (con Q *ₚ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ)))
      ≡⟨ d-leibniz (con Q) ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ)) ⟩
    (con Q ·ω dₖ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ)))
      +ω (((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ)) ·ω dₖ (con Q))
      ≡⟨ ap ((con Q ·ω dₖ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))) +ω_)
           (ap (((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ)) ·ω_) (d-const Q)
            ∙ ·ω-absorb ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))) ⟩
    (con Q ·ω dₖ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))) +ω 0ω
      ≡⟨ +ω-idr (con Q ·ω dₖ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))) ⟩
    con Q ·ω dₖ ((x̂ *ₚ x̂) +ₚ (ŷ *ₚ ŷ))
      ≡⟨ ap (con Q ·ω_) (d-+ (x̂ *ₚ x̂) (ŷ *ₚ ŷ)) ⟩
    con Q ·ω (dₖ (x̂ *ₚ x̂) +ω dₖ (ŷ *ₚ ŷ))
      ≡⟨ ap (con Q ·ω_) (ap₂ _+ω_ (d-leibniz x̂ x̂) (d-leibniz ŷ ŷ)) ⟩
    con Q ·ω (((x̂ ·ω dₖ x̂) +ω (x̂ ·ω dₖ x̂)) +ω ((ŷ ·ω dₖ ŷ) +ω (ŷ ·ω dₖ ŷ)))
      ≡⟨ ap (con Q ·ω_) (ap₂ _+ω_ (sym (·ω-distr x̂ x̂ (dₖ x̂))) (sym (·ω-distr ŷ ŷ (dₖ ŷ)))) ⟩
    con Q ·ω (((x̂ +ₚ x̂) ·ω dₖ x̂) +ω ((ŷ +ₚ ŷ) ·ω dₖ ŷ))
      ≡⟨ ·ω-distl (con Q) ((x̂ +ₚ x̂) ·ω dₖ x̂) ((ŷ +ₚ ŷ) ·ω dₖ ŷ) ⟩
    (con Q ·ω ((x̂ +ₚ x̂) ·ω dₖ x̂)) +ω (con Q ·ω ((ŷ +ₚ ŷ) ·ω dₖ ŷ))
      ≡⟨ ap₂ _+ω_ (·ω-assoc (con Q) (x̂ +ₚ x̂) (dₖ x̂))
                  (·ω-assoc (con Q) (ŷ +ₚ ŷ) (dₖ ŷ)) ⟩
    ((con Q *ₚ (x̂ +ₚ x̂)) ·ω dₖ x̂) +ω ((con Q *ₚ (ŷ +ₚ ŷ)) ·ω dₖ ŷ)
      ∎
```

Reading off the components: the coefficient of $\mathrm{d}x$ is $Q(x + x)
= 2Qx$ and of $\mathrm{d}y$ is $2Qy$, so the slope $1$-form is
$2Q(x\,\mathrm{d}x + y\,\mathrm{d}y)$. This is the exterior-algebra
witness of the optics module's `normal-value`{.Agda}: the mirror normal's
tangential slope is $-2q(x, y)$, and $\mathrm{d}(\mathrm{sag})$ carries
exactly those two numbers as the coefficients of $\mathrm{d}x$ and
$\mathrm{d}y$ — the gradient of the sag *is* the slope, derived rather
than posited.

## The field strength vanishes: the sag is conservative

The field strength is the exterior derivative of the potential,
$F_{\mathrm{sag}} = \mathrm{d}A_{\mathrm{sag}}$ — the same
$F = \mathrm{d}A$ recipe as Maxwell, one potential down. But here the
potential is *itself* exact, $A_{\mathrm{sag}} = \mathrm{d}(\mathrm{sag})$,
so its field strength is $\mathrm{d}\circ\mathrm{d}(\mathrm{sag})$, which
is zero by `d¹-d`{.Agda}. This is the honest degree-two content: a
paraboloid is a gradient graph, and a gradient has no curl — the sag field
is *conservative*, and the vanishing is a genuine $2$-form identity, not a
fabricated nonzero curvature.

```agda
  F-sag : Ω² Plane con-hom
  F-sag = d¹ A-sag

  sag-closed : F-sag ≡ 0²
  sag-closed = d¹-d sag
```

Contrast with Maxwell, where $A = x\,\mathrm{d}y$ is *not* exact and
$F = \mathrm{d}x \wedge \mathrm{d}y$ is a genuine constant magnetic field.
The sag potential is exact by construction — it is the differential of a
scalar — so its two-form is forced to vanish. The physics is that a static
optical surface stores no curl: there is a well-defined height at every
point of the aperture, and the slope field is its honest gradient.

## Gauge invariance

Even though the field strength is already zero, the same gauge freedom
Maxwell exploited holds here: adding the differential of any function
$\chi$ to the potential changes $A_{\mathrm{sag}}$ but leaves
$F_{\mathrm{sag}}$ untouched. Physically, re-zeroing the sag by an
additive reference surface $\chi$ — measuring depth from a shifted datum
plane — cannot change the (vanishing) curl. This is the abstract
`gauge`{.Agda} lemma, instantiated at the sag potential.

```agda
  same-optics : ∀ χ → d¹ (A-sag +ω dₖ χ) ≡ d¹ A-sag
  same-optics χ = gauge A-sag χ
```

Two sag potentials differing by such a $\chi$ describe the same optics:
the field strength — here the statement that the surface is conservative —
is identical, proved by the exterior-derivative's gauge invariance rather
than checked component by component.

## What is and is not proven

Everything above typechecks with **zero postulates**, over an *arbitrary*
commutative ring $R$ and an arbitrary curvature constant $Q : R$. Proven:
the sag potential `sag`{.Agda} as a scalar in the plane's polynomial ring;
its gradient `A-sag`{.Agda} as a Kähler $1$-form; the `slope-form`{.Agda}
identity that unfolds that gradient into $Q(x+x)\,\mathrm{d}x + Q(y+y)\,\mathrm{d}y$
— the $2Qx, 2Qy$ components matching the optics module's tangential normal
$-2q(x, y)$ — using only `d-leibniz`{.Agda}, `d-const`{.Agda}, `d-+`{.Agda},
`·ω-distr`{.Agda}, `·ω-distl`{.Agda} and `·ω-assoc`{.Agda}; the field
strength `F-sag`{.Agda}; that it vanishes, `sag-closed`{.Agda}, via
`d¹-d`{.Agda} (the conservative/exact fact, *not* a fake nonzero curvature);
and gauge invariance `same-optics`{.Agda} via the abstract `gauge`{.Agda}
lemma.

Not proven here, and *not claimed*: this is a degree-one and degree-two
statement only — the same $\Omega^{\ge 3}$, Bianchi identity, and de Rham
tower that `Physics.Maxwell`{.Agda} leaves to future work are absent here
too. The identification of the slope-form coefficients with the optics
normal is stated in prose, tying `slope-form`{.Agda} to
`Physics.Heliostat.Optics`{.Agda}'s `normal-value`{.Agda}, but is *not*
formalised as a cross-module equation: the two modules compute in different
representations (Kähler forms here, Kock–Lawvere derivatives there) and no
bridge lemma between them is proven. Nor is the sag's *focusing* property
touched — that lives in the optics module as an exact ring identity; here
we prove only that the sag field is conservative, which is the strongest
honest thing a $2$-form built from an exact $1$-form can say.
