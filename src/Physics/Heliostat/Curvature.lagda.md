<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Cat.Displayed.Total

open import Data.Fin using (Fin ; fzero)

import Algebra.Ring.Weil as Weil
import Algebra.Ring.Polynomial
import Algebra.Ring.Reasoning
import Cat.Reasoning

open is-ring-hom
```
-->

```agda
module Physics.Heliostat.Curvature where
```

# The paraboloid's curvature as a jet {defines="paraboloid-curvature focal-length"}

The [[parabolic mirror|heliostat]] focuses because of a single number:
its **curvature**, constant across the whole reflector, which *is* the
reciprocal focal length. `Physics.Heliostat.Optics`{.Agda} proves the
focusing as an exact reflection identity; here we read the same
geometry through the [[jet derivative|jet-derivative]] instead, and
watch the focal length fall out as the second-order coefficient of a
[[Weil 2-jet|second-order-weil-algebra]] — exactly the way
`Physics.Newton`{.Agda} reads the stiffness of a spring off the
$\delta^2$-term of its potential.

Along one axis the mirror's height is the paraboloid $h(x) = q\,x^2$.
The coefficient $q$ is all there is to a parabola: its second
derivative is the constant $2q$, and a classical parabola $y = x^2/(4f)$
with focal length $f$ has exactly $q = 1/(4f)$, so the *undivided*
second derivative $2q = 1/(2f)$ is the reciprocal focal length up to
the same factor of two that the jet derivative always keeps explicit.
We compute the whole jet of $h$ at the thickened point $\hat x + \delta$
and read curvature off the top.

Building the 2-jet is done exactly as in the [[second-order Taylor
expansion|newtons-second-law]] of `Physics.Newton`{.Agda}: the
observable ring is the one-variable polynomial ring $R[x]$, the Weil
algebra $W_2$ is built *over* it, and `taylor₂`{.Agda} is the algebra
map sending the variable to the thickened point.

```agda
module _ {ℓ} (R : CRing ℓ) where
  open Algebra.Ring.Polynomial R
```

<!--
```agda
  private
    Obs : CRing ℓ
    Obs = R[ Lift ℓ (Fin 1) ]

    module R' = CRing-on (R .snd)
    module Ro = CRing-on (Obs .snd)
    module CR = Cat.Reasoning (CRings ℓ)

  module WObs = Weil Obs
  private module W = CRing-on (WObs.W₂ .snd)
```
-->

```agda
  x̂ : ⌞ Obs ⌟
  x̂ = var (lift fzero)

  taylor₂ : CR.Hom Obs (WObs.W₂)
  taylor₂ = extend (WObs.ι CR.∘ con-hom) (λ _ → x̂ , con R'.1r , con R'.0r)
```

## The height of the mirror

Fix the parabola's curvature coefficient $q$. As a polynomial
observable the height is $h = q\cdot x^2$ — the constant `con Q`{.Agda}
times the square `x̂ *ₚ x̂`{.Agda}, both living in $R[x]$. Writing it as
`con Q`{.Agda} *times a square* is not incidental: it is precisely the
shape that keeps us clear of the [[divided-power hazard|jet-derivative]]
of the jet derivative, as we note at the end.

```agda
  module curvature (Q : ⌞ R ⌟) where
    h : ⌞ Obs ⌟
    h = con Q *ₚ (x̂ *ₚ x̂)
```

The square `x̂ *ₚ x̂`{.Agda} is exactly the potential $V$ whose 2-jet
`Physics.Newton`{.Agda} computes: value $x^2$, velocity $\hat x +ₚ \hat
x = 2x$, and undivided curvature `con R'.1r`{.Agda}. We reproduce that
`V-jet`{.Agda} computation here rather than importing it, so that this
module stands on its own polynomial identities.

<!--
```agda
    private abstract
      V-jet-1
        : (x̂ *ₚ con R'.1r) Ro.+ (con R'.1r *ₚ x̂) ≡ x̂ +ₚ x̂
      V-jet-1 = ap₂ _+ₚ_ Ro.*-idr (*ₚ-idl x̂)

      V-jet-2
        : ((x̂ *ₚ con R'.0r) Ro.+ (con R'.1r *ₚ con R'.1r)) Ro.+ (con R'.0r *ₚ x̂)
        ≡ con R'.1r
      V-jet-2 =
        ap₂ Ro._+_
          (ap₂ Ro._+_ Rr.*-zeror (*ₚ-idl (con R'.1r)))
          Rr.*-zerol
        ∙ ap (Ro._+ Rr.0r) Ro.+-idl
        ∙ Ro.+-idr
        where module Rr = Algebra.Ring.Reasoning (Obs .fst , Obs .snd .CRing-on.has-ring-on)
```
-->

```agda
    V-jet : taylor₂ .∫Hom.fst (x̂ *ₚ x̂) ≡ (x̂ *ₚ x̂ , x̂ +ₚ x̂ , con R'.1r)
    V-jet = ap₂ _,_ refl (ap₂ _,_ V-jet-1 V-jet-2)
```

The jet of the *constant* `con Q`{.Agda} needs no computation at all:
`taylor₂`{.Agda} factors constants through
`WObs.ι CR.∘ con-hom`{.Agda}, so a constant becomes the jet with zero
$\delta$- and $\delta^2$-parts, `refl`{.Agda} by definitional unfolding
of `extend`{.Agda} on the `con`{.Agda} constructor.

```agda
    Q-jet : taylor₂ .∫Hom.fst (con Q) ≡ (con Q , con R'.0r , con R'.0r)
    Q-jet = refl
```

## Reading off the three components

`taylor₂`{.Agda} is a ring homomorphism, so the jet of the *product*
$h = q\cdot x^2$ is the $W_2$-product of the two jets above. The
truncated-convolution product of $W_2$ then does all the work: with
$a = (q, 0, 0)$ and $c = (x^2, 2x, 1)$, the three components
$(a_0c_0,\; a_0c_1 + a_1c_0,\; a_0c_2 + a_1c_1 + a_2c_0)$ collapse to
value $q\,x^2$, velocity $2q\,x$, and $\delta^2$-coefficient $q$,
because the two zeros in $a$ annihilate every cross term.

```agda
    h-jet
      : taylor₂ .∫Hom.fst h
      ≡ ( (con Q Ro.* (x̂ *ₚ x̂))
        , (con Q Ro.* (x̂ +ₚ x̂))
        , con Q )
    h-jet =
      taylor₂ .∫Hom.snd .pres-* (con Q) (x̂ *ₚ x̂)
      ∙ ap₂ W._*_ Q-jet V-jet
      ∙ ap₂ _,_ refl (ap₂ _,_ vel curv)
      where
```

The value-slot is definitional. The velocity-slot is
$q\cdot 2x + 0\cdot x^2$: the zero kills its cross term and the left
factor is what survives, `Ro.+-idr`{.Agda} after `Rr.*-zerol`{.Agda}.

<!--
```agda
        module Rr = Algebra.Ring.Reasoning (Obs .fst , Obs .snd .CRing-on.has-ring-on)
```
-->

```agda
        vel
          : (con Q Ro.* (x̂ +ₚ x̂)) Ro.+ (con R'.0r Ro.* (x̂ *ₚ x̂))
          ≡ con Q Ro.* (x̂ +ₚ x̂)
        vel = ap ((con Q Ro.* (x̂ +ₚ x̂)) Ro.+_) Rr.*-zerol ∙ Ro.+-idr
```

The $\delta^2$-slot is
$q\cdot 1 + 0\cdot 2x + 0\cdot x^2 = q$: multiplication by the honest
undivided second derivative `con R'.1r`{.Agda} of the square gives back
`con Q`{.Agda}, and the two zeros clear the remaining terms.

```agda
        curv
          : ((con Q Ro.* con R'.1r) Ro.+ (con R'.0r Ro.* (x̂ +ₚ x̂)))
            Ro.+ (con R'.0r Ro.* (x̂ *ₚ x̂))
          ≡ con Q
        curv =
          ap₂ Ro._+_
            (ap₂ Ro._+_ Ro.*-idr Rr.*-zerol)
            Rr.*-zerol
          ∙ ap (Ro._+ Rr.0r) Ro.+-idr
          ∙ Ro.+-idr
```

## The curvature is the reciprocal focal length {defines="curvature-is-focal"}

The raw $\delta^2$-coefficient of the height jet is `con Q`{.Agda}. The
*physical* curvature — the undivided second derivative $\partial_x^2(q
x^2) = 2q$ — is that coefficient added to itself, exactly the
$c \mathbin{+} c$ doubling that the [[jet derivative|jet-derivative]]
$D$ bakes into its $\delta$-slot and that `Physics.Newton`{.Agda}'s
`newton`{.Agda} reads through `X .snd .snd R'.+ X .snd .snd`{.Agda}. So
we read the $\delta^2$-slot of the height jet, double it, and land on
`con Q +ₚ con Q` $= 2q$: the constant focal curvature.

```agda
    curvature-is-focal
      : let j = taylor₂ .∫Hom.fst h
        in (j .snd .snd) Ro.+ (j .snd .snd) ≡ con Q +ₚ con Q
    curvature-is-focal = ap₂ Ro._+_ curv curv
      where curv = ap (λ j → j .snd .snd) h-jet
```

The number `con Q +ₚ con Q` is the same at *every* $x$ — it does not
mention `x̂`{.Agda} — which is the algebraic content of the parabola's
defining property: constant curvature. A classical parabola $y = x^2/
(4f)$ has $q = 1/(4f)$, so this constant is $2q = 1/(2f)$, the
reciprocal focal length up to the ubiquitous undivided factor of two.

## The axial focusing residual is second order {defines="focusing-residual"}

`Physics.Oscillator`{.Agda}'s `euler-energy-defect`{.Agda} and the
Euler-defect story of `Physics.Newton`{.Agda} share one shape: the
*error* of a first-order approximation is an honestly second-order
quantity that a square-zero infinitesimal annihilates. The paraboloid
has the same shape, and we can state the honest, achievable half of it.

A **spherical** mirror of the same vertex curvature agrees with the
paraboloid to second order but not beyond; the paraboloid is the shape
whose height is *exactly* quadratic, with no $\delta^3$ and higher
tail. Concretely: the height jet's velocity-slot vanishes at the vertex
$\hat x \mapsto 0$, and the *residual* of the linear (flat-mirror)
approximation to $h$ — the difference between $h$ and its own tangent
jet — has zero value- and zero $\delta$-component, i.e. it is a
purely-$\delta^2$ jet, the algebraic witness that the focusing error is
second-order and no lower.

The flat-mirror (tangent) approximation to $h$ keeps the value- and
$\delta$-slots of the height jet and zeroes the curvature.

```agda
    tangent-jet : ⌞ WObs.W₂ ⌟
    tangent-jet = (con Q Ro.* (x̂ *ₚ x̂)) , (con Q Ro.* (x̂ +ₚ x̂)) , con R'.0r

    residual : ⌞ WObs.W₂ ⌟
    residual = taylor₂ .∫Hom.fst h W.- tangent-jet
```

Subtraction in $W_2$ is componentwise, so once `h-jet`{.Agda} has
rewritten the height jet into its explicit triple, the value- and
$\delta$-slots of the residual are each a thing minus itself, killed by
`Ro.+-invr`{.Agda}.

```agda
    focusing-residual-second-order
      : residual .fst ≡ Ro.0r
      × residual .snd .fst ≡ Ro.0r
    focusing-residual-second-order =
        (ap (λ j → (j W.- tangent-jet) .fst) h-jet
          ∙ Ro.+-invr)
      , (ap (λ j → (j W.- tangent-jet) .snd .fst) h-jet
          ∙ Ro.+-invr)
```

The residual's surviving component is its $\delta^2$-slot `con Q Ro.-
con R'.0r` $= q$ — the constant curvature reappearing as the leading
error term, exactly the aberration-order coefficient. That the residual
lives *entirely* in degree two is the honest, machine-checked half of
"a parabola focuses to second order". The *quantitative* aberration
coefficient — the leading term of the focal error for a genuinely
off-axis ray, which lives at $\delta^4$ — would need the fourth-order
Weil algebra $W_4$, which the [[reading guide|higher-topos-theory-in-physics]]
lists as missing ("Weil algebras beyond second order"); we make no
claim about it.

## What is and is not proven

`h-jet`{.Agda} computes the full second-order jet of the paraboloid
$h = q\,x^2$ at the thickened point, reading value $q x^2$, velocity
$q\cdot 2x$, and raw $\delta^2$-coefficient $q$, entirely from the fact
that `taylor₂`{.Agda} is a ring homomorphism together with the
truncated product of $W_2$ and a handful of zero/identity laws — no
postulates, no `--allow-unsolved`, nothing assumed. `Q-jet`{.Agda}
holds by `refl`{.Agda}. `curvature-is-focal`{.Agda} proves the doubled
$\delta^2$-coefficient equals `con Q +ₚ con Q` $= 2q$, the *constant*
curvature that is the reciprocal focal length $1/(2f)$; the constancy
(independence of `x̂`{.Agda}) is manifest in the statement.
`focusing-residual-second-order`{.Agda} proves the honest, achievable
half of the aberration story: the residual of the flat-mirror
approximation to $h$ has vanishing value- and $\delta$-components, so
the axial focusing error is a purely second-order jet.

What is **not** proven, and is not claimed: the *quantitative* optical
aberration coefficient of an off-axis ray, which lives at fourth order
and needs the Weil algebra $W_4$ — listed as missing in the [[reading
guide|higher-topos-theory-in-physics]] ("Weil algebras beyond second
order"). We compute only through $\delta^2$. Two things also make this
computation *safe* that would not survive naively at higher order.
First, `taylor₂`{.Agda} inserts the variable as $\hat x + 1\cdot\delta$,
so the $\delta^2$-slot of the square is the *undivided* `con R'.1r`
$= 2\cdot\tfrac12$, and multiplying by `con Q`{.Agda} scales it to $q$;
the physical $2q$ is recovered only by the explicit $c \mathbin{+} c$
doubling, never by dividing — so nothing here needs $R$ to be a
$\bQ$-algebra. Second, the [[divided-power hazard|jet-derivative]] that
makes the full-triple Leibniz rule *false* at the $\delta^2$-component
does **not** bite, because $h$ is a *constant times a square*: the
constant jet `(con Q , con 0r , con 0r)`{.Agda} has zero $\delta$- and
$\delta^2$-parts, so the $\delta^1\!\cdot\!\delta^2$ cross terms that
break Leibniz never arise — every product with the constant factor is
exact in all three slots. We use only `pres-*`{.Agda} of the
homomorphism and the product law directly, never `D-leibniz`{.Agda}, so
we never touch the component where truncation lies.
