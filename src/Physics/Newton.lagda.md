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
module Physics.Newton where
```

# Newton's second law, algebraically {defines="newtons-second-law"}

[[Hamiltonian mechanics|harmonic-oscillator]] over the dual numbers
turned "the velocity is the infinitesimal flow of position" into a
theorem about square-zero elements. Pushing the same idea one order
further — replacing the dual numbers by the [[second-order Weil
algebra|second-order-weil-algebra]] $W_2$, whose elements are jets
$a + b\delta + c\delta^2$ rather than mere tangent vectors — lets
*acceleration* enter algebraically too, and with it Newton's second
law $F = ma$: not an axiom, but the readout of the [[jet
derivative|jet-derivative]] applied twice.

## Second-order Taylor expansion

A polynomial observable, evaluated at the thickened point $\hat x +
\delta$ of $W_2$ built over the polynomial ring itself, expands to
second order: the constant term is the value, the $\delta$-term is
the first derivative, and the $\delta^2$-term is *half* the second
derivative — except that no division by two has been assumed, so
what appears is honestly the *undivided* second derivative, matching
the convention of the [[jet derivative|jet-derivative]] $D$.

```agda
module second-order {ℓ} (R : CRing ℓ) where
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
```
-->

```agda
  x̂ : ⌞ Obs ⌟
  x̂ = var (lift fzero)

  V : ⌞ Obs ⌟
  V = x̂ *ₚ x̂

  taylor₂ : CR.Hom Obs (WObs.W₂)
  taylor₂ = extend (WObs.ι CR.∘ con-hom) (λ _ → x̂ , con R'.1r , con R'.0r)
```

The value, the derivative $2x$, and the undivided second derivative
$1$ (the curvature of the potential, standing in for the stiffness of
the spring) all appear at once, as the three components of a single
jet — mostly by definitional unfolding of `extend`{.Agda} on the
constructors of `V`{.Agda}, cleaned up by the same identity and
zero laws that closed `hooke`{.Agda} in
[[the harmonic oscillator|harmonic-oscillator]].

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
  V-jet : taylor₂ .∫Hom.fst V ≡ (x̂ *ₚ x̂ , x̂ +ₚ x̂ , con R'.1r)
  V-jet = ap₂ _,_ refl (ap₂ _,_ V-jet-1 V-jet-2)
```

## Newton's second law {defines="newtons-second-law-jet-flow"}

A trajectory of the harmonic oscillator, tracked to second order, is
a pair of jets $X = (x_0, v, c_x)$ and $P = (p_0, w, c_p)$ in
$W_2$ — position and momentum, each carrying its own value, velocity,
and curvature coefficient. Hamilton's equations $\dot X = P$ and
$\dot P = -X$ are equations of jets, but the [[jet
derivative|jet-derivative]] $D$ only sees two orders below its input,
so they can only honestly be asked to hold in the two degrees where
$D$ still carries content — the same truncation already forced on
the [[Leibniz rule|jet-derivative]] for $D$ itself.

```agda
module second-order-flow {ℓ} (R : CRing ℓ) where
  module W = Weil R
```

<!--
```agda
  private
    module R' = CRing-on (R .snd)
```
-->

```agda
  record is-jet-flow (X P : ⌞ W.W₂ ⌟) : Type ℓ where
    field
      velocity₀ : X .snd .fst ≡ P .fst
      velocity₁ : X .snd .snd R'.+ X .snd .snd ≡ P .snd .fst
      force₀    : P .snd .fst ≡ R'.- (X .fst)
      force₁    : P .snd .snd R'.+ P .snd .snd ≡ R'.- (X .snd .fst)
```

**Newton's second law is the composite of two of these fields**:
chasing $\dot X = P$ into its middle degree and substituting
$\dot P = -X$ in its zeroth degree reads off exactly $2c_x = -x_0$ —
twice the acceleration coefficient equals (minus) the restoring
force. This is $F = ma$ with the mass and the spring constant both
set to one, and the $\textstyle\frac12$ of $x(t) = x_0 + vt +
\textstyle\frac12 at^2$ made visible as the *un*divided power that it
always secretly was.

```agda
  newton
    : ∀ {X P} → is-jet-flow X P
    → X .snd .snd R'.+ X .snd .snd ≡ R'.- (X .fst)
  newton flow = velocity₁ ∙ force₀
    where open is-jet-flow flow
```

Such flows exist: given any initial position $x_0$ and momentum
$p_0$, and *any* choice of curvature coefficients $c_x, c_p$
satisfying the halving constraints that `velocity₁`{.Agda} and
`force₁`{.Agda} demand, the triples $X = (x_0, p_0, c_x)$ and $P =
(p_0, -x_0, c_p)$ solve the truncated Hamilton equations — the first
two fields discharge by `refl`, the last two by hypothesis.

```agda
  jet-flow
    : ∀ x₀ p₀ cₓ cₚ
    → cₓ R'.+ cₓ ≡ R'.- x₀
    → cₚ R'.+ cₚ ≡ R'.- p₀
    → is-jet-flow (x₀ , p₀ , cₓ) (p₀ , R'.- x₀ , cₚ)
  jet-flow x₀ p₀ cₓ cₚ hv hp .is-jet-flow.velocity₀ = refl
  jet-flow x₀ p₀ cₓ cₚ hv hp .is-jet-flow.velocity₁ = hv
  jet-flow x₀ p₀ cₓ cₚ hv hp .is-jet-flow.force₀    = refl
  jet-flow x₀ p₀ cₓ cₚ hv hp .is-jet-flow.force₁    = hp
```

Over a $\bQ$-algebra the halves $c_x = -\textstyle\frac12 x_0$ and
$c_p = -\textstyle\frac12 p_0$ exist and are unique, so the jet flow
through any initial condition is unique too. Over a general
commutative ring — the integers, say — no such half need exist at
all: this is exactly why the discrete simulator of
[[the harmonic oscillator|harmonic-oscillator]] does not integrate a
jet flow directly, but instead advances by the *exact* quarter-period
map $(x, p) \mapsto (p, -x)$, a symplectic rotation that sidesteps
needing $\textstyle\frac12$ by never asking for the second-order
coefficient in the first place.
