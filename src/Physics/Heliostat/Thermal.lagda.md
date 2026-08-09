<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Solver
open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Cat.Displayed.Total

open import Data.Fin using (Fin ; fzero)

import Algebra.Ring.Polynomial
import Algebra.Ring.DualNumbers as Dual
import Algebra.Ring.Reasoning
import Cat.Reasoning

open is-ring-hom
```
-->

```agda
module Physics.Heliostat.Thermal where
```

# The receiver's thermal dynamics, synthetically {defines="heliostat-receiver-thermal"}

The [[heliostat|higher-topos-theory-in-physics]] aims a mirror so that
the reflected sunbeam lands on a fixed absorber — the *receiver*. Once
the light arrives a second story begins: the receiver *heats up*, and
its temperature settles where the absorbed solar power balances the
heat it sheds back to its surroundings. That balance is a
one-dimensional dynamical system, and — exactly as with the
[[harmonic oscillator|harmonic-oscillator]] and the mirror's own
[[optics|kock-lawvere]] — its differential content is *synthetic*: the
linear-stability rate of the receiver is a [[dual-number|dual-numbers]]
derivative, the steady-state energy balance is a ring identity, and the
forward-Euler integrator's failure is exactly the $(\mathrm{d}t)^2$
term that the nilpotency $\epsilon^2 = 0$ kills. No limits, no
division, no reals — just constructive algebra over any [[commutative
ring|commutative-ring]] of scalars, in the same style
`Physics.Oscillator`{.Agda} derives Hooke's law and the Euler energy
defect.

## The flux functional and its physical constants

Lumped-parameter thermodynamics models the receiver as a single body
at temperature $T$, with heat capacity $C$, gaining power and losing it
through two channels. The net power into the body is the **flux
functional**
$$
\Phi(T) \;=\; P \;-\; h\,(T - T_\infty) \;-\; \sigma\varepsilon A\,(T^4 - T_\infty^4),
$$
where $P$ is the absorbed solar power delivered by the mirror, $h$ the
convective coefficient, $T_\infty$ the ambient temperature, and
$\sigma\varepsilon A$ the effective Stefan–Boltzmann radiative
prefactor (emissivity $\varepsilon$, area $A$, Stefan's constant
$\sigma$). The first loss term is **Newton's law of cooling**, linear
in the temperature excess; the second is **grey-body radiation**,
quartic in the absolute temperature. The evolution is $C\dot T =
\Phi(T)$ — we keep $C$ on the left throughout and never divide by it,
so the whole development stays over an arbitrary commutative ring.

The constants $P, h, \sigma\varepsilon A, T_\infty$ enter as *scalars*
of the coefficient ring $R$: they are injected into the observable ring
as `con`{.Agda}stants, while the temperature $T$ alone is the
polynomial variable. That placement is what makes the constants
differentiate to zero automatically, leaving only the response of the
two loss channels to a change in $T$. The heat capacity $C$ never
appears as a coefficient — it stays on the left of $C\dot T = \Phi$ —
so it is not among the module parameters at all.

```agda
module thermal {ℓ} (R : CRing ℓ) (P h σεA T∞ : ⌞ R ⌟) where
  open Algebra.Ring.Polynomial R
```

<!--
```agda
  private
    R[T] : CRing ℓ
    R[T] = R[ Lift ℓ (Fin 1) ]

    module R' = CRing-on (R .snd)
    module RT = CRing-on (R[T] .snd)
    module Rr = Algebra.Ring.Reasoning (R[T] .fst , R[T] .snd .CRing-on.has-ring-on)
    module CR = Cat.Reasoning (CRings ℓ)
```
-->

The single observable variable is the temperature $\hat T$; the
constants ride along as `con`{.Agda}stants. Because only the *slope* in
$\hat T$ governs stability, and only a zero of the flux governs the
balance, we record $\Phi$ in its **expanded** monomial form. The two
ambient offsets are folded into single scalar `con`{.Agda}stants — the
convective offset $P + h\,T_\infty$ into the first summand, the
radiative offset $\sigma\varepsilon A\,T_\infty^4$ into the second — and
the two temperature-dependent losses appear as the bare monomials $-h
\hat T$ and $-\sigma\varepsilon A\,\hat T^4$. This is precisely $P -
h(\hat T - T_\infty) - \sigma\varepsilon A(\hat T^4 - T_\infty^4)$ with
the minus signs distributed; writing it this way keeps every
differentiated product a clean `con`{.Agda}stant-times-a-monomial, so
the derivative below collapses through unit and zero laws alone — no
distributive step, no `cring!`{.Agda} needed for the derivative itself.
Folding each offset into a *single* `con`{.Agda} (rather than a sum of
two `con`{.Agda}s) is deliberate: `δ`{.Agda} of one `con`{.Agda} is
`con R'.0r`{.Agda} on the nose, so `Rr.+-idl`{.Agda} clears it in the
stability proof without an intervening `con-+`{.Agda} step.

```agda
  T̂ : ⌞ R[T] ⌟
  T̂ = var (lift fzero)

  T̂⁴ : ⌞ R[T] ⌟
  T̂⁴ = ((T̂ *ₚ T̂) *ₚ T̂) *ₚ T̂

  Φ : ⌞ R[T] ⌟
  Φ = (con (P R'.+ (h R'.* T∞)) +ₚ negₚ (con h *ₚ T̂))
    +ₚ (con (σεA R'.* (((T∞ R'.* T∞) R'.* T∞) R'.* T∞))
         +ₚ negₚ (con σεA *ₚ T̂⁴))
```

## The stability rate, from a dual-number derivative

The linear stability of a steady state is governed by the slope
$\delta\Phi/\delta T$: a small perturbation $\delta T$ relaxes at rate
$\delta\Phi/\delta T$, so the receiver is stable precisely when this
slope is negative. We compute it *synthetically*, by the same
Kock–Lawvere recipe that derived Hooke's law from the oscillator's
potential — evaluate $\Phi$ at the thickened point $\hat T + \epsilon$
of the [[dual numbers|dual-numbers]] and read off the coefficient of
$\epsilon$. Each variable's $\epsilon$-seed is `con R'.1r`{.Agda}, the
direction along which we differentiate.

```agda
  taylor : CR.Hom R[T] (Dual.R[ε] R[T])
  taylor = extend (Dual.ι-dual R[T] CR.∘ con-hom) (λ _ → T̂ , con R'.1r)

  δ : ⌞ R[T] ⌟ → ⌞ R[T] ⌟
  δ p = taylor .∫Hom.fst p .snd
```

The quartic is the only nontrivial piece. Where the oscillator's
`hooke`{.Agda} differentiated a *square* in one Leibniz step, the
radiative term is a *fourth power*, and the [[Leibniz
rule|jet-derivative]] that dual multiplication carries in its
$\epsilon$-component fires once at each nesting of the left-associated
product $((\hat T\hat T)\hat T)\hat T$. Every differentiated factor
carries the $\epsilon$-seed `con R'.1r`{.Agda}, so it collapses through
the unit laws `Rr.*-idr`{.Agda} ($x\cdot 1 = x$) and `*ₚ-idl`{.Agda}
($1\cdot x = x$) — exactly the two rewrites of `hooke`{.Agda} — leaving
the Leibniz tree of cubes.

<!--
```agda
  private
    δ⁴-lemma
      : δ T̂⁴
      ≡ ((T̂ *ₚ T̂) *ₚ T̂)
      +ₚ (((T̂ *ₚ T̂) +ₚ ((T̂ +ₚ T̂) *ₚ T̂)) *ₚ T̂)
    δ⁴-lemma =
      ap₂ _+ₚ_
        Rr.*-idr
        (ap (_*ₚ T̂)
          (ap₂ _+ₚ_
            Rr.*-idr
            (ap (_*ₚ T̂) (ap₂ _+ₚ_ Rr.*-idr (*ₚ-idl T̂)))))
```
-->

```agda
  δT⁴ : δ T̂⁴
      ≡ ((T̂ *ₚ T̂) *ₚ T̂)
      +ₚ (((T̂ *ₚ T̂) +ₚ ((T̂ +ₚ T̂) *ₚ T̂)) *ₚ T̂)
  δT⁴ = δ⁴-lemma
```

Read as physics this is $4\hat T^3$. The outer summand $(\hat T\hat
T)\hat T$ is one cube outright; the inner factor $\hat T\hat T + (\hat T
+ \hat T)\hat T$, multiplied by the trailing $\hat T$, distributes to
three more copies of $\hat T^3 = (\hat T\hat T)\hat T$ once one applies
the distributive law $(\hat T + \hat T)\hat T = \hat T^3 + \hat T^3$.
Distributing is a further ring step past what the unit laws alone
reach, so we stop at the honest normal form the derivative
*definitionally* produces — the four-fold cube is grouped, not yet
summed flat — and "$4\hat T^3$" is the reading of that normal form, not
a separately collapsed theorem. This is the same discipline
`Physics.Newton`{.Agda} keeps when it leaves a jet's components in
definitional shape.

With the quartic in hand, the derivative of the *whole* flux follows by
additivity of $\delta$ across the sum and the vanishing of the
constants. The absorbed power $P$, both ambient offsets $h\,T_\infty$
and $\sigma\varepsilon A\,T_\infty^4$ are all `con`{.Agda}stants, so
their $\epsilon$-components are `con R'.0r`{.Agda} and drop out; the
linear term contributes $-h$ (its $\epsilon$-slot $h\cdot 1 + 0\cdot
\hat T$ collapsing by `Rr.*-idr`{.Agda}, `Rr.*-zerol`{.Agda} and
`Rr.+-idr`{.Agda}) and the quartic contributes $-\sigma\varepsilon
A\cdot\delta(\hat T^4)$ (its zero cross term cleared the same way). The
result is the **stability rate**
$$
\frac{\delta\Phi}{\delta T} \;=\; -h \;-\; \sigma\varepsilon A\,\delta(\hat T^4),
$$
which, reading $\delta(\hat T^4) = 4\hat T^3$, is the eigenvalue
$-(h + 4\sigma\varepsilon A\,T^3)$ of the linearized receiver: always
negative for positive constants and temperature, so the steady state
below is **linearly stable**.

<!--
```agda
  private
    δ-lin : δ (con h *ₚ T̂) ≡ con h
    δ-lin = ap₂ _+ₚ_ Rr.*-idr Rr.*-zerol ∙ Rr.+-idr

    δ-rad : δ (con σεA *ₚ T̂⁴) ≡ con σεA *ₚ δ T̂⁴
    δ-rad = ap ((con σεA *ₚ δ T̂⁴) +ₚ_) Rr.*-zerol ∙ Rr.+-idr
```
-->

```agda
  stability-rate
    : δ Φ ≡ negₚ (con h) +ₚ negₚ (con σεA *ₚ δ T̂⁴)
  stability-rate =
    ap₂ _+ₚ_
      (ap₂ _+ₚ_ refl (ap negₚ δ-lin) ∙ Rr.+-idl)
      (ap₂ _+ₚ_ refl (ap negₚ δ-rad) ∙ Rr.+-idl)
```

The left summand of $\delta\Phi$ is $\delta(\text{const}) + \delta(-h
\hat T)$; the constant slot is `con R'.0r`{.Agda} by definitional
unfolding of `taylor`{.Agda} on a `con`{.Agda}, so `Rr.+-idl`{.Agda}
discards it, leaving $-h$. The right summand is $\delta(\text{const}) +
\delta(-\sigma\varepsilon A\,\hat T^4)$, whose constant slot again
vanishes and whose surviving piece is $-\sigma\varepsilon A\,\delta(\hat
T^4)$.

## Steady state: absorbed = convected + radiated

A **steady state** $T^\ast$ is a zero of the flux, $\Phi(T^\ast) = 0$:
the temperature at which the receiver neither heats nor cools. At such
a point the power bookkeeping closes — the absorbed solar power equals
the sum of what convection and radiation carry away. This is a purely
*algebraic* rearrangement of $\Phi = 0$, so we prove it at the scalar
level over $R$, where the [[ring solver|commutative-ring]]
`cring!`{.Agda} discharges the identity in one line. Working over $R$
(not $R[T]$) is exactly what lets `cring!`{.Agda} fire: it is the
abstract module parameter, as the `cancel`{.Agda} and
`square-growth`{.Agda} lemmas of `Physics.Oscillator`{.Agda} require.

We package the three energy channels as scalar functions of a
temperature $t : \lfloor R\rfloor$: `absorbed`{.Agda} is the constant
$P$, `convected`{.Agda} is $h(t - T_\infty)$, and `radiated`{.Agda} is
$\sigma\varepsilon A(t^4 - T_\infty^4)$. The flux at $t$ is `absorbed −
convected − radiated`.

```agda
  absorbed convected radiated fluxR : ⌞ R ⌟ → ⌞ R ⌟
  absorbed  _ = P
  convected t = h R'.* (t R'.- T∞)
  radiated  t = σεA R'.* ((((t R'.* t) R'.* t) R'.* t)
                          R'.- (((T∞ R'.* T∞) R'.* T∞) R'.* T∞))
  fluxR     t = (P R'.- convected t) R'.- radiated t
```

The algebraic content is a single ring identity: the absorbed power
*is* the sum of the two losses plus whatever net flux remains. When
that net flux is zero, the balance is exact. We state it directly on the
channel aliases — the solver unfolds them, and every subtraction with
them, down to the ring's own $+$, $\cdot$ and $-$ that its reflection
recognizes.

<!--
```agda
  private abstract
    balance-identity
      : ∀ t → absorbed t ≡ (convected t R'.+ radiated t) R'.+ fluxR t
    balance-identity t = cring! R
```
-->

```agda
  energy-balance
    : ∀ t → fluxR t ≡ R'.0r
    → absorbed t ≡ convected t R'.+ radiated t
  energy-balance t p =
      balance-identity t
    ∙ ap ((convected t R'.+ radiated t) R'.+_) p
    ∙ R'.+-idr
```

At a steady temperature $T^\ast$, then, the absorbed solar power the
mirror delivers is spent exactly on convective and radiative losses:
the receiver's **first law of thermodynamics**, in equilibrium, as a
theorem rather than an assumption.

## The forward-Euler defect

A finite-time simulation of the relaxation cannot use the synthetic
derivative directly — assembling finite evolution from an infinitesimal
generator needs *integration*, which (as for the oscillator) waits on
real analysis. The crudest finite scheme is **forward Euler**. Linearize
the relaxation about a reference so that the scaled temperature $y :=
C\,T$ obeys $\dot y = -k\,y$ for a rate $k$ (the stability eigenvalue
above, carrying its sign); one Euler step over $\mathrm{d}t$ sends $y$
to $y - \mathrm{d}t\,k\,y$.

The exact continuous relaxation would multiply $y$ by a genuine
exponential; the Euler step multiplies it by the truncated factor $1 -
\mathrm{d}t\,k$. The two agree to first order in $\mathrm{d}t$ and
differ at second order — and that defect is, once again, *exactly* a
$(\mathrm{d}t)^2$ term, the term $\epsilon^2 = 0$ annihilates.
Concretely, comparing one Euler step against the two-term expansion
$y - \mathrm{d}t\,k\,y + (\mathrm{d}t\,k)^2 y$ (kept undivided, so no
halving is assumed and no $\bQ$-algebra is needed), the miss is
precisely the quadratic remainder $(\mathrm{d}t)^2 k^2 y$. We state it
as an equation the ring solver closes over the abstract $R$, mirroring
`euler-energy-defect`{.Agda} of `Physics.Oscillator`{.Agda} exactly.

```agda
  euler-step : ⌞ R ⌟ → ⌞ R ⌟ → ⌞ R ⌟ → ⌞ R ⌟
  euler-step dt k y = y R'.- ((dt R'.* k) R'.* y)
```

<!--
```agda
  private abstract
    euler-defect-identity
      : ∀ dt k y
      → (y R'.- ((dt R'.* k) R'.* y)) R'.+ ((dt R'.* dt) R'.* ((k R'.* k) R'.* y))
      ≡ (y R'.- ((dt R'.* k) R'.* y)) R'.+ (((dt R'.* k) R'.* (dt R'.* k)) R'.* y)
    euler-defect-identity dt k y = cring! R
```
-->

```agda
  euler-relaxation-defect
    : ∀ dt k y
    → euler-step dt k y R'.+ ((dt R'.* dt) R'.* ((k R'.* k) R'.* y))
    ≡ (y R'.- ((dt R'.* k) R'.* y)) R'.+ (((dt R'.* k) R'.* (dt R'.* k)) R'.* y)
  euler-relaxation-defect = euler-defect-identity
```

The Euler integrator undershoots the true relaxation by exactly
$(\mathrm{d}t)^2 k^2 y$ per step — the same quadratic-in-$\mathrm{d}t$
error that plagues the oscillator's symplectic Euler, and the same term
the nilpotent $\epsilon$ discards. The synthetic derivative sees the
relaxation rate *exactly*; the finite integrator pays for the missing
higher-order exponential in quadratic coin.

## What is and is not proven

Machine-checked here, over an *arbitrary* commutative ring $R$ with
scalars $P, h, \sigma\varepsilon A, T_\infty$ and **no division and no
postulates**:

- the **stability rate** `stability-rate`{.Agda}: the dual-number
  derivative of the flux functional is $\delta\Phi = -h - \sigma
  \varepsilon A\,\delta(\hat T^4)$, with the constants $P$, $h\,T_\infty$
  and $\sigma\varepsilon A\,T_\infty^4$ differentiating away — the
  receiver's linear-stability eigenvalue, derived, not posited;
- the **quartic derivative** `δT⁴`{.Agda}: the synthetic $\delta(\hat
  T^4)$ reduced by the Leibniz/unit-law chain to the grouped four-cube
  normal form whose reading is $4\hat T^3$;
- the **steady-state energy balance** `energy-balance`{.Agda}: at a zero
  of the flux, absorbed power equals convected plus radiated power — the
  equilibrium first law, a `cring!`{.Agda} identity over $R$;
- the **forward-Euler defect** `euler-relaxation-defect`{.Agda}: the
  Euler step of the linearized relaxation misses the second-order step
  by precisely a $(\mathrm{d}t)^2$ term, mirroring the oscillator's
  `euler-energy-defect`{.Agda}.

What is **not** proven, and deliberately so. The headline $\delta(\hat
T^4) = 4\hat T^3$ is stated as the derivative's honest *definitional*
normal form (a grouped tree of four cubes, one branch still bearing an
undistributed $\hat T + \hat T$); the flat "$4\hat T^3$" is its prose
reading, since distributing to a single $4\hat T^3$ is real ring
algebra we do not perform — exactly as `Physics.Newton`{.Agda} leaves
its jet components in definitional shape. The stability rate is likewise
stated as $-h - \sigma\varepsilon A\,\delta(\hat T^4)$ with
$\delta(\hat T^4)$ left as the opaque derivative, not further reduced.
Most importantly, **no finite-time solution of the thermal ODE $C\dot T
= \Phi(T)$ is constructed**: integrating the relaxation to an actual
cooling curve $T(t)$ needs the exponential, hence Taylor coefficients
$1/n!$ and a genuine limit — the same wall of *integration* at which the
[[oscillator|harmonic-oscillator]]'s continuous-time flow stops, and
which the [[reading guide|higher-topos-theory-in-physics]] lists among
the missing analytic ingredients. Everything at the *differential*
level — the stability rate, the equilibrium balance, the quantified
Euler defect — is synthetic and exact; the cooling curve itself waits on
a multiplicative theory of the reals, which the 1Lab does not yet have.
