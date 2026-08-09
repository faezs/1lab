<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative using (∂-of)
open import Data.Real.Smooth.Integral using (pt)
open import Data.Real.Smooth.Calculus using (∂-mul)
open import Data.Real.Smooth.FTC using (Constancy)

open import Data.Fin using (Fin ; fzero)
open import Data.Dec
```
-->

```agda
module Physics.FiniteTime where
```

# Conservation over finite time {defines="finite-time-conservation"}

Every conservation law this development has proved so far has been
*infinitesimal*. In the [[smooth world|smooth-world]] the statement
"energy is conserved" is discharged by showing that the synthetic
derivative of the energy vanishes: for every nilsquare $\varepsilon$,
$E(t + \varepsilon) = E(t)$. That is a real theorem, and it is the
right theorem — but it is a statement about *infinitesimal*
displacement. Getting from it to "the energy at time $b$ equals the
energy at time $a$", for honest rationals $a$ and $b$ a finite
distance apart, is exactly the step that
[[Constancy|smooth-infinitesimal-analysis]] is *assumed* as an axiom
for in Bell's axiomatics: in SIA one **postulates** that a function
with identically vanishing derivative is constant, because the
synthetic layer has no integral with which to prove it.

Over the [[Dedekind reals|dedekind-real]] we no longer have to assume
it. The [[Riemann integral|riemann-integral]] of a
[[bounded-smooth|bounded-smooth-function]] function is *constructed*,
its convergence is proved, and the [[first direction of the
Fundamental Theorem|ftc-direction-one]] identifies the integral of a
derivative with the endpoint difference. The constancy principle is a
corollary. This module is where that corollary is cashed out for the
physics layer: **a conserved quantity of a bounded-smooth trajectory
takes the same value at every rational time**, not merely at
infinitesimally displaced ones.

## Conservation on an oriented interval

Fix a *quantity along a trajectory*: a real-valued function $E$ of a
single time coordinate — the energy, or any other observable
evaluated along a solution — together with a bounded-smooth structure
$A$ for it. Its time derivative is `∂-of E fzero A`{.Agda}, the
depth-two Hadamard quotient on the diagonal in the unique direction.

The **conservation hypothesis** is that this derivative vanishes at
every *rational time*: $\dot E(q) = 0$. Over a time interval $[a,b]$
oriented by $a \le b$, this forces the two endpoint readings to
agree.

```agda
conserved-on-interval
  : (E : Fun 1) (A : Smooth⁺ 1 E)
  → (a b : Ratio) → a ≤ b
  → (∀ q → ∂-of E fzero A (pt q) ≡ 0ᴿ)
  → E (pt b) ≡ E (pt a)
conserved-on-interval E A a b a≤b conserved = Constancy E A a b a≤b conserved
```

The proof is entirely in the analytic layer: every Riemann sum of the
identically-vanishing derivative is literally $0$, so $0$ is *a*
Riemann limit of $\dot E$; the telescope of
[[FTC|ftc-direction-one]] says $E(b) - E(a)$ is *a* Riemann limit of
$\dot E$; and Riemann limits are unique. Notably no Lipschitz
witness — and hence no construction of the integral itself — is
needed for this direction, only the convergence machinery it was
built from.

## Conservation at all times

The orientation $a \le b$ in the statement above is an artefact of how
the dyadic partition is laid down, not of the physics: a conserved
quantity does not know which of two instants came first. Since the
rational order is weakly total and the conclusion is an equation
between reals, we can dispose of the hypothesis by cases and read the
interval backwards when needed.

```agda
conserved-everywhere
  : (E : Fun 1) (A : Smooth⁺ 1 E)
  → (∀ q → ∂-of E fzero A (pt q) ≡ 0ᴿ)
  → (s t : Ratio) → E (pt s) ≡ E (pt t)
conserved-everywhere E A conserved s t with holds? (s ≤ t)
... | yes s≤t  = sym (conserved-on-interval E A s t s≤t conserved)
... | no ¬s≤t  = conserved-on-interval E A t s
                   (≤-is-weakly-total s t ¬s≤t) conserved
```

This is the genuine finite-time statement, and it is the one the
physics layer wanted all along: an observable whose *instantaneous*
rate of change vanishes has *globally* constant readings. The
synthetic layer can state the hypothesis but cannot reach the
conclusion; here the conclusion is a theorem.

<!--
```agda
private
  *ᴿ-zeror : ∀ x → x *ᴿ 0ᴿ ≡ 0ᴿ
  *ᴿ-zeror x =
      sym (+ᴿ-idr (x *ᴿ 0ᴿ))
    ∙ ap ((x *ᴿ 0ᴿ) +ᴿ_) (sym (+ᴿ-invr (x *ᴿ 0ᴿ)))
    ∙ +ᴿ-assoc (x *ᴿ 0ᴿ) (x *ᴿ 0ᴿ) (-ᴿ (x *ᴿ 0ᴿ))
    ∙ ap (_+ᴿ (-ᴿ (x *ᴿ 0ᴿ)))
        ( sym (*ᴿ-distribˡ x 0ᴿ 0ᴿ)
        ∙ ap (x *ᴿ_) (+ᴿ-idr 0ᴿ))
    ∙ +ᴿ-invr (x *ᴿ 0ᴿ)
```
-->

## A closed instance

The principle is only worth as much as the hypotheses one can
actually *discharge*, so before any parametrised example, here is one
that assumes nothing at all. A constant observable has vanishing
derivative by `∂-const`{.Agda} — the equation holds by
`refl`{.Agda} — so its conservation is a closed theorem of this
development, with no hypothesis left standing.

```agda
constant-conserved
  : (c : ℝ) (s t : Ratio)
  → (λ (_ : Fin 1 → ℝ) → c) (pt s) ≡ (λ (_ : Fin 1 → ℝ) → c) (pt t)
constant-conserved c = conserved-everywhere
  (λ _ → c) (smooth⁺-const c) (λ _ → refl)
```

## A worked conservation law

The next instance carries computational content rather than a new
hypothesis: its vanishing derivative is *derived*, through the
Leibniz rule, rather than read off.

Let $u$ be a bounded-smooth quantity that is **stationary**: its own
derivative vanishes identically. (Physically: a free particle's
momentum under no force, or an amplitude at a critical
configuration.) The associated *quadratic* observable $u^2$ — a
kinetic energy, up to the mass factor — is then conserved, and its
derivative is computed by [[Leibniz|derivative-calculus]] as
$u\dot u + u\dot u$ before the hypothesis is used at all.

Two honest caveats about what this instance does and does not show.
Stationarity of $u$ is *assumed*, exactly as strong as the hypothesis
of the theorem it feeds; nothing is discharged here that was not
already granted. And since a stationary $u$ is itself constant by
`conserved-everywhere`{.Agda}, the conclusion for $u^2$ also follows
in one line from that constancy, without Leibniz. What the instance
genuinely exhibits is that the *product* bounded-smooth structure
`smooth⁺-mul`{.Agda} and the derivative calculus compute correctly
through the finite-time principle — not an independent conservation
law.

```agda
module _ (u : Fun 1) (Au : Smooth⁺ 1 u)
         (stationary : ∀ x → ∂-of u fzero Au x ≡ 0ᴿ) where

  u² : Fun 1
  u² v = u v *ᴿ u v

  A² : Smooth⁺ 1 u²
  A² = smooth⁺-mul Au Au
```

The bounded-smooth structure on $u^2$ is the canonical product
structure, so its derivative is *computed* by `∂-mul`{.Agda}: two
copies of $u \cdot \dot u$, each of which the hypothesis kills.

```agda
  square-stationary : ∀ x → ∂-of u² fzero A² x ≡ 0ᴿ
  square-stationary x =
      ∂-mul Au Au fzero x
    ∙ ap₂ _+ᴿ_ leibniz-term leibniz-term
    ∙ +ᴿ-idr 0ᴿ
    where
      leibniz-term : (u x *ᴿ ∂-of u fzero Au x) ≡ 0ᴿ
      leibniz-term = ap (u x *ᴿ_) (stationary x) ∙ *ᴿ-zeror (u x)
```

Feeding that into the finite-time principle gives the conservation
law: the energy reading is the same at *every* pair of rational
times, with no orientation and no interval fixed in advance.

```agda
  square-conserved : (s t : Ratio) → u² (pt s) ≡ u² (pt t)
  square-conserved =
    conserved-everywhere u² A² (λ q → square-stationary (pt q))
```

## What is and is not proven

Proven here, with no postulates, no holes and no choice:

* `conserved-on-interval`{.Agda} — a bounded-smooth observable with
  identically vanishing time derivative has equal readings at the two
  ends of any oriented rational interval;
* `conserved-everywhere`{.Agda} — the same with the orientation
  hypothesis eliminated, i.e. *finite-time conservation* proper;
* `square-conserved`{.Agda} — a worked instance in which the vanishing
  of the derivative is obtained from the Leibniz rule applied to the
  canonical product structure, not by inspection of the function.

The only hypotheses are the ones written into the types: a
bounded-smooth structure `Smooth⁺ 1 E`{.Agda} for the observable — the
honest constructive replacement for "$E$ is smooth", carrying an
explicit tower of Hadamard quotients together with box bounds at every
level — and the vanishing of `∂-of E fzero A`{.Agda}. Both are module
or record *parameters*; nothing is asserted.

**Not** proven, and worth naming so the boundary is visible:

* **No ODE existence or uniqueness.** Nothing here produces a
  trajectory from a differential law; the trajectory (and its
  bounded-smooth structure) is an input. Picard iteration needs the
  *second* direction of the Fundamental Theorem,
  $\frac{\d}{\d t}\int_a^t f = f$, which
  [[FTC|ftc-direction-one]] explicitly does not attempt: it requires a
  fresh total Hadamard quotient manufactured from the integral
  remainder.
* **No Noether theorem.** Deriving a conserved quantity *from* a
  symmetry, rather than being handed one, again needs direction two
  (to integrate the variation) as well as the variational calculus on
  path space.
* **Rational times only.** The conclusion quantifies over rational
  instants, since that is the domain the dyadic partition and
  `pt`{.Agda} are indexed by. Extending to arbitrary real times needs a
  continuity argument for $E$ along the Cauchy approximation of a real,
  which the present development does not carry.
* **One dimension.** The observable is a function of a single time
  coordinate. Conservation along higher-dimensional parameter spaces
  would need iterated integrals over boxes, outside the scope of the
  analytic layer as built.

Against the synthetic side: `Physics.SmoothWorld`{.Agda} obtains
stationarity from nilsquare infinitesimals and takes Constancy as an
explicit hypothesis record, precisely because the smooth world has no
integral. This module needs no such hypothesis — the integral exists,
so the principle is a theorem, and the physics layer can finally say
"conserved" and mean it over finite time.
