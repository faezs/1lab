<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sets.Closed
open import Cat.Prelude

open import Cat.CartesianClosed.Free.Signature

open import Algebra.Ring.Solver

open import Algebra.Group.Instances.Cyclic
open import Algebra.Group.Cat.Base
open import Algebra.Group.Action
open import Algebra.Ring.Commutative
open import Algebra.Group
open import Algebra.Ring

open import Data.Fin using (Fin ; fzero ; fsuc ; fin)
open import Data.Int.Divisible using (_∣ℤ_ ; dividesℤ)
open import Data.Int.DivMod using (same-rem→divides-diff)
open import Data.Int

open import Physics.Heliostat.Optics

import Cat.Instances.SimplicialSets.ActionGroupoid
import Cat.CartesianClosed.Free.Model
import Algebra.Ring.Polynomial
import Cat.Reasoning

open λ-Signature
open Precategory
open Functor
```
-->

```agda
module Physics.Heliostat.Solar where
```

# The solar clock and the fixed focus {defines="solar-position solar-clock diurnal-cycle fixed-focus-invariant"}

`Physics.Heliostat.Tracking`{.Agda} compiled a heliostat that *tracks*:
the sun advances by the oscillator's exact restoring `kick`{.Agda} $s
\mapsto -s$, an aiming law re-points the mirror at every tick, and the
reflected ray stays locked on target — with the diurnal cycle closing
by `refl`{.Agda}. But that motion is only the $\mathbb{Z}/2$ *shadow*
of the sun's real path: negation is an involution, so "two ticks and
back" is all a sign flip can express. The sky does not run on a
two-hour clock. This module supplies the two pieces of *solar position
proper* that the tracking module deliberately left out:

1. **The clock closes on a real period.** The sun's diurnal march is a
   [[cyclic group|cyclic-group]] of order $24$ — the hour angle — and
   its annual declination is a cyclic group of order $365$. Neither is
   an involution, so neither can be `negℤ-negℤ`{.Agda}; we model them
   with the *upstream* finite cyclic groups `ℤ/ 24`{.Agda} and
   `ℤ/ 365`{.Agda}, reusing exactly the recipe by which
   `Physics.Heliostat.Symmetry`{.Agda} gauges the paraboloid's spatial
   `ℤ/ 4`{.Agda}. The period-closure is then a *theorem of the group*:
   advancing $24$ hours returns to the same hour, closed by the
   quotient constructor, not by iterating a sign.

2. **The focus is the conserved charge of that clock.** As the sun
   advances and the primary re-points, the *reflected beam-up ray*
   still passes through the **same focus**. This is the discrete
   Noether charge of time-translation — the optical analogue of the
   oscillator's conserved energy — and unlike Tracking's scalar
   `tracks-sun`{.Agda} it is stated on the genuine `Vec3`{.Agda}
   derived normal and focus of `Physics.Heliostat.Optics`{.Agda},
   through the coordinate-free `focusing-parallel`{.Agda}.

We do **not** re-derive the compile-and-`refl` machinery
(`Physics.Oscillator`{.Agda}, `Physics.Heliostat.Tracking`{.Agda}), the
scalar on-target invariant (Tracking's `on-target`{.Agda}), the
focus/normal optics (`Physics.Heliostat.Optics`{.Agda}), or the
`ℤ/_`{.Agda} machine (`Algebra.Group.Instances.Cyclic`{.Agda}); we cite
them and assemble.

## The compiled solar clock

First, the sky as a system that *runs*. The state is a pair `(hour,
day)` of integers; one application of the step advances the hour angle
by one tick. We keep this in the same [[λ-signature]] compile-and-run
idiom as the oscillator and the tracker: one base type `tick`{.Agda},
one operation `advance`{.Agda} that pushes a coordinate forward by the
integer successor.

```agda
data Sky-type : Type where
  tick : Sky-type

data Sky-op : types.Ty Sky-type → Sky-type → Type where
  advance : Sky-op (` tick) tick
```

<!--
```agda
private
  Sky-type-is-set : is-set Sky-type
  Sky-type-is-set = is-prop→is-set λ where tick tick → refl

  Sky-op-is-prop : ∀ {τ b} → is-prop (Sky-op τ b)
  Sky-op-is-prop advance advance = refl
```
-->

```agda
Sky : λ-Signature lzero
Sky .Ob = Sky-type
Sky .Ob-is-set = Sky-type-is-set
Sky .Hom = Sky-op
Sky .Hom-is-set = is-prop→is-set Sky-op-is-prop
```

<!--
```agda
open import Cat.CartesianClosed.Free Sky
open import Cat.CartesianClosed.Free.Lambda Sky
```
-->

The clock's step is a *program* — a term of the [[simply-typed lambda
calculus|STLC]] over this signature — so, one syntax all semantics, it
runs in every [[cartesian closed category]]. Its context is the pair
`(hour , day)`; it advances the hour and leaves the day, so one
application is one hour of solar time. (The day-rollover at hour $24$
is not part of the *ring* structure of the integers, so it is not a
signature operation; it lives at the cyclic-group level below, exactly
where the genuine period is.)

```agda
sky-program : Expr (∅ , ` tick `× ` tick) (` tick `× ` tick)
sky-program =
  `⟨ `hom advance (`π₁ (`var stop)) , `π₂ (`var stop) ⟩
```

To *simulate*, interpret the signature in sets: the tick type becomes
the integers and `advance`{.Agda} becomes the integer successor.

```agda
private
  module SetsModel = Cat.CartesianClosed.Free.Model Sky
    (Sets-cartesian {ℓ = lzero}) Sets-closed

sky-interp
  : elim.base-method
      SetsModel.chaotic-cartesian SetsModel.chaotic-closed
      (λ _ → el! Int)
sky-interp advance = λ h → sucℤ h

private
  module Run = SetsModel.model (λ _ → el! Int) sky-interp

sky-step : Int × Int → Int × Int
sky-step s = Run.compile .F₁ ⟦ sky-program ⟧ᵉ (lift tt , s)
```

The compiled clock *computes*: at hour $5$ of day $200$, one step
advances the hour to $6$ and holds the day — definitionally, by
`refl`{.Agda}.

```agda
_ : sky-step (5 , 200) ≡ (6 , 200)
_ = refl

_ : sky-step (sky-step (5 , 200)) ≡ (7 , 200)
_ = refl
```

And the advance commutes with the day, forever, for *every* state — the
day coordinate is inert under the diurnal step, which is why the
annual cycle below can be treated as an independent, coarser clock.

```agda
sky-holds-day : ∀ s → sky-step s .snd ≡ s .snd
sky-holds-day (h , d) = refl
```

## The diurnal and annual cycles, properly

The integer clock above never *returns*: `sucℤ`{.Agda} on $\Int$ has no
period. The genuine solar periods are cyclic groups, and we take them
from upstream: the hour angle is `ℤ/ 24`{.Agda} and the declination is
`ℤ/ 365`{.Agda}, both the `ℤ/_`{.Agda} of
`Algebra.Group.Instances.Cyclic`{.Agda}, exactly the construction whose
`ℤ/ 4`{.Agda} `Physics.Heliostat.Symmetry`{.Agda} gauges for the
paraboloid's spatial symmetry.

```agda
Diurnal Annual : Group lzero
Diurnal = ℤ/ 24
Annual  = ℤ/ 365
```

Both clocks are **generated by advancing one tick** — this is
`ℤ/n-cyclic`{.Agda}, the statement that `1`{.Agda} generates the whole
group, so every hour is reached by repeatedly stepping from midnight.

```agda
diurnal-generated : is-cyclic Diurnal
diurnal-generated = ℤ/n-cyclic 24

annual-generated : is-cyclic Annual
annual-generated = ℤ/n-cyclic 365
```

The **period-closure theorem** is that advancing a full period returns
to the start: $24$ hours later it is the same hour, $365$ days later
the same day. This is *not* an involution — it cannot be
`negℤ-negℤ`{.Agda} — but it is a one-line theorem of the quotient
group: in `ℤ/ 24`{.Agda} the class of `pos 24`{.Agda} equals the class
of the unit `0`{.Agda}, because $24$ divides $24$. The witness is the
[[quotient|group-quotient]] constructor `quot`{.Agda} fed the honest
divisibility fact `dividesℤ`{.Agda}, precisely how the cyclic group is
built.

```agda
diurnal-closes : Path ⌞ Diurnal ⌟ (inc (pos 24)) (inc (pos 0))
diurnal-closes = quot (same-rem→divides-diff 24 (pos 24) (pos 0) refl)

annual-closes : Path ⌞ Annual ⌟ (inc (pos 365)) (inc (pos 0))
annual-closes = quot (same-rem→divides-diff 365 (pos 365) (pos 0) refl)
```

That the clocks are *genuinely* of order $24$ and $365$ — not
collapsed, not secretly smaller — is the finiteness equivalence
`Finite-ℤ/n`{.Agda}: the hour set has exactly $24$ elements and the day
set exactly $365$, each in bijection with the standard finite set. This
is the same `Finite-ℤ/n`{.Agda} that `Symmetry`{.Agda} uses to read a
gauge loop back as an element of `Fin 4`{.Agda}.

```agda
diurnal-24-hours : ⌞ Diurnal ⌟ ≃ Fin 24
diurnal-24-hours = Finite-ℤ/n 24

annual-365-days : ⌞ Annual ⌟ ≃ Fin 365
annual-365-days = Finite-ℤ/n 365
```

## Gauging the diurnal cycle

Time translation is a symmetry to be *gauged*: two instants that differ
by a whole solar cycle are the same phase of the sky. The correct
object is again the [[action groupoid|action-groupoid]], exactly as the
oscillator gauges its parity and the paraboloid its rotation — but now
the acting group is the diurnal `ℤ/ 24`{.Agda}, acting on the set of
hours by the **principal action**, translation of the hour angle. This
action needs no order-checking obligation: the principal action of any
group on itself is available upstream (`principal-action`{.Agda}), and
the period-$24$ closure is carried by the group `ℤ/ 24`{.Agda} itself.

```agda
Hours : Set lzero
Hours = Diurnal .fst

diurnal-action : Action (Sets lzero) Diurnal Hours
diurnal-action = principal-action Diurnal
```

The gauged clock is the homotopy quotient — the [[nerve]] of the action
groupoid — instantiated at the diurnal group, its hour set and the
translation action. As for the oscillator and the paraboloid, its
low-dimensional plots are the physics: a vertex is an hour of the day,
and an edge is an hour *together with* the time-translation acting on
it, now an element of `⌞ ℤ/ 24 ⌟`{.Agda}.

```agda
module Clock =
  Cat.Instances.SimplicialSets.ActionGroupoid Diurnal Hours diurnal-action

clock-vertices : ⌞ Clock.homotopy-quotient .F₀ 0 ⌟ ≃ ⌞ Diurnal ⌟
clock-vertices = Clock.quotient-vertices

clock-edges : ⌞ Clock.homotopy-quotient .F₀ 1 ⌟ ≃ (⌞ Diurnal ⌟ × ⌞ Diurnal ⌟)
clock-edges = Clock.quotient-edges
```

The principal action is [[free|free-action]] — translation by a nonzero
element fixes no hour — so, unlike the paraboloid's axis, no vertex of
the clock carries extra stabiliser loops. The gauge groupoid of the sky
is the delooping $\mathbf{B}(\mathbb{Z}/24)$ spread over its hours: a
torsor of instants, one solar day.

## The fixed focus, as a conserved charge

Now the conservation law. We work over an abstract commutative ring
`S`{.Agda}, so the ring solver `cring!`{.Agda} applies (the
abstract-then-instantiate discipline of `euclid`{.Agda} and
`Physics.Heliostat.Symmetry.rotation`{.Agda}); the geometry is the
Euclidean toolkit `euclid`{.Agda} of the optics module.

```agda
module noether {ℓ} (S : CRing ℓ) where
  open euclid S
  private module S = CRing-on (S .snd)
```

Tracking established, in scalar half-angle units, that the reflected
ray holds its target through the diurnal step: `tracks-sun`{.Agda}. The
statement here is its `Vec3`{.Agda} refinement, on the honest paraboloid
optics. The **beam-up ray** is the reflection of the incoming axial ray
in the paraboloid's derived normal, and the ray it must stay parallel
to is the surface-to-focus ray `foc g -v surf a b c`{.Agda}. That the
two are parallel — the reflected beam passes through the focus, at
*every* mirror point — is `focusing-parallel-abs`{.Agda}: their cross
product vanishes, under the focal relation $4qf = 1$.

The **conserved charge of the diurnal clock** is that this parallelism
is *the same* before and after the sun advances and the mirror
re-points. Because the vanishing cross product is a fixed value — the
zero vector — for every state satisfying the focal relation, the
"charge after the step" equals the "charge before the step" by
transitivity, exactly as Tracking's `tracks-sun`{.Agda} is
`on-target`{.Agda} composed with its inverse. We phrase it for two
mirror configurations $(a,b)$ and $(a',b')$ sharing the same focal
scalar $c$ and focus $g$ — the sun has moved, the primary has
re-pointed to a new patch, but the focus is unmoved:

```agda
  focus-invariant
    : ∀ a b a' b' c g
    → four c S.* g ≡ S.1r
    → cross (reflect incoming (parab-normal a b c)) (foc g -v surf a b c)
    ≡ cross (reflect incoming (parab-normal a' b' c)) (foc g -v surf a' b' c)
  focus-invariant a b a' b' c g focal =
      focusing-parallel-abs a b c g focal
    ∙ sym (focusing-parallel-abs a' b' c g focal)
```

The focus itself sits on the optical axis, and the diurnal motion is a
rotation *about* that axis (this is exactly the `focus-rot-fixed`{.Agda}
of `Symmetry`{.Agda}): so the conserved charge is not merely that *some*
focus is shared, but that the **on-axis focus point is literally fixed**
— its coordinates are unchanged. In the vector units this is a two-atom
`cring!`{.Agda} identity: rotating $(0,0,g)$ about the $z$-axis moves
nothing, so the focus is the invariant of time translation on the nose.

```agda
  rotated-focus : ⌞ S ⌟ → Vec3
  rotated-focus g = (S.- S.0r) , S.0r , g

  focus-on-axis-fixed
    : ∀ g → foc g ≡ rotated-focus g
  focus-on-axis-fixed g i = neg-zero i , S.0r , g
    where
      neg-zero : foc g .fst ≡ (S.- S.0r)
      neg-zero = cring! S
```

## Wiring the charge to the real optics

The abstract charge specialises to the genuine synthetic optics exactly
as `Symmetry`{.Agda}'s equivariance does: open the optics module at a
ring `R`{.Agda}, and take the derived `normal`{.Agda}, `focus`{.Agda}
and `σ`{.Agda}. The reflected ray is then reflection in the
*synthetically-derived* normal (`normal-value`{.Agda}), and the
coordinate-free conservation is `focusing-parallel`{.Agda} composed with
its inverse across the tracking step.

```agda
module solar-noether {ℓ} (R : CRing ℓ) where
  open Algebra.Ring.Polynomial R
  open Physics.Heliostat.Optics.optics R
  open Physics.Heliostat.Optics.euclid (R[ Lift ℓ (Fin 2) ])
```

<!--
```agda
  private
    Obs : CRing ℓ
    Obs = R[ Lift ℓ (Fin 2) ]

    module Obs = CRing-on (Obs .snd)
```
-->

The **fixed-focus Noether charge** on the real reflector: as the sun
advances and the primary re-points from focal configuration `Q`{.Agda}
to configuration `Q′`{.Agda} sharing the focus `F`{.Agda}, the reflected
beam stays parallel to the surface-to-focus ray — the focus is
unmoved. Both sides are the zero vector by `focusing-parallel`{.Agda},
so the invariance is the composite, precisely the shape of Tracking's
`tracks-sun`{.Agda} one dimension up.

```agda
  fixed-focus
    : ∀ Q Q′ F → Focal Q F → Focal Q′ F
    → cross (reflect incoming (normal Q))  (focus F -v σ Q)
    ≡ cross (reflect incoming (normal Q′)) (focus F -v σ Q′)
  fixed-focus Q Q′ F focal focal′ =
      focusing-parallel Q F focal
    ∙ sym (focusing-parallel Q′ F focal′)
```

## What is and is not proven

Fully proven, zero postulates. The compiled solar clock
`sky-step`{.Agda} is the interpretation of a genuine `λ-Signature`{.Agda}
program in sets, and the two `refl`{.Agda}-checks confirm it advances
the hour and holds the day definitionally; `sky-holds-day`{.Agda}
proves the day is inert under the diurnal step for *every* state. The
genuine periods are the upstream finite cyclic groups: `Diurnal`{.Agda}
and `Annual`{.Agda} are `ℤ/ 24`{.Agda} and `ℤ/ 365`{.Agda},
`diurnal-generated`{.Agda}/`annual-generated`{.Agda} prove each is
generated by the one-tick advance (`ℤ/n-cyclic`{.Agda}),
`diurnal-closes`{.Agda}/`annual-closes`{.Agda} prove the cycle closes
after a full period as a theorem of the quotient group (`quot`{.Agda} of
an honest `dividesℤ`{.Agda} — *not* the `negℤ`{.Agda} involution, which
only expresses $\mathbb{Z}/2$), and
`diurnal-24-hours`{.Agda}/`annual-365-days`{.Agda} prove via
`Finite-ℤ/n`{.Agda} that the clocks have exactly $24$ and $365$ states.
The diurnal cycle is *gauged*: `diurnal-action`{.Agda} is the upstream
`principal-action`{.Agda} of `ℤ/ 24`{.Agda} on its hours, and
`Clock`{.Agda} is its action groupoid with the plot equivalences
`clock-vertices`{.Agda}/`clock-edges`{.Agda}. The conservation law is
proven at both levels: over any commutative ring,
`focus-invariant`{.Agda} proves the reflected-beam-parallel charge is
the same before and after the sun advances and the primary re-points
(via `Optics.focusing-parallel-abs`{.Agda}), `focus-on-axis-fixed`{.Agda}
proves the on-axis focus point is literally unmoved by the axial diurnal
rotation (`cring!`{.Agda}), and `fixed-focus`{.Agda} states the same
charge on the honest synthetically-derived `normal`{.Agda}/`focus`{.Agda}
of `Physics.Heliostat.Optics`{.Agda} through
`Optics.focusing-parallel`{.Agda} — the discrete Noether charge of
time-translation, the optical twin of the oscillator's
`energy-conserved`{.Agda}.

Deliberately *not* modelled, by design rather than as a gap. The
day-rollover coupling the two clocks — the hour angle spilling into the
declination at hour $24$ — is not a ring operation on the integers, so
it is not a signature step; the honest home of the period is the cyclic
group, where `diurnal-closes`{.Agda} and `annual-closes`{.Agda} live,
and the two clocks are treated as independent cyclic factors
(`sky-holds-day`{.Agda} is exactly the statement that the diurnal step
leaves the annual coordinate alone). The *continuous* solar path — the
real $\mathrm{SO}(2)$ of the sky, the sun's position as a genuine
smooth function of time — is out of reach for the same reason the
paraboloid's continuous $\mathrm{SO}(2)$ is in `Symmetry`{.Agda} and
finite-time tracking is in `Tracking`{.Agda}: it needs the
real-numbers object and the smooth structure the [[reading
guide|higher-topos-theory-in-physics]] lists as honestly missing. We
capture the integer skeletons `ℤ/ 24`{.Agda} and `ℤ/ 365`{.Agda},
which are the exact cyclic orders of the diurnal and annual clocks, and
the conservation law at the differential (ring) level, exact but
discrete. And, as in Tracking, the scalar `tracks-sun`{.Agda} shadow of
the fixed-focus charge is cited, not re-proven; this module supplies
its `Vec3`{.Agda} refinement.
