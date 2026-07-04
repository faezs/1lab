<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sets.Closed
open import Cat.Prelude

open import Cat.CartesianClosed.Free.Signature

open import Data.Int

import Cat.CartesianClosed.Free.Model

open λ-Signature
open Precategory
open Functor
```
-->

```agda
module Physics.Heliostat.Tracking where
```

# Sun-tracking as a compiled program {defines="heliostat-tracking"}

The [[reading guide|higher-topos-theory-in-physics]] compiles a toy
[[heliostat|heliostat-tracking]] — a mirror that *aims* — and the
[[harmonic oscillator|harmonic-oscillator]] compiles a system that
*moves*. This module fuses the two into the device the name promises:
a [[heliostat]] that **tracks**. The sun advances across the sky by the
oscillator's exact integer motion, and at every instant an aiming law
re-points the mirror so that the reflected ray stays locked on a fixed
target. Both the motion and the aiming are a single [[λ-signature]]
program, so — one syntax, all semantics — the identical tracking law
runs in every [[cartesian closed category]], and on the integers it
closes its diurnal cycle *by `refl`{.Agda}*.

## Units and conventions

We measure the sun's direction by a single scalar coordinate, of one
base type `dir`, and work in the linearized half-angle units of the
toy heliostat, where the reflection law that makes the mirror bisect
the sun and target directions is exactly *addition*: the reflected ray
is `mirror + sun`, and holding it on a target `t` means the mirror
must be set to `t − sun`. The diurnal advance is the oscillator's
exact restoring `kick`{.Agda} `s ↦ −s` — the sign-flipping half of its
symplectic quarter-turn, an exact $\mathbb{Z}/2$ motion needing no
reals. The full vector reflection law — the mirror normal as a genuine
bisector of two direction *vectors* — is not a signature operation
here: it is abstract-ring cross-product algebra, and it already lives,
*derived* rather than posited, in `Physics.Heliostat.Optics`{.Agda}.
Forcing it into this signature would be padding, so we keep it out and
track the scalar.

## The signature: one base type, two operations

One base type `dir`; two operations. `sun-step`{.Agda} advances the
sun by one diurnal tick, and `track`{.Agda} is the aiming law that,
given the current sun coordinate and the fixed target, returns the
mirror setting `target − sun`. Each operation's argument is written as
a product-formed [[type|λ-signature]] over the base types, and — as the
signature interface demands — each returns a single base type.

```agda
data Track-type : Type where
  dir : Track-type

data Track-op : types.Ty Track-type → Track-type → Type where
  sun-step : Track-op (` dir)            dir
  track    : Track-op (` dir `× ` dir)   dir
```

<!--
```agda
private
  Track-type-is-set : is-set Track-type
  Track-type-is-set = is-prop→is-set λ where dir dir → refl

  Track-op-is-prop : ∀ {τ b} → is-prop (Track-op τ b)
  Track-op-is-prop sun-step sun-step = refl
  Track-op-is-prop track    track    = refl
```
-->

```agda
Tracker : λ-Signature lzero
Tracker .Ob = Track-type
Tracker .Ob-is-set = Track-type-is-set
Tracker .Hom = Track-op
Tracker .Hom-is-set = is-prop→is-set Track-op-is-prop
```

<!--
```agda
open import Cat.CartesianClosed.Free Tracker
open import Cat.CartesianClosed.Free.Lambda Tracker
```
-->

## The tracking law as a λ-term

The controller is a *program* — a term of the [[simply-typed lambda
calculus|STLC]] over this signature — and therefore makes sense in
every [[cartesian closed category]] at once. Its context holds the
pair `(current sun coordinate , fixed target)`; it emits the pair
`(advanced sun , mirror setting)`. The mirror is set from the sun *and*
the target by the aiming law, while the sun is advanced by one tick, so
that one application is one diurnal step of the coupled system.

```agda
track-program : Expr (∅ , ` dir `× ` dir) (` dir `× ` dir)
track-program =
  `⟨ `hom sun-step (`π₁ (`var stop))
   , `hom track    (`var stop) ⟩
```

## Running it in sets

To *simulate*, interpret the signature in the topos of sets: the
direction base type becomes the integers, `sun-step`{.Agda} becomes
negation, and `track`{.Agda} becomes subtraction — target minus sun.

```agda
private
  module SetsModel = Cat.CartesianClosed.Free.Model Tracker
    (Sets-cartesian {ℓ = lzero}) Sets-closed

tracker-interp
  : elim.base-method
      SetsModel.chaotic-cartesian SetsModel.chaotic-closed
      (λ _ → el! Int)
tracker-interp sun-step = λ s       → negℤ s
tracker-interp track    = λ (s , t) → t +ℤ negℤ s

private
  module Run = SetsModel.model (λ _ → el! Int) tracker-interp

step : Int × Int → Int × Int
step s = Run.compile .F₁ ⟦ track-program ⟧ᵉ (lift tt , s)
```

The compiled controller is an honest function, and it *computes*: with
the sun at coordinate $2$ and the target fixed at $5$, one diurnal step
advances the sun to $-2$ and sets the mirror to $5 - 2 = 3$ — and this
is so definitionally, by `refl`{.Agda}.

```agda
_ : step (2 , 5) ≡ (-2 , 3)
_ = refl

_ : step (-2 , 5) ≡ (2 , 7)
_ = refl
```

## The reflected ray stays on target

The point of a heliostat is not the mirror setting but the *reflected
ray* — `mirror + sun`, in our additive units. When the mirror tracks
the target, this ray is `(t − s) + s`, and the tracking is correct
exactly when that equals `t`. This holds not for a sampled sun position
but for *every* state, as a theorem of integer ring algebra — the
`period-four`{.Agda}/`energy-conserved`{.Agda} analogue.

```agda
reflect : Int → Int → Int
reflect s t = (t +ℤ negℤ s) +ℤ s

on-target : ∀ s t → reflect s t ≡ t
on-target s t =
    sym (+ℤ-assoc t (negℤ s) s)
  ∙ ap (t +ℤ_) (+ℤ-invl s)
  ∙ +ℤ-zeror t
```

And because the aiming law is re-applied at each tick, the target is
held fixed *through* the diurnal motion: re-tracking the advanced sun
`−s` hits the same target as tracking the original sun `s`. Sun-tracking
is the invariance of the reflected ray under discrete time translation —
a discrete Noether statement for the diurnal cycle, the exact analogue
of the oscillator's `period-four`{.Agda}.

```agda
tracks-sun : ∀ s t → reflect (negℤ s) t ≡ reflect s t
tracks-sun s t = on-target (negℤ s) t ∙ sym (on-target s t)
```

The diurnal cycle also closes on the nose: two ticks of `sun-step`{.Agda}
return the sun to where it started, since negation is an involution.
So — target held fixed, sky returning to its start — the tracking
mirror runs a closed daily loop, all of it a theorem rather than a
numerical coincidence.

```agda
diurnal-cycle : ∀ s → negℤ (negℤ s) ≡ s
diurnal-cycle = negℤ-negℤ
```

## One syntax, all semantics

Because `track-program`{.Agda} is a plain λ-term over the signature,
the identical tracking law runs in **every** cartesian closed category.
Swapping `Sets-cartesian`{.Agda}/`Sets-closed`{.Agda} for
`Sh[]-cartesian`{.Agda}/`Sh[]-closed`{.Agda} on any [[sites|site]] compiles
the *same* program into a gros topos of generalized smooth spaces,
where the base type may be a sheaf of smoothly-varying directions and
the [[mapping space|higher-topos-theory-in-physics]] supplies the
configuration space of a *field* of tracking heliostats. The reading
guide's `heliostat-in-sheaves`{.Agda} already exhibits this sheaf
compilation for the aiming half; the tracking program factors through
the identical machinery, so we cite it rather than rebuild it.

## What is and is not proven

Fully proven, zero postulates: the signature is a genuine
`λ-Signature`{.Agda} (its operation family is a proposition, so its
hom-sets are sets); `track-program`{.Agda} is a well-typed λ-term;
its Sets-interpretation `step`{.Agda} is the compiled functor applied
to the term, and the two `refl`{.Agda}-checks confirm it computes on
concrete integers definitionally. `on-target`{.Agda} proves the
reflected ray equals the target for *every* sun position and target,
`tracks-sun`{.Agda} proves this invariance survives the diurnal motion,
and `diurnal-cycle`{.Agda} proves the sky's motion closes after two
ticks — all three universal, all three by `Data.Int`{.Agda} ring
lemmas (`+ℤ-assoc`{.Agda}, `+ℤ-invl`{.Agda}, `+ℤ-zeror`{.Agda},
`negℤ-negℤ`{.Agda}), never sampled.

Deliberately *not* modelled here — and this is a design choice, not a
gap: the vector reflection law (the mirror normal as the bisector of
two direction *vectors*) is left as abstract-ring cross-product
algebra, where it belongs; it is *derived*, not posited, in
`Physics.Heliostat.Optics`{.Agda}, and packing it into a signature
operation would be padding. The diurnal motion is the exact
$\mathbb{Z}/2$ shadow of the oscillator's quarter-turn, kept scalar to
meet the one-base-type / two-operation budget; the full symplectic
$\mathbb{Z}/4$ orbit lives in `Physics.Oscillator`{.Agda}. And, as
everywhere in this development, *finite-time* continuous tracking —
integrating the diurnal advance from an infinitesimal generator —
waits on a real-numbers object and the analytic ingredients the
reading guide lists as honestly missing.
