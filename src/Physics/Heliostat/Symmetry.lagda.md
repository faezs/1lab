<!--
```agda
open import Cat.Prelude

open import Algebra.Ring.Solver

open import Algebra.Group.Instances.Cyclic
open import Algebra.Group.Cat.Base
open import Algebra.Group.Action
open import Algebra.Ring.Commutative
open import Algebra.Group
open import Algebra.Ring

open import Data.Fin using (Fin ; fzero ; fsuc ; fin ; lower)
open import Data.Int.DivMod using (_%ℤ_ ; Fin-%ℤ)
open import Data.Int
open import Data.Nat using (zero≠suc)

open import Physics.Heliostat.Optics

import Algebra.Ring.Polynomial
import Cat.Instances.SimplicialSets.ActionGroupoid
import Cat.Reasoning

open Precategory
open Functor
```
-->

```agda
module Physics.Heliostat.Symmetry where
```

# The paraboloid's axial symmetry, gauged {defines="paraboloid-rotation-symmetry heliostat-gauge"}

The paraboloid of `Physics.Heliostat.Optics`{.Agda} is a surface of
revolution: rotating the mirror about its optical axis is a symmetry.
The *continuous* rotation group $\rm{SO}(2)$ is out of reach here — it
needs the real-numbers object the 1Lab does not yet have — but its
integer skeleton is not. The quarter-turn $(u,v) \mapsto (-v,u)$ is an
**exact** symmetry, defined over any commutative ring, and iterating it
four times is the identity: it generates a copy of $\ZZ/4$ acting on
the reflector. This module gauges that $\ZZ/4$ exactly as the
[[harmonic oscillator|harmonic-oscillator]]'s
`Physics.Oscillator`{.Agda} gauges its parity, reusing the same
[[action groupoid|action-groupoid]] machinery — but with the *upstream*
[[cyclic group|cyclic-group]] `ℤ/ 4`{.Agda} in place of a hand-rolled
finite group, so that generation-by-one and the mapping-out property
`ℤ/-out`{.Agda} come for free.

Two things must be shown, and they live at two different levels. First,
the rotation is a genuine symmetry of the *optics* — the mirror
surface, its sag, its synthetically-derived normal and its focus all
transform correctly — and this is a family of exact ring identities
over an abstract scalar ring, discharged by the solver `cring!`{.Agda}
exactly as the focusing theorem is. Second, the rotation is a *gauge*
symmetry to be quotiented, and this lives at the level of sets: the
homotopy quotient of the configuration space by $\ZZ/4$, whose vertex
over the axis remembers the four distinct rotation loops that the naive
quotient set forgets — the orbi-singularity $\rm{pt}/\!\!/(\ZZ/4)$.

## The quarter-turn and its optical equivariance

We work first over an abstract commutative ring `S`{.Agda}, reusing the
Euclidean toolkit `euclid`{.Agda} of the optics module. The quarter-turn
acts on the mirror coordinates by $(a,b) \mapsto (-b,a)$, and on a full
space vector by the corresponding rotation about the $z$-axis $(x,y,z)
\mapsto (-y,x,z)$; the axis $z$ is fixed, which is exactly why the focus
survives.

```agda
module rotation {ℓ} (S : CRing ℓ) where
  open euclid S
  private module S = CRing-on (S .snd)

  rot-z : Vec3 → Vec3
  rot-z (x , y , z) = (S.- y) , x , z
```

The **sag** — the height $c(a^2+b^2)$ of the paraboloid over a mirror
point — is a rotation *invariant*: substituting $(a,b) \mapsto (-b,a)$
gives $c((-b)^2 + a^2) = c(a^2+b^2)$, a two-atom `cring!`{.Agda}
identity. This is the analogue of the oscillator's
`parity-preserves-energy`{.Agda}: the datum the dynamics depends on is
untouched by the symmetry, which is what licenses gauging it.

```agda
  sag-rot-invariant
    : ∀ a b c → surf (S.- b) a c .snd .snd ≡ surf a b c .snd .snd
  sag-rot-invariant a b c = cring! S
```

The **surface itself is rotation-equivariant**: rotating the mirror
coordinates and then forming the surface point agrees with forming the
surface point and then rotating it about the axis. The first two
components are the definition of `rot-z`{.Agda} up to sign bookkeeping,
and the third is the sag invariance above; all three are `cring!`{.Agda}.

```agda
  surf-rot-equivariant
    : ∀ a b c → surf (S.- b) a c ≡ rot-z (surf a b c)
  surf-rot-equivariant a b c = ap₂ _,_ eq-x (ap₂ _,_ eq-y eq-z) where
    eq-x : surf (S.- b) a c .fst ≡ rot-z (surf a b c) .fst
    eq-x = cring! S
    eq-y : surf (S.- b) a c .snd .fst ≡ rot-z (surf a b c) .snd .fst
    eq-y = cring! S
    eq-z : surf (S.- b) a c .snd .snd ≡ rot-z (surf a b c) .snd .snd
    eq-z = cring! S
```

The **derived normal is rotation-equivariant** in the same way. Because
the normal was obtained as a synthetic cross product of tangent vectors
(not posited), its equivariance is a statement about the closed-form
`parab-normal`{.Agda} $(-2ca, -2cb, 1)$, and it too is componentwise
`cring!`{.Agda}: rotating the base point rotates the normal about the
axis.

```agda
  normal-rot-equivariant
    : ∀ a b c → parab-normal (S.- b) a c ≡ rot-z (parab-normal a b c)
  normal-rot-equivariant a b c = ap₂ _,_ eq-x (ap₂ _,_ eq-y eq-z) where
    eq-x : parab-normal (S.- b) a c .fst ≡ rot-z (parab-normal a b c) .fst
    eq-x = cring! S
    eq-y : parab-normal (S.- b) a c .snd .fst ≡ rot-z (parab-normal a b c) .snd .fst
    eq-y = cring! S
    eq-z : parab-normal (S.- b) a c .snd .snd ≡ rot-z (parab-normal a b c) .snd .snd
    eq-z = cring! S
```

Finally the **on-axis focus is a fixed point**: $F = (0,0,g)$ lies on
the rotation axis, so rotating it does nothing. This is the reason the
paraboloid focuses to the *same* point under any rotation — the whole
point of an axial reflector.

```agda
  focus-rot-fixed : ∀ g → rot-z (foc g) ≡ foc g
  focus-rot-fixed g = ap₂ _,_ neg-zero refl where
    neg-zero : rot-z (foc g) .fst ≡ foc g .fst
    neg-zero = cring! S
```

## Wiring the equivariance to the real optics

The identities above are stated over abstract atoms; the real mirror
observables are their instances at the polynomial ring, with the mirror
coordinates `û`{.Agda} and `v̂`{.Agda} as atoms $a,b$ and the focal
scalar `con Q`{.Agda} as $c$. So the equivariance of the *actual*
optics objects — `σ`{.Agda}, `normal`{.Agda}, `focus`{.Agda} of
`Physics.Heliostat.Optics.optics`{.Agda} — is obtained by opening the
optics module at a ring `R`{.Agda}, opening `rotation`{.Agda} at the
observable ring, and specialising. The surface is
`σ Q = surf û v̂ (con Q)`{.Agda} definitionally, and the derived normal
agrees with the closed form by `normal-value`{.Agda}, so the abstract
statements transport directly.

To keep a single `euclid`{.Agda} in scope — and so avoid an ambiguous
`surf`{.Agda} — we take the vector toolkit `surf`{.Agda}, `foc`{.Agda},
`parab-normal`{.Agda} from the optics re-export, and the *rotation*
names from the `rotation`{.Agda} module qualified as `Rot`{.Agda}. The
observable ring is the same `R[ \mathrm{Lift}\,(\mathrm{Fin}\,2)]`
either way.

```agda
module optics-symmetry {ℓ} (R : CRing ℓ) where
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
    module Rot = rotation Obs
```
-->

The mirror surface, rotated in its coordinates, is the surface rotated
about the axis:

```agda
  σ-rot-equivariant
    : ∀ Q → surf (Obs.- v̂) û (con Q) ≡ Rot.rot-z (σ Q)
  σ-rot-equivariant Q = Rot.surf-rot-equivariant û v̂ (con Q)
```

The synthetic normal is rotation-equivariant, connecting through the
`normal-value`{.Agda} identification of the cross-product normal with
its closed form on both sides:

```agda
  normal-rot-equivariant′
    : ∀ Q → parab-normal (Obs.- v̂) û (con Q) ≡ Rot.rot-z (normal Q)
  normal-rot-equivariant′ Q =
      Rot.normal-rot-equivariant û v̂ (con Q)
    ∙ ap Rot.rot-z (sym (normal-value Q))
```

And the focus is fixed by the rotation, being on-axis:

```agda
  focus-rot-fixed′ : ∀ F → Rot.rot-z (focus F) ≡ focus F
  focus-rot-fixed′ F = Rot.focus-rot-fixed (con F)
```

## The gauge group and its action

Gauging is a set-level operation, so — exactly as the oscillator uses
`Int`{.Agda} for its `Phase`{.Agda} rather than an abstract ring — we now
descend to the integers. A configuration of the reflector is a pair of
integer mirror coordinates, and the quarter-turn acts on them by the
same $(u,v) \mapsto (-v,u)$, now with concrete `negℤ`{.Agda}.

```agda
Config : Set lzero
Config = el! (Int × Int)

rot90 : Int × Int → Int × Int
rot90 (u , v) = negℤ v , u
```

Iterating the quarter-turn four times is the identity — the same
$\ZZ/4$ closure that the oscillator's `period-four`{.Agda} exhibits for
its symplectic time-step — and here it is a two-line `negℤ-negℤ`
computation, one negation cancelling per coordinate.

```agda
rot90⁴ : ∀ s → rot90 (rot90 (rot90 (rot90 s))) ≡ s
rot90⁴ (u , v) i = negℤ-negℤ u i , negℤ-negℤ v i
```

<!--
```agda
private
  module Sl = Cat.Reasoning (Sets lzero)

  rot90³ : Int × Int → Int × Int
  rot90³ (u , v) = v , negℤ u

  rot90-rot90³ : ∀ s → rot90 (rot90³ s) ≡ s
  rot90-rot90³ (u , v) i = negℤ-negℤ u i , v

  rot90³-rot90 : ∀ s → rot90³ (rot90 s) ≡ s
  rot90³-rot90 (u , v) i = u , negℤ-negℤ v i

  rot90-iso : Config Sl.≅ Config
  rot90-iso = Sl.make-iso rot90 rot90³
    (funext rot90-rot90³) (funext rot90³-rot90)
```
-->

To build the action we use the upstream mapping-out property
`ℤ/-out`{.Agda}: a homomorphism $\ZZ/4 \to \rm{Aut}(\mathtt{Config})$
is exactly an automorphism of `Config`{.Agda} whose fourth power is the
identity. Our generator is the iso `rot90-iso`{.Agda}, and its
order-four `wraps` obligation is `rot90⁴`{.Agda}, read as an equality of
isos through `Sl.≅-path`{.Agda} — the same iso-equality reasoning the
oscillator uses for its `parity-action`{.Agda}. Precomposing with the
lift `G→LiftG`{.Agda}, exactly as the library's `ℤ/2→S₂`{.Agda} does,
lands the homomorphism in the same universe.

```agda
rot-action : Action (Sets lzero) (ℤ/ 4) Config
rot-action =
  ℤ/-out 4 rot90-iso (Sl.≅-path (funext rot90⁴)) Groups.∘ G→LiftG (ℤ/ 4)
```

## The gauged reflector

The gauged configuration space is the homotopy quotient — the [[nerve]]
of the action groupoid — instantiated at `ℤ/ 4`{.Agda}, `Config`{.Agda}
and the action just built. As for the oscillator, its low-dimensional
plots are exactly the physics: a vertex is a mirror configuration, and
an edge is a configuration *together with* the rotation acting on it —
now an element of `⌞ ℤ/ 4 ⌟`{.Agda} rather than a bit.

```agda
module Gauged =
  Cat.Instances.SimplicialSets.ActionGroupoid (ℤ/ 4) Config rot-action

quotient-vertices : ⌞ Gauged.homotopy-quotient .F₀ 0 ⌟ ≃ (Int × Int)
quotient-vertices = Gauged.quotient-vertices

quotient-edges
  : ⌞ Gauged.homotopy-quotient .F₀ 1 ⌟ ≃ ((Int × Int) × ⌞ ℤ/ 4 ⌟)
quotient-edges = Gauged.quotient-edges
```

## The orbi-singularity over the axis

The payoff is the vertex over the optical axis. The point $(0,0)$ is
fixed by *every* rotation — `rot90 (0,0) = (negℤ 0 , 0) = (0,0)`
definitionally — so its stabiliser is the whole of $\ZZ/4$. In the
homotopy quotient this means there are **four** genuinely distinct gauge
loops at that vertex, one for each rotation, where the quotient *set*
would have collapsed them to a single point. This is the paraboloid's
axial orbi-singularity $\rm{pt}/\!\!/(\ZZ/4)$, in its smallest instance:
invisible to sets, seen by the groupoid.

```agda
vertex : Int × Int
vertex = 0 , 0

loop₀ loop₁ loop₂ loop₃ : Gauged.Action-groupoid .Hom vertex vertex
loop₀ = inc (pos 0) , refl
loop₁ = inc (pos 1) , refl
loop₂ = inc (pos 2) , refl
loop₃ = inc (pos 3) , refl
```

The four loops share a source and target but differ in their group
component. As in the oscillator's `gauge-loops-differ`{.Agda}, we
separate them by `ap fst`; but the components now live in `⌞ ℤ/ 4 ⌟`,
not `Bool`, so we push them through the finiteness equivalence
`Finite-ℤ/n 4 : ⌞ ℤ/ 4 ⌟ ≃ Fin 4`{.Agda} — which sends `inc (pos i)`
to `i`{.Agda} — and separate the resulting `Fin 4`{.Agda} elements,
which are discrete. We show the quarter-turn loop differs from the
identity loop; the other pairs are identical.

```agda
gauge-loops-differ : ¬ loop₁ ≡ loop₀
gauge-loops-differ e = zero≠suc (sym one≡zero)
  where
    tofin : ⌞ ℤ/ 4 ⌟ → Fin 4
    tofin = Equiv.to (Finite-ℤ/n 4)

    lowers : (pos 1 %ℤ 4) ≡ (pos 0 %ℤ 4)
    lowers = ap (λ h → tofin (h .fst) .lower) e

    one≡zero : 1 ≡ 0
    one≡zero = sym (Fin-%ℤ {4} (fin 1)) ∙ lowers ∙ Fin-%ℤ {4} (fin 0)
```

## What is and is not proven

What is proven is the *discrete* axial symmetry, at both levels it lives
at. Over any commutative ring, the quarter-turn is an exact symmetry of
the paraboloid's optics: the sag is invariant, the surface and its
synthetically-derived normal are equivariant (rotating the mirror
coordinates rotates the space vector about the axis), and the on-axis
focus is a fixed point — all closed by the ring solver or `refl`, with
the normal's equivariance routed through the *derived* value
`normal-value`{.Agda} so that it is a statement about the honest
cross-product normal, not a posited one. At the set level, the
quarter-turn generates a genuine `ℤ/ 4`{.Agda} — the *upstream* cyclic
group, reused through its mapping-out property `ℤ/-out`{.Agda} rather
than reinvented — acting on integer mirror configurations, and its
homotopy quotient is the action groupoid whose vertex over the axis
carries four distinct stabiliser loops (`gauge-loops-differ`{.Agda}
separates two of them; the argument is the same for every pair), the
orbi-singularity $\mathrm{pt}/\!\!/(\ZZ/4)$ that the naive quotient set
collapses.

What is **not** proven is anything continuous. The full rotation group
$\rm{SO}(2)$ — the paraboloid's *actual* symmetry group — is not
constructed, because it needs the real-numbers object and the smooth
structure the 1Lab does not yet have (the same wall the optics module
and the oscillator hit); we capture only its integer skeleton $\ZZ/4$,
which is the largest cyclic subgroup that acts by *integer* coordinate
maps. Consequently we do not prove the focusing identity is invariant
under the gauge action as a single equivariant statement over the reals:
the equivariance lemmas here are the ring-level shadows of that
statement, exact but discrete. The Kan-complex structure of the homotopy
quotient, and its identification with a quotient *stack* over a
geometric site, are the same future work flagged in
`Cat.Instances.SimplicialSets.ActionGroupoid`{.Agda} — inherited here
unchanged.
