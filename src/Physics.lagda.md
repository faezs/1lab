---
description: |
  A reading guide to Urs Schreiber's "Higher Topos Theory in Physics",
  mapping its diagrams to their constructive formalisations, with a
  worked example of compiling a physical system to any topos.
---
<!--
```agda
open import Cat.CartesianClosed.Functor
open import Cat.Instances.Sets.Closed
open import Cat.Instances.SimplicialSets.Nerve
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Sheaf.Limits.Finite
open import Cat.Instances.Sets.Complete
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Localisation.Invertible
open import Cat.Instances.Localisation
open import Cat.Instances.Sheaves
open import Cat.Instances.Simplex
open import Cat.Diagram.Exponential
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Hom
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Cartesian
open import Cat.Prelude

open import Cat.CartesianClosed.Free.Signature

open import Data.Set.Projective
open import Data.Set.Surjection
open import Data.Int.Base using (Int ; _+ℤ_)
open import Data.Bool

open import Homotopy.Space.Delooping
open import Homotopy.Spectrum

open import Algebra.ChainComplex

open import Topoi.Base

import Algebra.ChainComplex.Moore
import Algebra.Ring.Grassmann
import Algebra.Ring.Center
import Cat.CartesianClosed.Free.Model
import Cat.Instances.NegativeSpheres
import Cat.Instances.Singular
import Algebra.ChainComplex.DoldKan
import Cat.Site.Sheafification.Lex
import Cat.Site.Sheafification.Locality
import Cat.Site.Sheafification.Plus
import Cat.Site.Sheafification.Glue
import Cat.Site.Sheafification.Kernel
import Cat.Site.Sheafification.Topos
import Physics.Oscillator
import Physics.Maxwell
import Physics.Newton
import Physics.Heliostat.Optics
import Physics.Heliostat.Eikonal
import Physics.Heliostat.Sheaf
import Physics.Heliostat.Forms
import Physics.Heliostat.Curvature
import Physics.Heliostat.Tracking
import Physics.Heliostat.Symmetry
import Physics.Heliostat.Bundle
import Physics.Heliostat.Thermal
import Physics.Heliostat.Solar
import Physics.SmoothWorld
import Physics.SmoothWorld.Internal
import Algebra.Ring.Kahler.Exterior
import Algebra.Ring.Weil
import Homotopy.Modality
import Data.Real.Arithmetic
import Data.Real.Order
import Data.Real.Base
import Cat.Instances.SimplicialPresheaves.Cech
import Cat.Instances.SimplicialSets.ActionGroupoid
import Cat.Instances.SuperSmoothSets
import Cat.Instances.FormalSmoothSets.DeRham
import Cat.Instances.Presheaf.Germs
import Cat.Instances.SimplicialPresheaves
import Cat.Site.Instances.Trivial
import Algebra.Ring.DualNumbers
import Algebra.Ring.Polynomial
import Cat.Instances.FormalSmoothSets
import Cat.Instances.Presheaf.Cohesive
import Cat.Instances.Presheaf.Concrete
import Cat.Instances.FormalSets
import Cat.Morphism

open λ-Signature
open Functor
```
-->

```agda
module Physics where
```

# Higher topos theory in physics {defines="higher-topos-theory-in-physics"}

This page maps the numbered diagrams and constructions of Urs
Schreiber's encyclopedia survey *Higher Topos Theory in Physics*
[@Schreiber:HTTPhysics] to their formalisations in the 1Lab. Two
warnings are in order. First, the 1Lab is resolutely *constructive*:
where the paper works over the site of smooth Cartesian spaces
$\bR^n$ — whose classical theory of smooth functions is not available
to us — we work over an *arbitrary* site, which is exactly the level
of generality at which the paper's topos-theoretic arguments live.
Second, the higher part of the story ($\infty$-topoi proper) remains
largely future work; the final section collects what is missing.

## Probes, plots and gluing

The starting point of the paper (its diagram (1)) is that physical
spaces are known by how we may *probe* them: maps compose, and
composition is associative and unital. This is the definition of a
[[precategory]]. A space $X$ probe-able by the objects of a category
$\cC$ of "shapes" assigns to each shape $U$ a set
$\rm{Plt}(U, X)$ of plots, contravariantly functorially — the paper's
boxed condition (1.), *precomposition of plots*, says exactly that
$\rm{Plt}(-, X)$ is a presheaf. Boxed condition (3.),
*postcomposition*, says that maps of such spaces are [[natural
transformations]].

```agda
_ = Precategory
_ = Functor
_ = _=>_
```

Boxed condition (2.), *gluing of plots*, is the sheaf condition for a
[[coverage]] on the category of shapes: a family of plots on the
patches of a cover, compatible on overlaps, glues to a unique global
plot. In the 1Lab this is the theory of [[sites|site]]: a
`Coverage`{.Agda} equips $\cC$ with covering sieves, a
`Patch`{.Agda} is a compatible family, a `Section`{.Agda} is a
gluing, and `is-sheaf`{.Agda} says every patch over every covering
sieve has a contractible space of sections.

```agda
_ = Coverage
_ = Patch
_ = Cat.Site.Base.Section
_ = is-sheaf
```

## The gros topos of generalized spaces

The paper's (2) defines the category of smooth sets as sheaves inside
presheaves, $\rm{SmthSet} := \rm{Sh}(\rm{CrtSp}) \mono
\rm{PSh}(\rm{CrtSp})$, and (8) recalls that such categories of
sheaves on a site are exactly the **Grothendieck topoi**. Both layers
exist here, over any site: the category `Sh[ C , J ]`{.Agda
ident=Sh[_,_]} of sheaves, the fully faithful inclusion into
presheaves, and its left exact left adjoint, [[sheafification]]. The
notion of [[topos]] as a lex-reflective subcategory of presheaves,
together with geometric morphisms `Geom[_,_]`{.Agda}, is in
`Topoi.Base`{.Agda}.

```agda
_ = Sh[_,_]
_ = forget-sheaf
_ = Sheafification⊣ι
_ = Topos
_ = Geom[_,_]
```

The embedding (3) of the site itself into its topos of spaces, and
the resulting tautology (4) — maps out of a representable are plots,
$\hom(\bR^n, X) \simeq \rm{Plt}(\bR^n, X)$ — are the [[Yoneda
embedding]] and the [[Yoneda lemma]].

```agda
_ = よ
_ = よ-is-fully-faithful
_ = yo
_ = yo-is-equiv
```

The paper's (5) and (6) — *germs* of plots, and the restriction of
maps to germs — hold over any category of probes equipped with
directed families of [[neighbourhood
inclusions|neighbourhood-structure]]: germs are a set-quotient of
plots, and maps of presheaves descend. The paper's (7) presents the
sheaf topos as the *localisation* of the presheaf topos at the
[[local isomorphisms|local-isomorphism]]. For the sites this
development actually builds — where the coverage is
[[trivial|trivial-coverage]] — this is a *theorem*: every presheaf is
a sheaf, germs along discrete neighbourhoods are plots, local
isomorphisms are invertible, and [[localising at
isomorphisms|localisation-at-isomorphisms]] is inessential, so
$\rm{Sh} = \rm{PSh} \simeq L^{\rm{liso}}\rm{PSh}$ on the nose.
What remains of (7) is precisely its analytic content: shrinking open
neighbourhoods over the good-open-cover coverage of the smooth site.

```agda
_ = Localisation
_ = Cat.Instances.Presheaf.Germs.Germs
_ = Cat.Instances.Presheaf.Germs.germs-map
_ = Cat.Instances.Presheaf.Germs.is-local-iso
_ = Cat.Site.Instances.Trivial.trivial-is-sheaf
_ = Cat.Site.Instances.Trivial.forget-trivial-is-precat-iso
_ = Localise-is-precat-iso
_ = Cat.Instances.Presheaf.Germs.Localise-discrete-is-precat-iso
```

## Fields and mapping spaces

Diagram (9) reads a field configuration as a map $\Phi : X \to F$
from spacetime to a space of field values — simply a morphism in the
topos. Diagram (10) is the heart of variational physics: the space
of *all* field configurations exists as a smooth set, the
**mapping space** $\rm{Maps}(X, F)$, characterised by the
[[exponential|exponential object]] adjunction: plots $U \to
\rm{Maps}(X, F)$ are maps $U \times X \to F$. Constructively and in
full generality: [[Sets is cartesian closed|sets-is-cartesian-closed]],
presheaf categories are [[cartesian closed]], and sheaf topoi are an
exponential ideal inside them.

```agda
_ = Sets-closed
_ = PSh-closed
_ = Sh[]-closed
_ = product⊣exponential
```

## Choice, constructively

The section-of-an-epimorphism diagram in the paper illustrates how
topos-internal logic differs from classical logic: the axiom of
choice — every epi $E \epi B$ has a section $\sigma$ — fails for
smooth sets ($\bR \epi \bR/\bZ$ has no continuous section). In the
1Lab even the base topos of sets is choice-free, so the phenomenon
is visible one level earlier: epimorphisms of sets are precisely the
[[surjections]], and the sets all of whose surjections split are the
[[projective|set-projective]] ones — assuming *every* set is
projective is exactly assuming the axiom of choice, which we neither
assume nor refute.

```agda
_ = Cat.Morphism.is-epic
_ = Cat.Morphism.has-section
_ = epi→surjective
_ = surjective→regular-epi
_ = is-set-projective
_ = set-surjections-split
```

## What makes a topos *gros*: cohesion, concreteness, infinitesimals

The topos of smooth sets is not just any topos: it is a topos of
*spaces*, related to the base topos of sets by Lawvere's adjoint tower
of [[cohesion|cohesive-topos]] — connected components, discrete
spaces, underlying points, codiscrete spaces. We construct the full
tower $\Pi_0 \dashv \rm{Disc} \dashv \Gamma \dashv \rm{Codisc}$
for the presheaf topos on *any* site with a terminal probe, together
with the equivalence $\Pi_0 \circ \rm{Disc} \simeq \rm{Id}$ that
distinguishes it from a petit topos.

```agda
_ = Cat.Instances.Presheaf.Cohesive.Γ
_ = Cat.Instances.Presheaf.Cohesive.Disc
_ = Cat.Instances.Presheaf.Cohesive.Codisc
_ = Cat.Instances.Presheaf.Cohesive.Π₀
_ = Cat.Instances.Presheaf.Cohesive.Disc⊣Γ
_ = Cat.Instances.Presheaf.Cohesive.Γ⊣Codisc
_ = Cat.Instances.Presheaf.Cohesive.Π₀⊣Disc
_ = Cat.Instances.Presheaf.Cohesive.Π₀-Disc
```

The paper's (11) and (12) — diffeological spaces as the smooth sets
determined by their points — are the [[concrete
presheaves|concrete-presheaf]] with respect to this cohesion: those
whose plots embed into functions on points. They form a full
subcategory, and the classifying spaces of differential forms are the
standard *non*-examples.

```agda
_ = Cat.Instances.Presheaf.Concrete.is-concrete
_ = Cat.Instances.Presheaf.Concrete.Concrete
```

For the infinitesimal column of the probe table — where variational
calculus takes place, (13)–(16) — the paper itself pivots to algebra:
the site is a full subcategory of formal duals of $R$-algebras. This
is fully constructive. Over any commutative ring we build the [[dual
numbers|dual-numbers]] $R[\epsilon]$ with $\epsilon^2 = 0$, the
walking-infinitesimal site $\{\ast, \bD\}$, and its cohesive gros
topos of [[formal sets|formal-sets]], in which Schreiber's (16) is a
*definition with content*: the tangent bundle is the mapping space
$T X = \rm{Maps}(\bD, X)$, the projection is restriction along
$\iota : \ast \to \bD$, and tangent vectors are exactly the plots
by the infinitesimal disk.

```agda
_ = Algebra.Ring.DualNumbers.R[ε]
_ = Algebra.Ring.DualNumbers.ε²
_ = Cat.Instances.FormalSets.Infinitesimals
_ = Cat.Instances.FormalSets.FrmlSet
_ = Cat.Instances.FormalSets.𝔻
_ = Cat.Instances.FormalSets.T
_ = Cat.Instances.FormalSets.T-proj
_ = Cat.Instances.FormalSets.T-at-point
```

And then, *properly*: the paper's site (13) of [[thickened Cartesian
spaces|thickened-cartesian-space]] itself, with both columns of the
probe table — affine spaces *and* infinitesimal thickenings — read
constructively through their function algebras. The smooth column is
the free commutative algebra — the [[polynomial
ring|polynomial-ring]], constructed as a higher inductive type with
its full universal property — and the site is closed under products
with the disk, which is what makes those products *representable*.
Over this site, [[formal smooth sets|formal-smooth-sets]] form a
cohesive gros topos containing the affine line, and the
**Kock–Lawvere axiom** of synthetic differential geometry — plots of
$\rm{Maps}(\bD, \bA^1)$ are pairs, value and derivative — is a
[[theorem|kock-lawvere]], proved by composing the universal
properties of the polynomial ring and the dual numbers with the
Yoneda lemma.

```agda
_ = Algebra.Ring.Polynomial.R[_]
_ = Algebra.Ring.Polynomial.extend
_ = Cat.Instances.FormalSmoothSets.ThCartSp
_ = Cat.Instances.FormalSmoothSets.FrmlSmthSet
_ = Cat.Instances.FormalSmoothSets.𝔸¹
_ = Cat.Instances.FormalSmoothSets.𝔻-product
_ = Cat.Instances.FormalSmoothSets.Kock-Lawvere
_ = Cat.Instances.FormalSmoothSets.Maps-point
```

`Kock-Lawvere`{.Agda} is precisely the theorem that the founding axiom
of J. L. Bell's [[smooth infinitesimal analysis|synthetic-derivative]]
[@Bell:Primer] — his **Principle of Microaffineness**, that every map
of the infinitesimal $\Delta = \{d : d^2 = 0\}$ into the line is
*uniquely* affine — holds in the gros topos. Taking that axiom as a
*hypothesis* (never a postulate), Bell's textbook development of the
calculus is a machine-checked constructive theory: the derivative is
the affine coefficient, its uniqueness *is* **microcancellation**, the
**fundamental equation** $f(x+\varepsilon) = f(x) + \varepsilon f'(x)$
has an identically-zero remainder, and the **Leibniz** and **chain**
rules and **Fermat's** stationary-point rule are two-line consequences
of $\varepsilon^2 = 0$. The **failure of excluded middle** on $\Delta$
is here a constructive *theorem*, and with a Constancy axiom the smooth
line is **indecomposable**. This is the abstract axiomatics underneath
the concrete dual-number `δ` every heliostat module computes with.

```agda
_ = Physics.SmoothWorld.Bell.microcancel
_ = Physics.SmoothWorld.Bell.fundamental
_ = Physics.SmoothWorld.Bell.deriv-*
_ = Physics.SmoothWorld.Bell.deriv-∘
_ = Physics.SmoothWorld.Bell.fermat-→
_ = Physics.SmoothWorld.Bell.Δ-no-lem
_ = Physics.SmoothWorld.Bell.indecomposable
```

That axiomatic development is honest but *ungrounded* — Microaffineness
holds in no set-level ring. The grounding is supplied model-side: over
`FrmlSmthSet`{.Agda}, the representable line $\bA^1$ **is** Bell's smooth
line, and `Kock-Lawvere`{.Agda} **is** his Microaffineness axiom, a
*theorem*. Read that way, `Physics.SmoothWorld.Internal`{.Agda} extracts
Bell's Chapter 1 directly: the **fundamental equation**
$f(x+\varepsilon)=f(x)+\varepsilon f'(x)$ is the unit of the
Kock–Lawvere equivalence, and **microcancellation** is its injectivity —
the model-side vindication the abstract module could only assume. The
one subtlety is sharp: the set-level axiomatization quantifies over
*arbitrary* set-functions on a ring's nilsquares, a strictly stronger,
false-in-general statement — Bell's consistency rests on the *smooth*
(internal-hom) arrow $T\bA^1$, which is exactly what `Kock-Lawvere`{.Agda}
governs.

```agda
_ = Physics.SmoothWorld.Internal.KL
_ = Physics.SmoothWorld.Internal.fundamental
_ = Physics.SmoothWorld.Internal.microcancel
_ = Physics.SmoothWorld.Internal.unique-slope
```

In this topos the paper's flagship *non-concrete* smooth set also
exists: the [[de Rham classifier|de-rham-classifier]] of 1-forms,
whose plots are [[Kähler differentials|kahler-differentials]]. It has
a contractible set of points, and — over a nontrivial ring — a
nonvanishing differential $\mathrm{d}x$ on the line, witnessed by
the derivative functional obtained by evaluating into the dual
numbers at $x + \epsilon$. So it is *not* concrete: smooth sets see
strictly more than diffeological spaces, which is where anomaly
polynomials live.

```agda
_ = Cat.Instances.FormalSmoothSets.DeRham.Ω¹-dR
_ = Cat.Instances.FormalSmoothSets.DeRham.Ω¹-dR-point
_ = Cat.Instances.FormalSmoothSets.DeRham.Ω¹-dR-not-concrete
```

For the fermionic column ((17), (18)): the [[Grassmann
algebra|grassmann-algebra]] over any commutative ring, with the
anticommutation relation as a constructor and the
$\mathbb{Z}/2$-grading carried by the parity involution.

```agda
_ = Algebra.Ring.Grassmann.Grassmann
_ = Algebra.Ring.Grassmann.σ-parity
_ = Algebra.Ring.Grassmann.σ-σ
```

The Grassmann algebra carries its full universal property — a map
out of it is a map on the base landing in the [[centre|
centre-of-a-ring]] of the target, together with anticommuting
square-zero images for the odd generators — and with it the paper's
super site ((19)–(20)) assembles: probes are polynomial affine
spaces with anticommuting directions, morphisms are
parity-respecting algebra maps under the base, the super point
$\bA^{0|0}$ is terminal by composing the two universal properties
through the centre, and [[super smooth sets|super-smooth-sets]] are
the presheaves on this site, cohesive as before.

```agda
_ = Algebra.Ring.Grassmann.grassmann-extend
_ = Algebra.Ring.Center.Centre
_ = Cat.Instances.SuperSmoothSets.SupCartSp
_ = Cat.Instances.SuperSmoothSets.pt-terminal
_ = Cat.Instances.SuperSmoothSets.SupSmthSet
```

Finally, on the last column of the table: stable homotopy theory. A
[[prespectrum]] is a tower of ever-higher deloopings
$E_0 \to \Omega E_1 \to \Omega^2 E_2 \to \cdots$, an
[[Ω-spectrum|omega-spectrum]] one where each map is an equivalence —
the paper's "Where quantum physics takes place".

```agda
_ = Prespectrum
_ = is-Ω-spectrum
```

## The constructive simulator: compiling physics to categories

The deepest structural point of the paper is that all these
"variable" contexts — sets, smooth sets, formal smooth sets, super
smooth sets — share the same *internal language*. A physical system
specified once, by operations on abstract types, makes sense in every
one of them. The 1Lab expresses this as [[compiling to
categories|compiling-to-categories]]: a [[λ-signature]] of base types
and operations freely generates a [[cartesian closed category]] of
programs, and any [[model|model-of-a-lambda-signature]] of the
signature in a cartesian closed category $\cC$ extends to a functor
$\Syn \to \cC$ preserving all the structure.

As a demonstration, here is a complete (if small) physical system: a
**heliostat** — a mirror that tracks the sun so that the reflected
ray hits a fixed target. The signature has two base types, `angle`
and `time`, and two operations: the sun's azimuth as a function of
time, and the aiming law. (Measuring time so that the sun moves at
unit speed, and angles in half-units, both operations are exactly
*addition*: the mirror normal must bisect the sun and target
directions.)

```agda
data Heliostat-type : Type where
  angle time : Heliostat-type

data Heliostat-op
  : types.Ty Heliostat-type → Heliostat-type → Type where
  sun-at : Heliostat-op (` time) angle
  aim    : Heliostat-op (` angle `× ` angle) angle
```

<!--
```agda
private
  Heliostat-type-is-set : is-set Heliostat-type
  Heliostat-type-is-set = retract→is-hlevel 2 dec enc ret (hlevel 2) where
    enc : Heliostat-type → Bool
    enc angle = true
    enc time = false

    dec : Bool → Heliostat-type
    dec true = angle
    dec false = time

    ret : ∀ x → dec (enc x) ≡ x
    ret angle = refl
    ret time = refl

  Heliostat-op-is-prop : ∀ {τ b} → is-prop (Heliostat-op τ b)
  Heliostat-op-is-prop sun-at sun-at = refl
  Heliostat-op-is-prop aim aim = refl
```
-->

```agda
Heliostat : λ-Signature lzero
Heliostat .Ob = Heliostat-type
Heliostat .Ob-is-set = Heliostat-type-is-set
Heliostat .Hom = Heliostat-op
Heliostat .Hom-is-set = is-prop→is-set Heliostat-op-is-prop
```

<!--
```agda
open import Cat.CartesianClosed.Free Heliostat
open import Cat.CartesianClosed.Free.Lambda Heliostat
```
-->

The controller is a *program* in the [[simply-typed lambda
calculus|STLC]] over this signature: given the time and the target
direction, point the mirror at the bisector of the current sun
position and the target.

```agda
mirror-program : Expr (∅ , ` time `× ` angle) (` angle)
mirror-program =
  `hom aim `⟨ `hom sun-at (`π₁ (`var stop)) , `π₂ (`var stop) ⟩
```

To *run* it, interpret the signature in the topos of sets: both base
types become the integers, and both operations become what they
always were, addition.

```agda
private
  module SetsModel = Cat.CartesianClosed.Free.Model Heliostat
    (Sets-cartesian {ℓ = lzero}) Sets-closed

heliostat-interp
  : elim.base-method
      SetsModel.chaotic-cartesian SetsModel.chaotic-closed
      (λ _ → el! Int)
heliostat-interp sun-at = λ t → t
heliostat-interp aim = λ (s , t) → s +ℤ t

private
  module Run = SetsModel.model (λ _ → el! Int) heliostat-interp

run-heliostat : Lift lzero ⊤ × Int × Int → Int
run-heliostat = Run.compile .F₁ ⟦ mirror-program ⟧ᵉ
```

The compiled controller is an honest function, and it *computes*: at
time $2$, aiming at target direction $3$, the mirror should sit at
$5$ — and this is so definitionally, by `refl`{.Agda}.

```agda
_ : run-heliostat (lift tt , 2 , 3) ≡ 5
_ = refl
```

The same program, unchanged, runs in every cartesian closed category:
in particular in the topos of sheaves on *any* site — any gros topos
of generalized smooth spaces — where the base types may now be
interpreted as, say, a sheaf of smoothly-varying angles, and where
mapping spaces (10) provide the configuration spaces of *fields* of
heliostats. This is the sense in which the formalisation is a
constructive simulator: one syntax, all semantics.

```agda
module heliostat-fields
    {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  where

  private
    module ShModel = Cat.CartesianClosed.Free.Model Heliostat
      (Sh[]-cartesian J) (Sh[]-closed {J = J})

  heliostat-in-sheaves
    : (V : Heliostat-type → ⌞ Sh[ C , J ] ⌟)
    → elim.base-method ShModel.chaotic-cartesian ShModel.chaotic-closed V
    → Functor Free-ccc Sh[ C , J ]
  heliostat-in-sheaves V ops = ShModel.model.compile V ops
```

Moreover the compilation functors are not bare functors: they
preserve products and exponentials — the [[cartesian closed
functor|cartesian-closed-functor]] structure that makes "the space of
fields" mean the same thing before and after compilation.

```agda
_ = SetsModel.model.compile-cartesian
_ = SetsModel.model.compile-closed
_ = Cartesian-closed-functor
```

The heliostat aims; for a system that *moves*, see the [[harmonic
oscillator|harmonic-oscillator]], which exercises every column built
below: its compiled dynamics conserve energy and close their orbits
*by theorem*, its force law is derived synthetically from the
potential, its continuous-time Hamiltonian flow conserves energy
exactly over the dual numbers (with the Euler integrator's failure
computed as exactly the $(\mathrm{d}t)^2$ term that nilpotency
kills), its fermionic partner satisfies Pauli exclusion as ring
algebra, and its parity symmetry is gauged with the homotopy
quotient remembering the stabilizer of the origin.

```agda
_ = Physics.Oscillator.step
_ = Physics.Oscillator.period-four
_ = Physics.Oscillator.energy-conserved
_ = Physics.Oscillator.force-from-potential.hooke
_ = Physics.Oscillator.hamiltonian-mechanics.conserved
_ = Physics.Oscillator.euler-energy-defect
_ = Physics.Oscillator.fermionic.modes-nilpotent
_ = Physics.Oscillator.gauge-loops-differ
_ = Physics.Newton.second-order-flow.newton
_ = Physics.Maxwell.electromagnetism.same-field
```

That toy heliostat aims in one dimension — its law *aim = addition* is
the bisector of the sun and target directions. The **real** device is a
paraboloid concentrator, and it lives in the infinitesimal column.
Reading geometric optics as a variational field theory after
Giotopoulos and Sati [@GiotopoulosSati:FieldTheory], the mirror is a
plot of a [[formal smooth set|formal-smooth-set]], its surface normal
is a genuine cross product of [[Kock–Lawvere|kock-lawvere]] tangent
derivatives — *derived*, not posited — Fermat's principle is the
Euler–Lagrange condition $\delta(\mathrm{path}) = 0$, and the
parabola's perfect focusing is an exact ring identity: the axial ray
reflects, at *every* surface point, onto the line through the focus.
Its finite counterpart is the [[eikonal|eikonal]]: the same mirror is
equidistant from focus and directrix — the equal-optical-path principle
that makes the reflected wavefront a sphere — again an exact ring
identity, the wavefront order of the same Fermat principle whose ray
order is the reflection law. As with the oscillator, the Euler–Lagrange
*equation* is reached synthetically while the optical *action integral*,
and the eikonal equation $|\nabla S|^2 = n^2$ as a field equation, wait
on integration.

The ray bundle itself — the *"section built from germs"* of the
concentrator's control code — is realised as the [[germs|germ-of-a-plot]]
of this aiming field over the reflector's *own* probe site: the aiming
polynomial is literally a plot of the line by the mirror probe $\bA^2$,
whose function ring *is* the optics observable ring, and its stalk is the
germ of that plot. Over this formal site the germ coincides with the
plot — the section is its own germ — the genuinely *shrinking*
infinitesimal germs of the smooth site being the same analytic gap listed
below.

```agda
_ = Physics.Heliostat.Optics.optics.normal-value
_ = Physics.Heliostat.Optics.optics.focusing
_ = Physics.Heliostat.Optics.optics.focusing-parallel
_ = Physics.Heliostat.Eikonal.wavefront.equal-path
_ = Physics.Heliostat.Eikonal.wavefront.mirror-on-sphere
_ = Physics.Heliostat.Sheaf.sheaf.aiming-plot
_ = Physics.Heliostat.Sheaf.sheaf.germs-are-plots
_ = Physics.Heliostat.Sheaf.sheaf.aim-descends
```

Following the oscillator, the heliostat now exercises *every* column of
the probe table over the same infrastructure. Its sag potential's
[[Kähler differential|kahler-differentials]] is the optical field
strength, an exact — hence conservative — $1$-form, with the same
`gauge`{.Agda} invariance as `Physics.Maxwell`{.Agda}. The paraboloid's
curvature is a [[Weil|formal-smooth-set]] $2$-jet whose $\delta^2$
coefficient *is* the reciprocal focal length, exactly as
`Physics.Newton`{.Agda} reads $F = ma$ off a jet. The sun-*tracking* law
is a [[compiled|compiling-to-categories]] $\lambda$-program that runs in
every cartesian closed category and closes its diurnal cycle by
`refl`{.Agda}. Its $\ZZ/4$ axial-rotation symmetry is **gauged**, the
mirror vertex an orbi-singularity $\rm{pt}/\!\!/(\ZZ/4)$ that the naive
quotient forgets — the `gauge-loops-differ`{.Agda} of the oscillator, one
turn finer. And the by-hand tangent partial is *proved* to be the genuine
[[Kock–Lawvere|formal-smooth-set]] derivative of a synthetic tangent
vector, with the aiming field's differentials honestly *non*-concrete.

```agda
_ = Physics.Heliostat.Forms.sag-forms.slope-form
_ = Physics.Heliostat.Forms.sag-forms.same-optics
_ = Physics.Heliostat.Curvature.curvature.curvature-is-focal
_ = Physics.Heliostat.Curvature.curvature.focusing-residual-second-order
_ = Physics.Heliostat.Tracking.step
_ = Physics.Heliostat.Tracking.on-target
_ = Physics.Heliostat.Symmetry.optics-symmetry.normal-rot-equivariant′
_ = Physics.Heliostat.Symmetry.gauge-loops-differ
_ = Physics.Heliostat.Sheaf.sheaf.∂u-is-KL-derivative
_ = Physics.Heliostat.Sheaf.sheaf.aiming-nonconcrete-contrast
```

Beyond the optics, the concentrator's remaining subsystems are its
reward, its receiver, and its clock. The focusing **reward** is a
variance: the ray-bundle score is the Koenig–Huygens / parallel-axis
decomposition of the endpoints, whose spread term is a manifest sum of
squares and which is **permutation-invariant** — the bundle is a *set*
of ray germs, order-free, factoring through the same set-quotient as the
`Sheaf`{.Agda} germs. The **receiver**'s thermal relaxation has a
synthetic stability rate — the dual-number derivative of its
radiative-plus-convective flux, $-(h + 4\sigma\epsilon A\,T^3)$ — and the
exact $(\mathrm{d}t)^2$ Euler defect of the oscillator. And the **solar
clock** closes on genuine cyclic periods $\ZZ/24$, $\ZZ/365$, while the
mirror's **focus is the conserved Noether charge** of the diurnal
time-translation: as the sun moves and the primary re-points, the focus
is fixed on the nose.

```agda
_ = Physics.Heliostat.Bundle.bundle-variance.parallel-axis-2
_ = Physics.Heliostat.Bundle.bundle-variance.reward-swap-2
_ = Physics.Heliostat.Thermal.thermal.stability-rate
_ = Physics.Heliostat.Thermal.thermal.euler-relaxation-defect
_ = Physics.Heliostat.Solar.sky-holds-day
_ = Physics.Heliostat.Solar.diurnal-closes
_ = Physics.Heliostat.Solar.noether.focus-invariant
```

## Gauge transformations and simplicial shapes

Where the paper turns to gauge theory ((22)–(25)), plots stop forming
sets and start forming *groupoids*: two field configurations may be
identified by a gauge transformation, gauge transformations compose
(23), and higher gauge transformations identify identifications. The
shapes probing this structure are the simplices $\Delta^n$ of (25),
which form the [[simplex category]] with its [[coface]] and
[[codegeneracy]] generators satisfying the simplicial identities; the
resulting probe-topos is that of [[simplicial sets|simplicial-set]].

```agda
_ = Δ
_ = δ
_ = σ
_ = δ-comm
_ = σ-comm
_ = δ-σ-comm
_ = sSet
_ = Δ[_]
```

The paper's boxed *Kan condition* — every [[horn]] $\Lambda^n_k \mono
\Delta^n$ of gauge transformations admits a filler — is
`is-kan`{.Agda}, and the higher groupoids of (32),
$\rm{Sh}(\Delta)_{\rm{Kan}} \mono \rm{Sh}(\Delta)$, are the full
subcategory of [[Kan complexes|kan-complex]].

```agda
_ = Λ[_,_]
_ = horn-inclusion
_ = is-kan
_ = Kan-complexes
```

The delooping groupoid $\mathbf{B}G$ of (26) is the [[nerve]] of the
one-object [[delooping category]], and the computation (27) of its
plots — a single vertex, a 1-simplex for every group element, and a
2-simplex for every *pair*, witnessing the composite — holds here
for any monoid:

```agda
_ = nerve
_ = nerve-B
_ = nerve-B₀-is-contr
_ = nerve-B₁≃M
_ = nerve-B₂≃M×M
```

Chain complexes ((29)) exist as a category; connected components of
simplicial sets give the combinatorial core of nonabelian cohomology
((39)): $H^1$ with coefficients in a group is $\pi_0$ of the mapping
space into the delooping. [[Simplicial
presheaves|simplicial-presheaf]] over any site realise the shape of
(36), and the computation (37) of $\Delta^2$-plots of the delooping
at every geometric stage follows from the nerve computation by
Yoneda. Parameterized spectra — the objects of the tangent topos
(41) — are families of [[prespectra|prespectrum]].

```agda
_ = Chain-complex
_ = Ch
_ = π₀ˢ
_ = H¹[_,_]
_ = Cat.Instances.SimplicialPresheaves.sPSh
_ = Cat.Instances.SimplicialPresheaves.plots-Δ²-BM
_ = Prespectrum-over
```

The bridge from the gauge column to the linear one — the direction
of the Dold–Kan correspondence (30) that physics uses, from
simplicial data to a BRST-style complex — is the [[Moore
complex|moore-complex]] of normalized chains of a simplicial abelian
group, where normalization makes $\partial \partial = 0$ a single
simplicial identity. The [[Čech object|cech-object]] of a map of
presheaves packages descent data along an atlas, augmented over its
base ((38)); the [[action groupoid|action-groupoid]] realises the
homotopy quotient of a gauge action, with configurations as vertices
and gauge transformations as edges; and the probes of the stable
column form the site of [[negative-dimensional
spheres|negative-sphere]], whose presheaves are families pointed
over a common base — parameterized spectra before stabilisation.

```agda
_ = Algebra.ChainComplex.Moore.Moore
_ = Cat.Instances.SimplicialPresheaves.Cech.Čech
_ = Cat.Instances.SimplicialPresheaves.Cech.cech-aug
_ = Cat.Instances.SimplicialSets.ActionGroupoid.Action-groupoid
_ = Cat.Instances.SimplicialSets.ActionGroupoid.homotopy-quotient
_ = Cat.Instances.SimplicialSets.ActionGroupoid.quotient-edges
_ = Cat.Instances.NegativeSpheres.Lin
_ = Cat.Instances.NegativeSpheres.base-section
```

Three more strata have since landed. The **orbi-singular site** of
(28) is the global orbit category — groups, with conjugacy classes
of homomorphisms — with the trivial cone as terminal probe. The
**inverse Dold–Kan construction** gives the functor $\Gamma$ from
chain complexes back to simplicial abelian groups, hom-theoretically
(so no shuffle combinatorics), and with it the Eilenberg–MacLane
objects $K(A,n)$ of (31) and ordinary **cohomology** as $\pi_0$ of
mapping spaces. And toward the topos-theoretic completion of (8),
sheafification over an *arbitrary* coverage is proven to preserve
the terminal object.

```agda
_ = Cat.Instances.Singular.Snglr
_ = Cat.Instances.Singular.Snglr-terminal
_ = Algebra.ChainComplex.DoldKan.Γ
_ = Algebra.ChainComplex.DoldKan.K
_ = Algebra.ChainComplex.DoldKan.H[_,_]⟨_⟩
_ = Cat.Site.Sheafification.Lex.Sheafification-pres-⊤
_ = Cat.Site.Sheafification.Locality.locally-equal→inc-path
_ = Cat.Site.Sheafification.Locality.sheaf-detects
_ = Cat.Site.Sheafification.Plus.loc-trans
_ = Cat.Site.Sheafification.Plus.A₁-is-separated
_ = Cat.Site.Sheafification.Glue.covering-stable
_ = Cat.Site.Sheafification.Glue.B⁺-is-sheaf
_ = Cat.Site.Sheafification.Glue.unit⁺-injective
_ = Cat.Site.Sheafification.Kernel.unit-kernel
_ = Cat.Site.Sheafification.Topos.Sheafification-is-lex
_ = Cat.Site.Sheafification.Topos.Sheaves-topos
```

On the homotopy-theoretic side of the dictionary, the delooping of a
group exists as a higher inductive type with $G \simeq \Omega
\mathbf{B} G$ — the paper's (34) in the case $n = 1$ — and first
nonabelian cohomology appears as $H^1(X; G) = \| X \to \mathbf{B}G
\|_0$, computed in the 1Lab for abelian coefficients.

```agda
_ = Deloop
_ = G≃ΩB
```

## ∞-topoi, internally

The paper's ambient objects are *∞*-topoi, and the 1Lab meets them
from the inside: cubical type theory is the internal language of an
∞-topos, with types as ∞-groupoids and [[univalence]] as the object
classifier — the descent property by which Rezk and Lurie
characterise ∞-topoi. On this foundation the 1Lab now has the
internal theory of their subtopoi: [[modalities|modality]] à la
Rijke–Shulman–Spitters, whose lex members are reflective
sub-∞-topoi. The truncation modalities present the tower of
$n$-topoi sitting inside the ∞-topos — the paper's $n$-groupoid
approximations — and the open modality (proven left exact) presents
open subtopoi. The simplicial localisations $L^{\rm{heq}}$ of
(32)–(36) are externally-presented versions of exactly such
reflections.

```agda
_ = Homotopy.Modality.Modality
_ = Homotopy.Modality.is-lex
_ = Homotopy.Modality.Modality.modal-Σ
_ = Homotopy.Modality.Truncation
_ = Homotopy.Modality.Open-is-lex
_ = Data.Real.Base.ℝ
_ = Data.Real.Base.rational-density
_ = Data.Real.Arithmetic.archimedean
_ = Data.Real.Arithmetic._+ᴿ_
_ = Data.Real.Arithmetic.+ᴿ-invr
_ = Data.Real.Arithmetic.ratℝ-+
_ = Data.Real.Order.maxᴿ
_ = Data.Real.Order.absᴿ
```

## What is missing

For honesty, the items of the paper with no 1Lab counterpart yet.
On the analytic side, the boundary is sharp: the *differential*
layer of real analysis — derivatives, forces, flows, conservation
laws — is fully synthetic, with nilpotent infinitesimals in place of
limits (see the oscillator's Hamiltonian mechanics), and Taylor-level
calculus needs only $\bQ$-algebras and higher-order thickenings; but
*integration* — finite-time evolution, convergence, and the good
open covers of the classical smooth site — needs a genuine
real-numbers object. The [[Dedekind reals|dedekind-real]] now exist,
as a small type of located two-sided cuts, with their order theory,
density of the rationals, negation, the archimedean property,
Bishop approximation within any positive slack, an additive abelian
group structure ([[Minkowski addition|real-addition]] of cuts, with
the rational embedding an additive homomorphism), the
[[lattice|real-lattice]] of join, meet and absolute value, and
[[multiplication|real-multiplication]] of cuts by the interval
product — sign-analysis-free, commutative, with a two-sided unit,
zero absorption, and **full distributivity** over addition
(`*ᴿ-distribˡ`{.Agda}): the reverse containment $x \cdot (y + z) \le
x \cdot y + x \cdot z$ is proven by a simultaneous
$\delta$-budget tightening of *all three* factor brackets against
the super-additive defect of the four-fold minimum. Strictly
positive reals even have **reciprocals**
(`Data.Real.Reciprocal`{.Agda}): the reciprocal cut and the full
inverse law $x \cdot x^{-1} = 1$. The reals are thus a commutative
distributive structure with inverses; what remains before the
ordered field is complete is associativity of multiplication (the
same interval technique on triple products) and reciprocals of reals
merely apart from zero (the sign-indeterminate case). With the field
comes a constructive theory of $C^\infty$ maps and the classical
smooth site. Concretely missing, then:
the smooth-site instance of (7) (localisation over the
good-open-cover coverage, with shrinking-neighbourhood germs); the
pullback half of left exactness for the higher-inductive
sheafification (terminal-preservation is proven for arbitrary
coverages, and the path-space problem for the unit is
solved up to gluing: `Cat.Site.Sheafification.Plus`{.Agda} builds
saturated local equality as a proposition-valued HIT — making
transitivity and restriction-stability theorems — and delivers the
first half of the plus-construction: the effective separated
quotient $A_1$, proven separated over any coverage; locally equal
sections have equal units, and every sheaf detects local equality.
The gluing half is now also done:
`Cat.Site.Sheafification.Glue`{.Agda} saturates the coverage (again
a proposition-valued HIT), builds the plus-construction $B^+$ of a
separated presheaf over saturated covers — where restriction is
choice-free — and proves it a sheaf with injective unit. The
assembly is done as well: `Cat.Site.Sheafification.Kernel`{.Agda}
composes quotient and plus and proves, over an arbitrary coverage,
that **the unit of sheafification identifies two sections exactly
when they are locally equal** — the complete path-space
characterisation of the higher-inductive sheafification. And
`Cat.Site.Sheafification.Topos`{.Agda} finishes the item entirely:
**sheafification is left exact**, so `Sh[ C , J ]`{.Agda
ident=Sh[_,_]} is a `Topos`{.Agda} in the official sense, over any
coverage — diagram (8) discharged in full); Weil algebras beyond
second order (the second-order algebra, its jet derivative, and
Newton's law as a theorem now exist — see
`Physics.Newton`{.Agda}) and coverages on the thickened site; the odd-plot
description of spinor fields (21) and super-thickenings combining
the fermionic and infinitesimal sites; de Rham forms beyond degree two (Kähler 2-forms, the exterior
derivative with $d \circ d = 0$, gauge invariance of the field
strength, and electromagnetism in Landau gauge now exist — see
`Physics.Maxwell`{.Agda}; $\Omega^{\ge 3}$, the Bianchi identity in
degree two, the differential as a map of smooth sets, and
Deligne/connection refinements ((39), (40)) remain); the unit and counit of the
Dold–Kan correspondence (30) — both functors now exist, the Moore
complex $N$ and its inverse $\Gamma$, with $K(A,n)$ and ordinary
cohomology defined — together with Kan fibrancy of $K(A,n)$; closure of Kan complexes under
mapping spaces and the *external presentation* of the simplicial
localisations $L^{\rm{heq}}, L^{\rm{lheq}}$ ((32)–(36)) — their
internal shadow now exists as [[modalities|modality]], but
presenting a particular gros ∞-topos by simplicially localising
simplicial presheaves needs quasicategory or complete-Segal-object
infrastructure the 1Lab does not have;
the local weak equivalence of the Čech augmentation over covers,
giving cofibrant resolutions (full (39)); cohesion over the orbi-singular site (the site itself now exists,
with terminal probe; the instantiation awaits level-polymorphic
cohesion); and the stable localisation of presheaves on $\rm{Lin}$
presenting the tangent topos (41). Each is a well-posed project over
the infrastructure assembled above.

Finally, the *internalization* of [[smooth infinitesimal
analysis|synthetic-derivative]] is only begun. `Kock-Lawvere`{.Agda}
grounds Bell's Microaffineness and the differential calculus for the
representable line and its smooth (internal-hom) function space
`T`$\bA^1$ (see `Physics.SmoothWorld.Internal`{.Agda}); but the internal
calculus for arbitrary self-maps $\bA^1 \to \bA^1$ — Leibniz and the
chain rule at the internal-hom level, and any genuine $\forall(f : \bA^1
\to \bA^1)$ — needs three pieces that do not yet exist: an internal
**ring-object** structure on $\bA^1$; the **tensor product of
$R$-algebras** $R[X \uplus Y] \simeq R[X] \otimes_R R[Y]$ that would make
general products $\bA^n_k \times \bA^m_j$ representable (only the
bespoke $\times\bD$ product is shipped); and — for the logic rather than
the algebra — an **internal-language / Kripke–Joyal** layer, the sole
syntactic doctrine present being *regular* logic, without $\forall$ or
$\Rightarrow$.
