---
description: |
  Physics by refl: a synthetic, computing formalization of the
  topos-theoretic physics stack, where the axioms of synthetic
  differential geometry are theorems and the mechanics runs by
  definitional equality.
---
<!--
```agda
open import Cat.Prelude

import Cat.Instances.SimplicialSets.ActionGroupoid
import Cat.Instances.SimplicialSets.Nerve
import Cat.Instances.SimplicialPresheaves.Cech
import Cat.Instances.FormalSmoothSets.DeRham
import Cat.Instances.FormalSmoothSets
import Cat.Instances.SuperSmoothSets
import Cat.Instances.Presheaf.Cohesive
import Cat.Instances.Localisation.Invertible
import Cat.Site.Sheafification.Kernel
import Cat.Site.Sheafification.Topos
import Cat.CartesianClosed.Free.Model

import Algebra.ChainComplex.Moore
import Algebra.Ring.Kahler.Exterior
import Algebra.Ring.Grassmann

import Data.Real.Arithmetic
import Data.Real.Order
import Data.Real.Base

import Homotopy.Modality

import Physics.Oscillator
import Physics.Maxwell
import Physics.Newton
```
-->

```agda
module Physics.Paper where
```

# Physics by refl {defines="physics-by-refl"}

*A synthetic, computing formalization of the topos-theoretic physics
stack.*

**Abstract.** We report a formalization, in cubical Agda over the
1Lab, of the mathematical stack that Urs Schreiber's *Higher Topos
Theory in Physics* [@Schreiber:HTTPhysics] presents as the natural
home of physics: probe-categories and their gros topoi, cohesion,
infinitesimal thickenings, fermionic algebra, gauge groupoids, and
the internal theory of higher toposes. The formalization is
*constructive* — zero postulates — and it *computes*: a harmonic
oscillator specified once as a λ-term is compiled to the topos of
sets and traces its orbit by definitional equality, while its
conservation laws, force law, exclusion principle, and gauge
redundancy are theorems rather than observations. Two design
decisions distinguish this development from its neighbours. First,
the axioms of synthetic differential geometry are not postulated:
the Kock–Lawvere property is *proven* for an explicitly constructed
site of thickened affine spaces, so that nilpotent infinitesimals —
and with them, mechanics without limits — are available on
constructive ground. Second, every claim in this paper is a
hyperlink into machine-checked source, and the paper itself is a
module: if a theorem breaks, the paper fails to typecheck.

## 1. The claim, bounded precisely

"Physics as computation" admits a strong existing reading: Immler's
verified ODE solver in Isabelle/HOL [@Immler:Lorenz] certified the
numerics behind Tucker's proof that the Lorenz attractor is chaotic
— formalized flows, Poincaré maps, and rigorous enclosures. That
work verifies that a *simulation is correct*. The present
development makes a different claim: here the physics *is* the
computation. The oscillator's closed orbit is a chain of
definitional equalities; energy conservation along the infinitesimal
Hamiltonian flow is an identity in a ring with $\epsilon^2 = 0$, not
an enclosure with an error bound. The two claims are complementary —
enclosures reach the Lorenz attractor, identities do not (yet) — and
we bound ours honestly in §7.

The formalization spans, in rough dependency order: a
compiling-to-categories pipeline in the sense of Elliott
[@Elliott:compiling]; sheaves on probe sites with adjoint-quadruple
cohesion; polynomial and dual-number algebras as higher inductive
types with their universal properties, assembled into the thickened
site where Kock–Lawvere holds; Kähler differentials and the
non-concrete de Rham classifier; Grassmann algebras and the super
site; the simplicial layer (nerves, Kan conditions, homotopy
quotients, Čech objects, Moore complexes); Dedekind reals with
order, lattice, and additive-group structure; and reflective
subuniverses and left-exact modalities after Rijke, Shulman and
Spitters [@RSS:Modalities], as the internal theory of
sub-∞-toposes.

## 2. One syntax, all semantics

A physical system is specified as a λ-signature — base types and
operations — and its dynamics as a term of the simply-typed λ
calculus over that signature. The free cartesian closed category on
the signature admits a structure-preserving functor to *any*
cartesian closed category, so one specification runs everywhere: in
sets, in any presheaf topos, in any sheaf topos over any site.

```agda
_ = Cat.CartesianClosed.Free.Model.model.compile
```

The demonstration system is the harmonic oscillator, compiled to
sets over the integers at quarter-period time steps. It runs, and
its qualitative physics holds by theorem: the orbit closes for
*every* initial condition, and the energy is invariant under the
flow — discrete Noether, universally quantified.

```agda
_ = Physics.Oscillator.step
_ = Physics.Oscillator.period-four
_ = Physics.Oscillator.energy-conserved
```

## 3. Infinitesimals as theorems, mechanics without limits

Synthetic differential geometry is usually practised axiomatically:
one *posits* a ring object for which maps out of the walking
tangent $\mathbb{D}$ are affine (the Kock–Lawvere axiom), and
reasons in any model. The closest formal relative of the present
work — Cherubini, Coquand and Hutzler's synthetic algebraic
geometry in cubical Agda [@CCH:SAG] — likewise proceeds from
postulated duality axioms. This development instead *constructs* a
site of polynomial affine spaces with first-order thickenings, and
proves Kock–Lawvere as a statement about it: the tangent bundle of
the line is computed by the thickened probes. The thickening is
load-bearing — over reduced probes the theorem is false — which is
the paper's observation that infinitesimal halos belong in the
probe category, here made into mathematics.

```agda
_ = Cat.Instances.FormalSmoothSets.Kock-Lawvere
```

On this ground, mechanics proceeds without limits. Evaluating a
potential at the thickened point $x + \epsilon$ computes its
derivative — Hooke's law is derived, not posited — and the
Hamiltonian flow, *defined* by Hamilton's equations from synthetic
partial derivatives, conserves the Hamiltonian exactly: the Poisson
bracket $\{H, H\} = 0$ is ring algebra, with $\epsilon^2 = 0$ doing
the work that limits do classically. The finite-step Euler
integrator, by contrast, fails to conserve energy by *exactly* the
$(\mathrm{d}t)^2$ term that nilpotency kills — the boundary between
synthetic and numerical dynamics, computed.

```agda
_ = Physics.Oscillator.force-from-potential.hooke
_ = Physics.Oscillator.hamiltonian-mechanics.conserved
_ = Physics.Oscillator.euler-energy-defect
```

Second-order mechanics needs second-order infinitesimals: over the
Weil algebra $R[\delta]/\delta^3$, the Taylor expansion of the
potential computes value, force, and curvature in one evaluation,
and **Newton's second law is a theorem**: any jet-level solution of
Hamilton's equations has twice its acceleration coefficient equal to
the force — $F = ma$ with the $\tfrac12$ of $x + vt +
\tfrac12at^2$ made algebraically explicit, over any commutative
ring.

```agda
_ = Physics.Newton.second-order.V-jet
_ = Physics.Newton.second-order-flow.newton
```

The de Rham classifier of 1-forms is constructed from Kähler
differentials and proven *non-concrete* — it has one point but a
non-vanishing $\mathrm{d}x$ — witnessing, constructively, that
smooth sets see strictly more than diffeological spaces.

```agda
_ = Cat.Instances.FormalSmoothSets.DeRham.Ω¹-dR-not-concrete
```

## 4. Fermions, gauge, and the gros topoi

The fermionic sector is the Grassmann algebra over an arbitrary
commutative base, as a higher inductive type whose generating
relations *are* the physics: anticommutativity and the Pauli
exclusion principle. The theorem worth proving is that exclusion
survives superposition — any dressed mode $a\theta_i + b\theta_j$
squares to zero — and that fermion parity $(-1)^F$ is an involutive
grading. With the Grassmann universal property routed through the
centre of the target ring, the super site of the paper's diagram
(19)–(20) assembles, with a terminal super point and cohesive
presheaves.

```agda
_ = Physics.Oscillator.fermionic.modes-nilpotent
_ = Algebra.Ring.Grassmann.σ-σ
_ = Cat.Instances.SuperSmoothSets.pt-terminal
```

Gauge redundancy is groupoid structure, and discarding it is a
mathematical error the formalization can exhibit: gauging the
oscillator's parity symmetry via the action groupoid, the homotopy
quotient retains two provably distinct automorphisms at the
symmetric configuration — the stabilizer that the quotient *set*
destroys. Nonabelian cocycles appear as maps into the nerve of the
delooping, with $H^1$ as connected components of the mapping space;
Čech objects package descent data along a cover; the Moore complex
sends simplicial abelian groups to chain complexes with
$\partial\partial = 0$ falling out of a single simplicial identity.

```agda
_ = Physics.Oscillator.gauge-loops-differ
_ = Cat.Instances.SimplicialSets.Nerve.H¹[_,_]
_ = Cat.Instances.SimplicialPresheaves.Cech.cech-aug
_ = Algebra.ChainComplex.Moore.Moore
```

Gauge *fields* are differential forms, and the electromagnetic core
of that story is now formalized: Kähler 2-forms, the wedge, and the
exterior derivative with $d \circ d = 0$, whence **gauge invariance
of the field strength** — a vector potential in Landau gauge has $F
= \mathrm{d}A = \mathrm{d}x \wedge \mathrm{d}y$, a constant
magnetic field, and shifting $A$ by any exact form provably leaves
$F$ unchanged. The potential is gauge-dependent; the physics is
not; both facts are theorems.

```agda
_ = Algebra.Ring.Kahler.Exterior.gauge
_ = Physics.Maxwell.electromagnetism.F-value
_ = Physics.Maxwell.electromagnetism.same-field
```

All of this lives over an adjoint-quadruple cohesion
$\Pi_0 \dashv \rm{Disc} \dashv \Gamma \dashv \rm{Codisc}$
constructed for presheaves on any pointed probe site, and — for the
trivial coverages the development actually equips its sites with —
the paper's presentation of sheaves as a localisation at local
isomorphisms is a theorem rather than a programme.

```agda
_ = Cat.Instances.Presheaf.Cohesive.Π₀⊣Disc
_ = Cat.Instances.Localisation.Invertible.Localise-is-precat-iso
```

Since first writing this paper, the development has closed its own
largest gap: the higher-inductive sheafification is proven **left
exact** over an arbitrary coverage — through a path-space
characterisation of its unit as saturated local equality, itself
obtained by formalising the two-step plus-construction with
proposition-valued higher inductive types — so the sheaf categories
of this development are Grothendieck topoi in the 1Lab's official,
lex-reflective sense.

```agda
_ = Cat.Site.Sheafification.Kernel.unit-kernel
_ = Cat.Site.Sheafification.Topos.Sheaves-topos
```

## 5. The reals, and where analysis actually begins

The boundary between synthetic and analytic physics is the boundary
between nilpotents and limits, and the development walks up to it
from both sides. On the synthetic side, everything differential is
already algebra. On the analytic side, the Dedekind reals are
constructed as located two-sided cuts — landing in the lowest
universe, by propositional resizing — with their order theory,
density of the rationals, the archimedean property, Bishop
approximation within any positive tolerance, Minkowski addition
forming an abelian group, and the lattice of join, meet, and
absolute value. Multiplication of cuts, and past it a constructive
theory of $C^\infty$ maps, are what still separate this from the
classical smooth site.

```agda
_ = Data.Real.Base.ℝ
_ = Data.Real.Base.rational-density
_ = Data.Real.Arithmetic.archimedean
_ = Data.Real.Arithmetic.+ᴿ-invr
_ = Data.Real.Order.absᴿ
```

## 6. ∞-toposes, internally

Cubical type theory is the internal language of an ∞-topos, with
univalence as the object classifier — the descent property by which
Rezk and Lurie characterise ∞-toposes. The development contributes
the internal theory of their subtoposes: modalities in the sense of
Rijke–Shulman–Spitters, packaged minimally (reflector, unit,
elimination into reflected families, and modal path types) with
idempotence, the universal property, and closure of modal types
under identity and Σ all derived. Left-exact modalities are
identified as the sub-∞-toposes; the truncation modalities present
the $n$-topos tower; the open modality is constructed and *proven*
left exact. What the internal language cannot do — present a
particular gros ∞-topos by simplicially localising simplicial
presheaves — is exactly the stratum where Riehl–Shulman simplicial
type theory and its proof assistant Rzk [@RiehlShulman] are the
right companion tool, and we defer it there.

```agda
_ = Homotopy.Modality.Modality
_ = Homotopy.Modality.Modality.modal-Σ
_ = Homotopy.Modality.Open-is-lex
```

## 7. What is not claimed

No smooth manifolds, no convergence, no quantum dynamics: the
classical smooth site awaits constructive $C^\infty$ theory atop
the reals of §5; the Lorenz attractor remains Immler's, on the
other side of the nilpotent/limit boundary; the stable and
∞-categorical strata (spectra beyond towers, simplicial
localisations as presentations) are catalogued, with their internal
shadows formalized and their external presentations honestly
deferred. The full inventory of gaps is maintained, item by item,
at the end of the [[reading guide|higher-topos-theory-in-physics]].

## 8. Colophon

This development was written by Claude (Anthropic), as a
human-directed agent system: a coordinating model authored and
verified the core, and delegated parallelizable strata — the real
number arithmetic and lattice, among others — to concurrent
subagent sessions serialized through a typechecker lock, with every
milestone gated on a green check of the full file. The typechecker
was the only arbiter: nothing in this development is asserted on
authority, including by the authors of this sentence. The result is
59 commits of literate cubical Agda over the 1Lab, of which this
page is one — it typechecks, so the theorems it cites exist.
