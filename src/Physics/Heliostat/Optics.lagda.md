<!--
```agda
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Ring.Solver

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Data.Fin using (Fin ; fzero ; fsuc ; fin)

import Algebra.Ring.Polynomial
import Algebra.Ring.DualNumbers as Dual
import Algebra.Ring.Reasoning
import Cat.Reasoning
```
-->

```agda
module Physics.Heliostat.Optics where
```

# Parabolic focusing, synthetically {defines="heliostat parabolic-focusing reflection-law"}

A heliostat is a mirror that tracks the sun and throws its light onto
a fixed target. The idealized limit — the shape that focuses an
axial beam to a single point — is the paraboloid, and the statement
that it *does* focus is the founding computation of geometric optics.
Following Giotopoulos and Sati's *Field Theory via Higher Geometry I*
[@GiotopoulosSati:FieldTheory], we read geometric optics as a
**variational field theory in smooth sets**: the mirror is a plot of a
[[formal smooth set|formal-smooth-set]], its tangent planes are
computed by the same infinitesimal $\mathbb{D} = \operatorname{Spec}
R[\epsilon]$ that powers the already-formalized
[[Kock–Lawvere|formal-smooth-set]] theorem and the synthetic tangent
calculus of `Physics.Newton`{.Agda}, and Fermat's principle — light
takes the stationary optical path — is the Euler–Lagrange condition
$\delta(\text{path}) = 0$ of that field theory. The reflection law is
its infinitesimal shadow.

Exactly as in the [[harmonic oscillator|harmonic-oscillator]]'s
`hamiltonian-mechanics`{.Agda}, everything at the differential level is
*synthetic*: the surface normal is a genuine
[[cross product|parabolic-focusing]] of tangent vectors obtained by
synthetic partial differentiation (`∂x`/`∂p` there, `∂u`/`∂v` here,
both the Kock–Lawvere evaluate-at-$(x+\epsilon)$ recipe of the
[[dual numbers|dual-numbers]] — the field strengths of
`Physics.Maxwell`{.Agda} are the same $\epsilon$-coefficient read
invariantly as a [[Kähler form|kahler-differentials]]), and the
focusing identity is exact ring algebra over *any* commutative ring of
scalars, discharged by the ring solver `cring!`{.Agda}.

**Conventions.** Space is right-handed $R^3$; vectors are triples over
a commutative ring. The mirror carries coordinates $(u,v)$, the
optical axis is the $z$-direction, and the incoming solar ray travels
*down* the axis, $d = (0,0,-1)$. We work division-free: the focal
scalar $q = 1/(4f)$ is kept as a ring element, never a quotient, and
the relation $4qf = 1$ that pins the focus enters only as a
**hypothesis**, discharged by a `subst`/`ap` — never by dividing.

**Why two rings.** The [[ring solver|commutative-ring]] `cring!`{.Agda}
reflects a ring's *own* projections $\{0r, 1r, +, *, -\}$; over a
*derived* ring such as the polynomial ring the geometric operations are
the primitives the ring is built *from*, which the solver cannot see.
So the vector calculus and the pure focusing identity are proved once,
over an **abstract** commutative ring `S`{.Agda} where the solver
applies — this is the module `euclid`{.Agda} below — and only then
instantiated at the ring of polynomial observables, where the synthetic
derivatives live. This is the same abstract-then-instantiate discipline
the oscillator uses for its Euler defect.

## The vector toolkit and the focusing identity, abstractly

Over any commutative ring `S`{.Agda}, a vector is a triple, and we
build the pointwise vector-space operations together with the two
products of Euclidean geometry. The scan of the library turns up no
vector calculus, so this small $R^3$ layer is new.

```agda
module euclid {ℓ} (S : CRing ℓ) where
  private module S = CRing-on (S .snd)

  Vec3 : Type ℓ
  Vec3 = ⌞ S ⌟ × ⌞ S ⌟ × ⌞ S ⌟
```

The cross product uses the standard right-handed convention $a \times b
= (a_2 b_3 - a_3 b_2,\; a_3 b_1 - a_1 b_3,\; a_1 b_2 - a_2 b_1)$; these
are the tangent-plane operations through which the surface normal will
be *derived*, not posited.

```agda
  infixr 30 _·s_
  infixl 25 _+v_ _-v_

  _·s_ : ⌞ S ⌟ → Vec3 → Vec3
  s ·s (x , y , z) = (s S.* x) , (s S.* y) , (s S.* z)

  _+v_ _-v_ : Vec3 → Vec3 → Vec3
  (x , y , z) +v (x' , y' , z') = (x S.+ x') , (y S.+ y') , (z S.+ z')
  (x , y , z) -v (x' , y' , z') =
    (x S.+ (S.- x')) , (y S.+ (S.- y')) , (z S.+ (S.- z'))

  dot : Vec3 → Vec3 → ⌞ S ⌟
  dot (x , y , z) (x' , y' , z') =
    ((x S.* x') S.+ (y S.* y')) S.+ (z S.* z')

  cross : Vec3 → Vec3 → Vec3
  cross (a₁ , a₂ , a₃) (b₁ , b₂ , b₃) =
      ((a₂ S.* b₃) S.+ (S.- (a₃ S.* b₂)))
    , ((a₃ S.* b₁) S.+ (S.- (a₁ S.* b₃)))
    , ((a₁ S.* b₂) S.+ (S.- (a₂ S.* b₁)))
```

The **division-free reflection** of a ray $d$ across the plane with
normal $n$ is $\operatorname{reflect}_n d = \langle n,n\rangle\, d -
2\langle d,n\rangle\, n$. This is Householder reflection scaled by
$\langle n,n\rangle$: it avoids ever normalizing $n$, so no inverse of
$\langle n,n\rangle$ is needed, and it makes sense over any ring. (The
usual $d - 2\frac{\langle d,n\rangle}{\langle n,n\rangle}n$ is this one
divided by $\langle n,n\rangle$; over a general ring we keep the
unnormalized version and pay for it with an explicit scale factor in
the focusing theorem.) The doubling $2 = 1 + 1$ is written as
`S.1r S.+ S.1r`, so no numeral literal is needed.

```agda
  reflect : Vec3 → Vec3 → Vec3
  reflect d n = (dot n n ·s d) -v (((S.1r S.+ S.1r) S.* dot d n) ·s n)
```

The geometric data of the problem: the incoming axial ray $d =
(0,0,-1)$; the paraboloid $\sigma(u,v) = (u, v, q(u^2+v^2))$ of focal
scalar $q$; its focus $F = (0,0,f)$; the scale factor $4q$; and its
normal $(-2qu, -2qv, 1)$, which downstream we will *derive* by
differentiating $\sigma$.

```agda
  incoming : Vec3
  incoming = S.0r , S.0r , (S.- S.1r)

  surf : ⌞ S ⌟ → ⌞ S ⌟ → ⌞ S ⌟ → Vec3
  surf a b c = a , b , (c S.* ((a S.* a) S.+ (b S.* b)))

  foc : ⌞ S ⌟ → Vec3
  foc g = S.0r , S.0r , g

  four : ⌞ S ⌟ → ⌞ S ⌟
  four c = ((S.1r S.+ S.1r) S.* (S.1r S.+ S.1r)) S.* c

  parab-normal : ⌞ S ⌟ → ⌞ S ⌟ → ⌞ S ⌟ → Vec3
  parab-normal a b c =
    (S.- (c S.* (a S.+ a))) , (S.- (c S.* (b S.+ b))) , S.1r
```

Here is the payoff, stated abstractly. The parabola's defining
property is that every axial ray reflects **through the focus**; since
our reflection is unnormalized (scaled by $\langle n,n\rangle$), the
reflected ray is a fixed scalar multiple of the ray to the focus:
$$\operatorname{reflect}_n d \;=\; 4q \cdot (F - \sigma),$$
with proportionality constant $4q = 1/f$, precisely when the focal
relation $4qf = 1$ holds. The three components are commutative-ring
identities in the atoms $a, b, c, g$: the $x$- and $y$-components are
**unconditional**, and the $z$-component becomes one after the leading
constant $1$ is rewritten to $4qf$ using the focal relation — the only
non-solver step in the theorem.

```agda
  focusing-abs
    : ∀ a b c g → four c S.* g ≡ S.1r
    → reflect incoming (parab-normal a b c)
    ≡ four c ·s (foc g -v surf a b c)
```

<!--
```agda
  focusing-abs a b c g focal = ap₂ _,_ crown-x (ap₂ _,_ crown-y crown-z)
    where
      W : ⌞ S ⌟
      W = c S.* ((a S.* a) S.+ (b S.* b))

      crown-x
        : reflect incoming (parab-normal a b c) .fst
        ≡ (four c ·s (foc g -v surf a b c)) .fst
      crown-x = cring! S

      crown-y
        : reflect incoming (parab-normal a b c) .snd .fst
        ≡ (four c ·s (foc g -v surf a b c)) .snd .fst
      crown-y = cring! S

      z-step1
        : reflect incoming (parab-normal a b c) .snd .snd
        ≡ S.1r S.+ (S.- (four c S.* W))
      z-step1 = cring! S

      z-step2
        : (four c S.* g) S.+ (S.- (four c S.* W))
        ≡ (four c ·s (foc g -v surf a b c)) .snd .snd
      z-step2 = cring! S

      crown-z
        : reflect incoming (parab-normal a b c) .snd .snd
        ≡ (four c ·s (foc g -v surf a b c)) .snd .snd
      crown-z =
          z-step1
        ∙ ap (S._+ (S.- (four c S.* W))) (sym focal)
        ∙ z-step2
```
-->

The coordinate-free restatement: the reflected ray and the
surface-to-focus ray are **parallel**, so their cross product
vanishes. Being a scalar multiple of one another, the cross of the
reflected ray with the surface-to-focus ray is the cross of a vector
with its own multiple — zero by antisymmetry, componentwise a
`cring!`{.Agda} identity.

```agda
  focusing-parallel-abs
    : ∀ a b c g → four c S.* g ≡ S.1r
    → cross (reflect incoming (parab-normal a b c)) (foc g -v surf a b c)
    ≡ (S.0r , S.0r , S.0r)
```

<!--
```agda
  focusing-parallel-abs a b c g focal =
      ap (λ r → cross r (foc g -v surf a b c)) (focusing-abs a b c g focal)
    ∙ ap₂ _,_ par-x (ap₂ _,_ par-y par-z)
    where
      v : Vec3
      v = foc g -v surf a b c

      par-x : cross (four c ·s v) v .fst ≡ S.0r
      par-x = cring! S

      par-y : cross (four c ·s v) v .snd .fst ≡ S.0r
      par-y = cring! S

      par-z : cross (four c ·s v) v .snd .snd ≡ S.0r
      par-z = cring! S
```
-->

## The reflector surface and its synthetic normal

We now instantiate the abstract layer at the ring of **polynomial
observables** in the two mirror coordinates, opening the polynomial
ring exactly as `hamiltonian-mechanics`{.Agda} does.

```agda
module optics {ℓ} (R : CRing ℓ) where
  open Algebra.Ring.Polynomial R
```

<!--
```agda
  private
    Obs : CRing ℓ
    Obs = R[ Lift ℓ (Fin 2) ]

    ObsRing : Ring ℓ
    ObsRing = Obs .fst , Obs .snd .CRing-on.has-ring-on

    module R' = CRing-on (R .snd)
    module Ro = CRing-on (Obs .snd)
    module Rr = Algebra.Ring.Reasoning ObsRing
    module CR = Cat.Reasoning (CRings ℓ)
```
-->

The Euclidean toolkit and the focusing identity are those of
`euclid`{.Agda}, at the observable ring.

```agda
  open module E = euclid Obs

  û v̂ : ⌞ Obs ⌟
  û = var (lift fzero)
  v̂ = var (lift (fsuc fzero))
```

The paraboloid of focal length $f$ is $z = (u^2 + v^2)/(4f)$; writing
$q = 1/(4f)$ for the focal scalar — a base-ring constant, injected by
`con`{.Agda} so that it is inert under differentiation in the mirror
coordinates — the mirror height is $q(u^2+v^2)$, and the surface is the
graph `surf û v̂ (con q)`{.Agda}.

```agda
  σz : ⌞ R ⌟ → ⌞ Obs ⌟
  σz Q = con Q *ₚ ((û *ₚ û) +ₚ (v̂ *ₚ v̂))

  σ : ⌞ R ⌟ → Vec3
  σ Q = surf û v̂ (con Q)
```

The tangent vectors to the mirror are the two synthetic partial
derivatives of $\sigma$, computed by the *same* dual-number recipe as
`hamiltonian-mechanics`{.Agda}: thicken one coordinate at a time by an
$\epsilon$ with $\epsilon^2 = 0$, evaluate, and read off the
$\epsilon$-coefficient. The per-variable thickening maps send the
differentiated variable to $(x, 1)$ and the other to $(x, 0)$.

<!--
```agda
  private
    dir-u dir-v : Lift ℓ (Fin 2) → ⌞ Dual.R[ε] Obs ⌟
    dir-u (lift (fin 0))       = û , con R'.1r
    dir-u (lift (fin (suc k))) = v̂ , con R'.0r
    dir-v (lift (fin 0))       = û , con R'.0r
    dir-v (lift (fin (suc k))) = v̂ , con R'.1r
```
-->

```agda
  ∂u ∂v : ⌞ Obs ⌟ → ⌞ Obs ⌟
  ∂u F = extend (Dual.ι-dual Obs CR.∘ con-hom) dir-u .∫Hom.fst F .snd
  ∂v F = extend (Dual.ι-dual Obs CR.∘ con-hom) dir-v .∫Hom.fst F .snd
```

The $z$-component of $\sigma$ is $q(u^2 + v^2)$; its $u$-derivative is
$q\,(u + u) = 2qu$ by the Leibniz rule $\delta(x^2) = x + x$ that lives
in the dual-number multiplication — precisely the `hooke`{.Agda} /
`∂x-H`{.Agda} computation of the oscillator, with $q$ inert because
`con Q`{.Agda} carries $\epsilon$-coefficient zero.

```agda
  ∂u-σz : ∀ Q → ∂u (σz Q) ≡ con Q *ₚ (û +ₚ û)
  ∂u-σz Q =
      ap₂ _+ₚ_
        (ap (con Q *ₚ_)
          ( ap₂ _+ₚ_
              (ap₂ _+ₚ_ Ro.*-idr (*ₚ-idl û))
              (ap₂ _+ₚ_ Rr.*-zeror Rr.*-zerol ∙ +ₚ-idl (con R'.0r))
          ∙ Ro.+-idr))
        Rr.*-zerol
    ∙ Ro.+-idr

  ∂v-σz : ∀ Q → ∂v (σz Q) ≡ con Q *ₚ (v̂ +ₚ v̂)
  ∂v-σz Q =
      ap₂ _+ₚ_
        (ap (con Q *ₚ_)
          ( ap₂ _+ₚ_
              (ap₂ _+ₚ_ Rr.*-zeror Rr.*-zerol ∙ +ₚ-idl (con R'.0r))
              (ap₂ _+ₚ_ Ro.*-idr (*ₚ-idl v̂))
          ∙ +ₚ-idl (v̂ +ₚ v̂)))
        Rr.*-zerol
    ∙ Ro.+-idr
```

The $u$- and $v$-derivatives of the flat coordinates are $1$ and $0$,
the `∂x`/`∂p` computations verbatim — and here they hold *definitionally*.

<!--
```agda
  private
    ∂u-û : ∂u û ≡ con R'.1r
    ∂u-û = refl

    ∂u-v̂ : ∂u v̂ ≡ con R'.0r
    ∂u-v̂ = refl

    ∂v-û : ∂v û ≡ con R'.0r
    ∂v-û = refl

    ∂v-v̂ : ∂v v̂ ≡ con R'.1r
    ∂v-v̂ = refl
```
-->

```agda
  ∂uσ ∂vσ : ⌞ R ⌟ → Vec3
  ∂uσ Q = ∂u û , ∂u v̂ , ∂u (σz Q)
  ∂vσ Q = ∂v û , ∂v v̂ , ∂v (σz Q)
```

The **surface normal is derived, not postulated**: it is the cross
product of the tangent frame. Cranking $(1,0,2qu) \times (0,1,2qv)$
gives $(-2qu, -2qv, 1)$, the outward normal to the paraboloid.

```agda
  normal : ⌞ R ⌟ → Vec3
  normal Q = cross (∂uσ Q) (∂vσ Q)

  normal-value : ∀ Q → normal Q ≡ parab-normal û v̂ (con Q)
```

<!--
```agda
  private
    neg-0ₚ : negₚ (con R'.0r) ≡ con R'.0r
    neg-0ₚ = sym (+ₚ-idl (negₚ (con R'.0r))) ∙ +ₚ-invr (con R'.0r)

  normal-value Q =
    ap₂ _,_
      ( ap₂ _+ₚ_ Rr.*-zerol (ap negₚ (nx-clean Q))
      ∙ +ₚ-idl (negₚ (con Q *ₚ (û +ₚ û))) )
    (ap₂ _,_
      ( ap₂ _+ₚ_ Rr.*-zeror (ap negₚ (ny-clean Q))
      ∙ +ₚ-idl (negₚ (con Q *ₚ (v̂ +ₚ v̂))) )
      ( ap₂ _+ₚ_ (*ₚ-idl (con R'.1r)) (ap negₚ Rr.*-zerol)
      ∙ ap (con R'.1r +ₚ_) neg-0ₚ
      ∙ Ro.+-idr ))
    where
      nx-clean : ∀ Q → ∂u (σz Q) *ₚ con R'.1r ≡ con Q *ₚ (û +ₚ û)
      nx-clean Q = Ro.*-idr ∙ ∂u-σz Q

      ny-clean : ∀ Q → con R'.1r *ₚ ∂v (σz Q) ≡ con Q *ₚ (v̂ +ₚ v̂)
      ny-clean Q = *ₚ-idl _ ∙ ∂v-σz Q
```
-->

## Reflection as Fermat stationarity, and the focusing theorem

The reflection law is the Euler–Lagrange equation of Fermat's
principle: among all broken paths from the source to a point past the
mirror, light takes the one of *stationary* optical length, and
first-order stationarity $\delta(\text{path}) = 0$ forces the reflected
ray to be $\operatorname{reflect}_n d$ for the surface normal $n$.
Because $n$ was obtained by synthetic differentiation of the mirror,
the whole construction lives at the differential (jet) level where the
theory is exact — the same level at which `Physics.Newton`{.Agda}
reaches $F = ma$ and `hamiltonian-mechanics`{.Agda} reaches
$\{H,H\} = 0$.

The focus, and the focal relation stated over the observable ring: $4q$
times the focal length is the unit.

```agda
  focus : ⌞ R ⌟ → Vec3
  focus F = foc (con F)

  Focal : ⌞ R ⌟ → ⌞ R ⌟ → Type ℓ
  Focal Q F = four (con Q) *ₚ con F ≡ Ro.1r
```

The **focusing theorem**: reflecting the axial ray in the paraboloid's
derived normal sends it, exactly, to a $4q$-multiple of the ray toward
the focus. It is the abstract identity `focusing-abs`{.Agda},
instantiated at the observable ring with the mirror variables and the
constants as atoms, precomposed with the derivation of the normal.

```agda
  focusing
    : ∀ Q F → Focal Q F
    → reflect incoming (normal Q)
    ≡ four (con Q) ·s (focus F -v σ Q)
  focusing Q F focal =
      ap (reflect incoming) (normal-value Q)
    ∙ focusing-abs û v̂ (con Q) (con F) focal
```

And its coordinate-free form: the reflected ray is parallel to the ray
toward the focus — the invariant way to say "focuses to a point".

```agda
  focusing-parallel
    : ∀ Q F → Focal Q F
    → cross (reflect incoming (normal Q)) (focus F -v σ Q)
    ≡ (con R'.0r , con R'.0r , con R'.0r)
  focusing-parallel Q F focal =
      ap (λ n → cross (reflect incoming n) (focus F -v σ Q)) (normal-value Q)
    ∙ focusing-parallel-abs û v̂ (con Q) (con F) focal
```

## What is and is not proven

The reflection law and the parabolic focusing identity are reached at
the **differential level**, synthetically: the surface normal is a real
cross product of synthetically-differentiated tangents, and the
focusing equation is an exact ring identity closed by the solver plus
one substitution of the focal relation — no limits, no division, no
reals. This is the same reach, and the same wall, as the oscillator's
Hamiltonian mechanics: the Euler–Lagrange *equation* of Fermat's
principle is synthetic and attained, but the optical *action integral*
$\int L$ — and with it the full variational bicomplex, the horizontal
differential $\mathrm{d}_H$, and any statement quantifying over *all*
light paths as an extremum of a functional — stays out of reach exactly
where integration does, needing the good open covers and the
real-numbers object the 1Lab does not yet have. We prove that the
paraboloid focuses; we do not (and here cannot) prove it is the *unique*
surface that does, as that is a global variational statement.
