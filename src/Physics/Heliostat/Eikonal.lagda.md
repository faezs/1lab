<!--
```agda
open import Cat.Prelude

open import Algebra.Ring.Solver
open import Algebra.Ring.Commutative

open import Physics.Heliostat.Optics
```
-->

```agda
module Physics.Heliostat.Eikonal where
```

# The eikonal: wavefronts and equal optical path {defines="eikonal wavefront equal-optical-path"}

The [[reflection law and parabolic focusing|parabolic-focusing]] were
reached at the *infinitesimal* level: the surface normal is a synthetic
derivative, and the specular direction is the first-order stationary
point of Fermat's principle. That is the ray picture. The complementary
*finite* picture is the **eikonal** — the optical-path-length (or phase)
field $S$ whose level sets are the **wavefronts**, and whose gradient is
the ray direction. In the language of Giotopoulos and Sati's *Field
Theory via Higher Geometry I* [@GiotopoulosSati:FieldTheory], $S$ is a
scalar field, a map into the line, and Fermat's principle is the
statement that the total optical path from a common incoming wavefront
to the focus is *extremal*, hence — for the perfect focuser — *constant*.

Constant optical path is what "focuses in phase" means: a paraboloid
takes an incoming plane wavefront and returns a *spherical* wavefront
converging on the focus, every ray arriving with the same accumulated
path length. Classically this is the parabola's **focus–directrix**
definition: every surface point is equidistant from the focus
$F = (0,0,f)$ and the directrix plane $z = -f$. We recover exactly that,
as a commutative-ring identity, and it is the finite counterpart of the
infinitesimal reflection law — the two orders of the same variational
principle.

We work over the same abstract commutative ring as `euclid`{.Agda},
reusing its Euclidean vector toolkit, and stay division- and
square-root-free by stating everything through the **squared** distance
`dist²`{.Agda}: over a general ring there is no norm, but there is an
inner product, and the geometry lives entirely in it.

```agda
module wavefront {ℓ} (S : CRing ℓ) where
  open Physics.Heliostat.Optics.euclid S
  private module S = CRing-on (S .snd)

  sq : ⌞ S ⌟ → ⌞ S ⌟
  sq x = x S.* x

  dist² : Vec3 → Vec3 → ⌞ S ⌟
  dist² p q = dot (p -v q) (p -v q)
```

The mirror height $z = q(u^2+v^2)$ above the vertex; the distance from a
surface point *down* to the directrix plane $z = -f$ is then $z + f =
q(u^2+v^2) + f$.

```agda
  height : ⌞ S ⌟ → ⌞ S ⌟ → ⌞ S ⌟ → ⌞ S ⌟
  height a b c = c S.* ((a S.* a) S.+ (b S.* b))
```

## Focus–directrix equidistance is the eikonal

Here is the finite focusing theorem: the squared distance from any
surface point to the focus equals the squared distance to the directrix
plane. Since the directrix distance is $q(u^2+v^2) + f$, this reads
$\operatorname{dist}^2(\sigma, F) = (q(u^2+v^2) + f)^2$, and it holds
exactly when the focal relation $4qf = 1$ does. The proof is the same
`euclid`{.Agda}-style ring algebra: the difference of the two sides is
$(u^2+v^2)(4qf - 1)$, which the focal relation kills — one substitution
between two applications of the solver, no square roots, no division.

```agda
  equal-path
    : ∀ a b c g → four c S.* g ≡ S.1r
    → dist² (surf a b c) (foc g) ≡ sq (height a b c S.+ g)
```

<!--
```agda
  equal-path a b c g focal =
    sym
      ( eik-decomp
      ∙ ap (λ z → dist² (surf a b c) (foc g) S.+ (P S.* z)) focal-zero
      ∙ eik-collapse )
    where
      P : ⌞ S ⌟
      P = (a S.* a) S.+ (b S.* b)

      -- pure ring identity: the sphere/directrix difference is P·(4qf − 1)
      eik-decomp
        : sq (height a b c S.+ g)
        ≡ dist² (surf a b c) (foc g) S.+ (P S.* ((four c S.* g) S.+ (S.- S.1r)))
      eik-decomp = cring! S

      -- the focal relation makes that factor vanish
      one-minus-one : S.1r S.+ (S.- S.1r) ≡ S.0r
      one-minus-one = cring! S

      focal-zero : (four c S.* g) S.+ (S.- S.1r) ≡ S.0r
      focal-zero = ap (S._+ (S.- S.1r)) focal ∙ one-minus-one

      eik-collapse
        : dist² (surf a b c) (foc g) S.+ (P S.* S.0r)
        ≡ dist² (surf a b c) (foc g)
      eik-collapse = cring! S
```
-->

## The reflected wavefront is a sphere

A **wavefront** through a point is the level set of the optical-path
field; the reflected wavefront of an axial plane wave is the sphere of
squared radius $r^2$ about the focus, $\{\,p \mid \operatorname{dist}^2(p,
F) = r^2\,\}$. The theorem `equal-path`{.Agda} says precisely that each
surface point sits on such a sphere, with radius the directrix distance:
the mirror is *isochronous*. (Adding the incoming leg $z_0 - z$ to the
reflected leg $z + f$ gives the constant total $z_0 + f$, independent of
$(u,v)$ — but that sum needs an honest square root to take the distances
themselves, so we state the exact, algebraic, squared form.)

```agda
  on-wavefront : Vec3 → ⌞ S ⌟ → Vec3 → Type ℓ
  on-wavefront centre r² p = dist² p centre ≡ r²

  mirror-on-sphere
    : ∀ a b c g → four c S.* g ≡ S.1r
    → on-wavefront (foc g) (sq (height a b c S.+ g)) (surf a b c)
  mirror-on-sphere = equal-path
```

## What is and is not proven

The finite focusing statement — focus–directrix equidistance, the
mirror as an isochronous surface, the reflected wavefront as a sphere —
is an exact ring identity, the finite complement to the infinitesimal
reflection law of `Physics.Heliostat.Optics`{.Agda}. Together they are
the two orders of Fermat's principle: $\delta(\text{path}) = 0$ at the
ray level, constant path at the wavefront level. What remains beyond
reach is the same boundary as everywhere in this development: the
**eikonal equation** $|\nabla S|^2 = n^2$ as a genuine partial
differential equation on the field $S$ — a statement about *all* of
space rather than the surface — and the phase *integral* itself both
need the horizontal differential $\mathrm{d}_H$ of the variational
bicomplex and a real-numbers object with a square root, neither of which
the 1Lab yet has. We prove that the paraboloid is equidistant from focus
and directrix; we do not integrate the eikonal.
