<!--
```agda
open import Cat.Prelude

open import Algebra.Ring.Solver

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Physics.Heliostat.Optics
```
-->

```agda
module Physics.Heliostat.Bundle where
```

# The ray bundle as a set of germs, and its focusing spread {defines="ray-bundle bundle-variance focusing-spread koenig-huygens"}

A concentrator does not aim one ray; it aims a *bundle*. The reward that
trains a heliostat controller — how tightly the reflected rays converge
on the target — is a **statistic of the bundle**: the mean landing
point (the *centroid*, where the beam is aimed) and the spread about it
(the *variance*, how blurred the focal spot is). This module records
the algebraic identity underlying that statistic — the
Koenig–Huygens / parallel-axis (Lagrange) variance decomposition — as
an exact ring identity, and its **permutation invariance**, which is the
sheaf-theoretic heart of the matter: a bundle is a *set* of ray germs,
carrying no order, so the score may only depend on the multiset. The
per-ray germ realisation is exactly the aiming germ of
`Physics.Heliostat.Sheaf`{.Agda}; here we supply the order-free-bundle
half.

Following the discipline of `Physics.Heliostat.Optics`{.Agda}, we work
**division-free** and over an **abstract** commutative ring. The variance
decomposition classically carries a $1/n$ in the centroid; we clear it
by keeping the sums unnormalised — the "centroid" enters only as the
*sum* $\sum_i x_i$, never as an average $\frac1n\sum_i x_i$ — so no
inverse of $n$ is ever needed. And, exactly as the focusing identity is
closed by the [[ring solver|commutative-ring]] `cring!`{.Agda} only over
an abstract ring where the solver sees the ring's own projections
$\{0r,1r,+,*,-\}$, our variance identities are proved once over an
abstract `S`{.Agda} and instantiated afterward. This is the same
abstract-then-instantiate discipline the oscillator uses for its Euler
defect and the optics uses for the crown identity.

**Conventions and honest scope.** Ray endpoints are vectors over a
commutative ring, reusing the `Vec3`{.Agda} toolkit of
`Physics.Heliostat.Optics.euclid`{.Agda}; the squared length is
$\lVert v\rVert^2 = \langle v,v\rangle$, written `dot v v`. The doubling
$2 = 1 + 1$ is `S.1r S.+ S.1r`, so no numeral literal is needed. We
treat the **fixed bundle size $n = 2$** — two ray endpoints $x, y$ —
which is exactly the regime where the Lagrange identity is a pure
polynomial identity in finitely many atoms, hence `cring!`'s wheelhouse.
The general-$n$ variance decomposition and its non-negativity need a
ring-valued finite sum $\sum_i$ over `Fin`{.Agda} together with its
permutation invariance, *and* an ordered-ring order to state "$\ge 0$";
neither is developed here, and the closing section says so precisely.

## The vector toolkit, reused

We open the abstract Euclidean layer of `Physics.Heliostat.Optics`{.Agda}
at an abstract commutative ring `S`{.Agda}. This is the exact ring at
which `euclid`{.Agda} is parametrised, so `cring! S`{.Agda} applies. The
members `Vec3`{.Agda}, `dot`{.Agda}, `_+v_`{.Agda}, `_-v_`{.Agda} are
those of the optics module, unchanged; the squared-length abbreviation
`sq`{.Agda} is the only new definition, and it is *manifestly a sum of
three squares* — the key to reading the spread statistic below as
non-negative content even without an order.

```agda
module bundle-variance {ℓ} (S : CRing ℓ) where
  open Physics.Heliostat.Optics.euclid S
  private module S = CRing-on (S .snd)

  sq : Vec3 → ⌞ S ⌟
  sq v = dot v v
```

## The Lagrange identity at n = 2

The variance decomposition rests on a single scalar fact. Writing the
general Lagrange identity
$$2\Bigl(n\sum_i x_i^2 - \bigl(\textstyle\sum_i x_i\bigr)^2\Bigr) \;=\; \sum_{i,j}(x_i - x_j)^2,$$
its $n = 2$ instance reads
$2\bigl(2(x_1^2+x_2^2) - (x_1+x_2)^2\bigr) = 2(x_1-x_2)^2$; cancelling
the shared factor $2$ — the step that keeps everything division-free —
leaves the atomic identity
$$2(x_1^2+x_2^2) - (x_1+x_2)^2 \;=\; (x_1-x_2)^2.$$
By hand: the left side is $2x_1^2+2x_2^2 - x_1^2 - 2x_1x_2 - x_2^2 =
x_1^2 - 2x_1x_2 + x_2^2 = (x_1-x_2)^2$. This is a pure polynomial
identity in the two atoms $x_1, x_2$, so it is a single `cring! S`{.Agda}
— exactly the shape of the oscillator's `square-growth`{.Agda}. We state
it, as the gotcha corpus insists, as a *named* lemma with a full explicit
signature, never inlined into an `ap`.

```agda
  lagrange-2-scalar
    : ∀ (x₁ x₂ : ⌞ S ⌟)
    → ((S.1r S.+ S.1r) S.* ((x₁ S.* x₁) S.+ (x₂ S.* x₂)))
        S.+ (S.- ((x₁ S.+ x₂) S.* (x₁ S.+ x₂)))
    ≡ (x₁ S.+ (S.- x₂)) S.* (x₁ S.+ (S.- x₂))
  lagrange-2-scalar x₁ x₂ = cring! S
```

## The spread, as a witnessed sum of squares

Lifting to vectors is componentwise: `dot`{.Agda}, `_+v_`{.Agda} and
`_-v_`{.Agda} all compute coordinatewise, so the vector Lagrange identity
follows from three scalar calls — but because `dot`, `_+v_`, `_-v_`
reduce definitionally, the *whole vector statement* is again one
`cring! S`{.Agda}: after the geometric operations unfold, the goal is a
scalar ring identity in the six coordinate atoms. The left side is
$2(\lVert x\rVert^2 + \lVert y\rVert^2) - \lVert x + y\rVert^2$ — twice
the sum of squared lengths minus the squared length of the sum, the
unnormalised **variance** of the two-point bundle — and it equals
$\lVert x - y\rVert^2 = $ `sq (x -v y)`, which is *manifestly a sum of
three squares*.

This is the load-bearing reading of the statistic. Over an ordered ring
one would feed the right-hand side to $\le$ to conclude the spread is
$\ge 0$; over a bare commutative ring the "non-negativity" content **is**
precisely the equation "the spread equals `sq (x -v y)`", a dot of a
vector with itself. We state the theorem as that equality — the honest,
ordering-free deliverable — and do not assert `0 ≤ spread`, which would
need an order the abstract `S`{.Agda} does not carry.

```agda
  spread-2 : Vec3 → Vec3 → ⌞ S ⌟
  spread-2 x y =
    ((S.1r S.+ S.1r) S.* (sq x S.+ sq y)) S.+ (S.- sq (x +v y))

  lagrange-2-vec
    : ∀ (x y : Vec3) → spread-2 x y ≡ sq (x -v y)
  lagrange-2-vec x y = cring! S
```

## Koenig–Huygens / parallel-axis, division-free

The parallel-axis theorem $\sum_i \lVert x_i\rVert^2 = n\lVert\mu\rVert^2
+ \sum_i\lVert x_i - \mu\rVert^2$ splits the total spread of a bundle into
a **centroid** term (where the beam points) and a **variance** term (how
blurred the spot is). At $n = 2$, cleared of the $1/n$ in $\mu$ by
multiplying through, it becomes
$$2\bigl(\lVert x\rVert^2 + \lVert y\rVert^2\bigr) \;=\; \lVert x + y\rVert^2 + \lVert x - y\rVert^2,$$
the ring-theoretic parallelogram law: `sq (x +v y)` is the centroid
term (the squared length of the *sum*, i.e. twice the centroid scaled by
$n$) and `sq (x -v y)` is the variance term (the spread of the previous
section). It is immediate from `lagrange-2-vec`{.Agda} by rearrangement,
and again one `cring! S`{.Agda} directly.

```agda
  parallel-axis-2
    : ∀ (x y : Vec3)
    → (S.1r S.+ S.1r) S.* (sq x S.+ sq y)
    ≡ sq (x +v y) S.+ sq (x -v y)
  parallel-axis-2 x y = cring! S
```

The heliostat's **focusing reward** at $n = 2$ is this total: the sum of
the centroid and variance terms, i.e. twice the sum of squared endpoint
lengths, kept in the division-free unnormalised form. Naming it fixes the
statistic whose permutation invariance is the point.

```agda
  reward-2 : Vec3 → Vec3 → ⌞ S ⌟
  reward-2 x y = sq (x +v y) S.+ sq (x -v y)
```

## Permutation invariance — the bundle is order-free

A bundle is a *set* of ray germs: swapping the two rays must not change
the score. At $n = 2$ the permutation group is a single transposition, so
invariance is the statement that each ingredient of the reward is
symmetric in $x, y$. Both the centroid term `sq (x +v y)`{.Agda} and the
variance term `sq (x -v y)`{.Agda} are symmetric — the former because
addition commutes, the latter because $\lVert x - y\rVert^2 =
\lVert y - x\rVert^2$ (the sign flips inside a square) — and both are pure
ring identities in the coordinate atoms, hence `cring! S`{.Agda}. We
state each as a named lemma, then assemble the reward's invariance from
them.

```agda
  centroid-swap-2 : ∀ (x y : Vec3) → sq (x +v y) ≡ sq (y +v x)
  centroid-swap-2 x y = cring! S

  spread-swap-2 : ∀ (x y : Vec3) → sq (x -v y) ≡ sq (y -v x)
  spread-swap-2 x y = cring! S

  reward-swap-2 : ∀ (x y : Vec3) → reward-2 x y ≡ reward-2 y x
  reward-swap-2 x y = ap₂ S._+_ (centroid-swap-2 x y) (spread-swap-2 x y)
```

This `reward-swap-2`{.Agda} is the load-bearing correctness property. It
is exactly the coherence datum required to descend the reward through a
multiset quotient: `Data.Finset`{.Agda} presents the free
commutative-idempotent monoid with a swap constructor `∷-swap`{.Agda},
and a function on `Finset`{.Agda} that respects `∷-swap`{.Agda} factors
through it — at $n = 2$ the `∷-swap`{.Agda}-coherence *is*
`reward-swap-2`{.Agda}. So the bundle score, being invariant under the
one transposition, is a function of the two-element multiset of ray
endpoints, not of the ordered pair. (We record the coherence datum here;
building the `Finset`{.Agda}-fold that would carry the reward through the
quotient for *general* $n$ needs a commutative-monoid fold into `S`{.Agda}
that the library does not ship — see below.)

## Where the bundle's germs live, and where its order-freedom lives

Two separate pieces of `Physics`{.Agda}'s topos apparatus meet in the ray
bundle, and it is worth keeping them apart. The **per-ray germ** — each
reflected ray as a germ of the aiming plot over the mirror probe — is
`Physics.Heliostat.Sheaf`{.Agda}'s `aiming-germ`{.Agda}, with
`germs-are-plots`{.Agda} identifying germ and plot over the formal site.
That is Schreiber's diagram (5): each ray endpoint is a plot of the line
by the mirror probe $\bA^2$, whose function ring *is* the optics
observable ring (`Obs-is-mirror-functions`{.Agda}), so the endpoints of a
two-ray bundle are two such germs and the reward is a function of their
`Vec3`{.Agda} coordinates.

The **order-freedom of the bundle as a set** is a *different* quotient. It
is not `Sheaf`{.Agda}'s germ quotient — which, over the discrete
neighbourhood structure of the formal site, is trivial: the section is its
own germ, and there is no multiset of rays anywhere in that module. The
genuine order-free structure is the multiset set-quotient of
`Data.Finset`{.Agda}, whose `∷-swap`{.Agda} constructor is exactly
reorder-invariance. The connection, honestly stated, is this: the
*germ realisation* of each ray comes from `Sheaf`{.Agda}
(`germs-are-plots`{.Agda}), while the *order-freedom* of the bundle comes
from the `∷-swap`{.Agda}-coherence `reward-swap-2`{.Agda} proved above.
They are two claims, and we keep them separate — the recon and
`Sheaf`{.Agda}'s own honest-scope section both warn against conflating the
trivial germ-locality quotient with the multiset quotient.

## What is and is not proven

We prove, over an **abstract commutative ring** and entirely
**division-free**, the exact algebra of the two-ray focusing statistic:
the Lagrange identity `lagrange-2-scalar`{.Agda}; the variance-as-spread
identity `lagrange-2-vec`{.Agda}, which exhibits the unnormalised
two-point variance `spread-2`{.Agda} as `sq (x -v y)`{.Agda} — a manifest
sum of three squares, the ordering-free content of "the spread is
non-negative"; the Koenig–Huygens / parallel-axis decomposition
`parallel-axis-2`{.Agda} splitting the reward into centroid and variance
terms without ever dividing by $n$; and the **permutation invariance**
`reward-swap-2`{.Agda} that makes the bundle score a function of the
two-element *multiset* of ray germs — the `∷-swap`{.Agda}-coherence datum
that connects, in prose, to `Data.Finset`{.Agda}'s multiset quotient and,
per-ray, to `Physics.Heliostat.Sheaf`{.Agda}'s `germs-are-plots`{.Agda}.
Every identity above is a single `cring! S`{.Agda}; there are **no
postulates**.

What we do **not** prove, and honestly cannot at this scope:

- **General $n$.** The Lagrange/parallel-axis identity for arbitrary
  bundle size $n$ needs a ring-valued finite sum $\sum_i$ over
  `Fin n`{.Agda} (or a `Finset`{.Agda}-fold into a commutative monoid),
  a double-sum reindexing $\sum_{i,j} = \sum_{j,i}$, and an induction
  discharging the identity across the fold. The 1Lab ships **no**
  ring-valued indexed sum — `Data.Fin.Closure`{.Agda}'s `sum`{.Agda} is
  cardinality-valued (into `Nat`{.Agda}, for counting finite types), not
  a fold into a ring, and there is no bigop machinery. `Data.Finset`{.Agda}
  has the right multiset quotient (`∷-swap`{.Agda}, `∷-dup`{.Agda},
  `squash`{.Agda}) and a recursor `Finset-rec`{.Agda}, but no shipped
  commutative-monoid fold; building one and proving it respects
  `∷-swap`{.Agda}/`∷-dup`{.Agda} against `S`{.Agda}'s laws is a genuine
  piece of infrastructure, not an API call. So general-$n$ permutation
  invariance and the general variance decomposition are well-posed future
  work, blocked on a missing $\sum$-over-`Fin`-into-a-`CRing` and its
  invariance.

- **Non-negativity as an inequality.** We witness the spread as a sum of
  squares (`lagrange-2-vec`{.Agda}), but we do **not** assert
  `0 ≤ spread-2 x y`: the abstract `S`{.Agda} carries no order, and the
  reading guide `Physics`{.Agda} lists the ordered real-numbers structure
  — multiplication of Dedekind cuts and the constructive order it would
  induce — among the missing analytic infrastructure. Over an ordered
  ring the sum-of-squares equality would immediately give the inequality;
  here the equality *is* the deliverable.

These are the same walls that bound every module in this development: no
integration, no reals-with-multiplication, no shrinking germs. Within
them, the two-ray focusing statistic — its Koenig–Huygens decomposition
and its order-freedom — is exact ring algebra, closed by the solver, with
zero postulates.
