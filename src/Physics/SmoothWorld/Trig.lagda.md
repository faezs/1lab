<!--
```agda
open import 1Lab.Prelude hiding (_+_ ; _*_ ; _-_ ; ∣_∣)

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Physics.SmoothWorld
```
-->

```agda
module Physics.SmoothWorld.Trig where
```

# The infinitesimal trigonometric identities {defines="sin-epsilon cos-epsilon"}

In Bell's smooth world the two headline transcendental identities of
synthetic differential geometry are the *microscopic* trigonometric
laws
$$
  \sin\varepsilon = \varepsilon, \qquad \cos\varepsilon = 1
  \qquad (\varepsilon^2 = 0).
$$
They say that, to first order, sine is the identity and cosine is
constant — the infinitesimal shadow of $\sin' = \cos$, $\cos' =
-\sin$, evaluated at the origin. Bell derives them (*A Primer of
Infinitesimal Analysis*, §2) as a one-line corollary of the
**fundamental equation** $f(x + \varepsilon) = f(x) + \varepsilon\,
f'(x)$ once the origin values $\sin 0 = 0$, $\sin' 0 = 1$, $\cos 0 =
1$, $\cos' 0 = 0$ are known.

This module is honest in exactly the register [[the smooth
world|smooth-infinitesimal-analysis]] already operates in. It makes
**no** analytic claim that such functions $\sin,\cos$ *exist* — their
construction (power series over the completed reals) is the separate
business of the special-functions task. Here $\sin$ and $\cos$ are
abstract functions on the line, and their four origin facts are taken
as explicit **module parameters**, precisely as `Microaffineness`,
`Constancy` and `has-inverses` are parameters upstream. Everything
below is then genuinely proven, with zero postulates: given those four
hypotheses, the microscopic identities are theorems.

<!--
```agda
module _ {ℓ} (R : CRing ℓ) (micro : Microaffineness R) where
  private
    module R = CRing-on (R .snd)
  open Bell R micro
```
-->

We work over an arbitrary model `(R , micro)` of the Microaffineness
axiom and re-open `Bell R micro` — the same parameters as
[[`SmoothWorld`|smooth-infinitesimal-analysis]], never editing it — to
bring `fundamental`{.Agda}, `deriv`{.Agda}, the nilsquares `𝔻`{.Agda}
and the inclusion `∣_∣`{.Agda} into scope.

## The boundary data

The four origin facts. Bundling them as a record is a convenience for
callers that will eventually discharge all four from a genuine
construction of the trigonometric functions; the identities themselves
take them apart again.

```agda
  record SinCosBoundary
    (sin cos : ⌞ R ⌟ → ⌞ R ⌟) : Type ℓ where
    field
      sin0  : sin R.0r ≡ R.0r
      dsin0 : deriv sin R.0r ≡ R.1r
      cos0  : cos R.0r ≡ R.1r
      dcos0 : deriv cos R.0r ≡ R.0r
```

## The identities

Take $\sin,\cos$ with their four origin boundary values as
parameters.

```agda
  module _ (sin cos : ⌞ R ⌟ → ⌞ R ⌟)
           (sin0  : sin R.0r ≡ R.0r) (dsin0 : deriv sin R.0r ≡ R.1r)
           (cos0  : cos R.0r ≡ R.1r) (dcos0 : deriv cos R.0r ≡ R.0r) where
```

For $\sin\varepsilon = \varepsilon$ we rewrite $\varepsilon = 0 +
\varepsilon$ under $\sin$, fire the fundamental equation at the origin
to get $\sin 0 + \varepsilon\cdot\sin' 0$, substitute $\sin 0 = 0$ and
$\sin' 0 = 1$, and let the [[ring solver|ring-solver]] collapse $0 +
\varepsilon\cdot 1$ to $\varepsilon$.

```agda
    sin-ε : (ε : 𝔻) → sin ∣ ε ∣ ≡ ∣ ε ∣
    sin-ε ε =
      sin ∣ ε ∣
        ≡⟨ ap sin (sym R.+-idl) ⟩
      sin (R.0r R.+ ∣ ε ∣)
        ≡⟨ fundamental sin R.0r ε ⟩
      sin R.0r R.+ (∣ ε ∣ R.* deriv sin R.0r)
        ≡⟨ ap₂ (λ a b → a R.+ (∣ ε ∣ R.* b)) sin0 dsin0 ⟩
      R.0r R.+ (∣ ε ∣ R.* R.1r)
        ≡⟨ cring! R ⟩
      ∣ ε ∣ ∎
```

For $\cos\varepsilon = 1$ the argument is identical, ending at $1 +
\varepsilon\cdot 0 = 1$.

```agda
    cos-ε : (ε : 𝔻) → cos ∣ ε ∣ ≡ R.1r
    cos-ε ε =
      cos ∣ ε ∣
        ≡⟨ ap cos (sym R.+-idl) ⟩
      cos (R.0r R.+ ∣ ε ∣)
        ≡⟨ fundamental cos R.0r ε ⟩
      cos R.0r R.+ (∣ ε ∣ R.* deriv cos R.0r)
        ≡⟨ ap₂ (λ a b → a R.+ (∣ ε ∣ R.* b)) cos0 dcos0 ⟩
      R.1r R.+ (∣ ε ∣ R.* R.0r)
        ≡⟨ cring! R ⟩
      R.1r ∎
```

The same two proofs, packaged to run off a `SinCosBoundary`{.Agda}
record instead of four loose parameters.

```agda
  module _ (sin cos : ⌞ R ⌟ → ⌞ R ⌟) (bd : SinCosBoundary sin cos) where
    open SinCosBoundary bd

    sin-ε′ : (ε : 𝔻) → sin ∣ ε ∣ ≡ ∣ ε ∣
    sin-ε′ = sin-ε sin cos sin0 dsin0 cos0 dcos0

    cos-ε′ : (ε : 𝔻) → cos ∣ ε ∣ ≡ R.1r
    cos-ε′ = cos-ε sin cos sin0 dsin0 cos0 dcos0
```
