<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative
open import Data.Real.Complete using (le→sub ; sub→le)

open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Integral where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  interᴿ : ∀ a b c d → (a R.+ b) R.+ (c R.+ d) ≡ (a R.+ c) R.+ (b R.+ d)
  interᴿ a b c d = cring! S

  mul-sub : ∀ c x y → c R.* (y R.+ (R.- x)) ≡ (c R.* y) R.+ (R.- (c R.* x))
  mul-sub c x y = cring! S

  neg-sub : ∀ A B → R.- (A R.+ (R.- B)) ≡ B R.+ (R.- A)
  neg-sub A B = cring! S

  tele3 : ∀ a b c → a R.+ (R.- c) ≡ (a R.+ (R.- b)) R.+ (b R.+ (R.- c))
  tele3 a b c = cring! S

  rearr
    : ∀ a b c d
    → (a R.+ b) R.+ (R.- (c R.+ d)) ≡ (a R.+ (R.- c)) R.+ (b R.+ (R.- d))
  rearr a b c d = cring! S

  assoc3 : ∀ a b → (a R.+ b) R.+ b ≡ a R.+ (b R.+ b)
  assoc3 a b = cring! S

private module RI = Identities ℝ-comm

private
  ratℝ-mono : ∀ {p q} → p ≤ q → ratℝ p ≤ᴿ ratℝ q
  ratℝ-mono p≤q r r<p = <-≤-trans r<p p≤q
```
-->

# A Riemann integral over the honest reals {defines="riemann-integral"}

Synthetic differential geometry takes *integration* as an axiom: it
posits, for every function on an interval, a primitive with the
expected boundary behaviour. Over the [[honest Dedekind
reals|dedekind-real]] we can instead **construct** the integral, as
the limit of dyadic Riemann sums, and recover its defining
properties as theorems. The uniform modulus of continuity that a
constructive Riemann integral needs is exactly the
[[bound data|bounded-smooth-function]] carried by the
[[bounded-smooth functions|bounded-smooth-function]]
$\mathrm{Smooth}^{+}$ — so the integral is defined for every such
function, with no appeal to limits beyond
[[completeness|real-completeness]].

This module builds the finite dyadic Riemann sums and their exact
algebra unconditionally, then — behind a single, clearly delimited
hypothesis that those sums **converge** (the one genuine analytic
input, discussed at the end) — assembles the integral operator
together with its linearity and monotonicity.

## Some order limits

A real bounded below by every $-\varepsilon$ is nonnegative: the
one-sided [[Archimedean squeeze|real-lattice]] at the level of the
lower cuts.

```agda
nonneg-limit
  : ∀ {D} → (∀ ε → 0 < ε → ratℝ (-ℚ ε) ≤ᴿ D) → 0ᴿ ≤ᴿ D
nonneg-limit {D} h q q<0 = h ε 0<ε q mem
  where
  0<-q : 0 < (-ℚ q)
  0<-q = <-resp refl (+ℚ-idl (-ℚ q)) (<→positive-diff q<0)

  ε : Ratio
  ε = half (-ℚ q)

  0<ε : 0 < ε
  0<ε = half-pos 0<-q

  mem : q < (-ℚ ε)
  mem = <-resp (negℚ-invol q) refl (negℚ-anti-< (half-lt 0<-q))
```

From a two-sided modulus bound $\lvert I - R\rvert \le \varepsilon$
we read off the one-sided estimates $I \le R + \varepsilon$ and
$R \le I + \varepsilon$, the additive bookkeeping that limits of
Riemann sums run on.

```agda
close-upper
  : ∀ {I R} ε → absᴿ (I +ᴿ (-ᴿ R)) ≤ᴿ ratℝ ε → I ≤ᴿ (R +ᴿ ratℝ ε)
close-upper {I} {R} ε h =
  sub→le I R (ratℝ ε) (abs-out-l {I +ᴿ (-ᴿ R)} {ratℝ ε} h)

close-lower
  : ∀ {I R} ε → absᴿ (I +ᴿ (-ᴿ R)) ≤ᴿ ratℝ ε → R ≤ᴿ (I +ᴿ ratℝ ε)
close-lower {I} {R} ε h = sub→le R I (ratℝ ε)
  (subst₂ _≤ᴿ_ (RI.neg-sub I R) (-ᴿ-invol (ratℝ ε))
    (negᴿ-anti { -ᴿ ratℝ ε} {I +ᴿ (-ᴿ R)}
      (abs-out-r {I +ᴿ (-ᴿ R)} {ratℝ ε} h)))
```

## The dyadic partition

The mesh of the $2^{n}$-fold partition of $[a,b]$ is $(b-a)$ halved
$n$ times; the $i$-th node is $a + i \cdot h_{n}$; and a rational is
lifted to the one-dimensional argument tuple by the constant map.

```agda
pow2 : Nat → Nat
pow2 zero    = 1
pow2 (suc n) = pow2 n Nat.+ pow2 n

msh : Ratio → Ratio → Nat → Ratio
msh a b zero    = b +ℚ (-ℚ a)
msh a b (suc n) = half (msh a b n)

dyadic : (a b : Ratio) → Nat → Nat → Ratio
dyadic a b n i = a +ℚ (nℚ i *ℚ msh a b n)

pt : Ratio → (Fin 1 → ℝ)
pt q _ = ratℝ q
```

## The Riemann sum

A finite sum of reals, indexed by fuel, and the left-tagged Riemann
sum: $2^{n}$ equal pieces, each of width $h_{n}$, tagged at its left
node.

```agda
sumᴿ : Nat → (Nat → ℝ) → ℝ
sumᴿ zero    t = 0ᴿ
sumᴿ (suc k) t = sumᴿ k t +ᴿ t k

Riemann : (f : Fun 1) (a b : Ratio) → Nat → ℝ
Riemann f a b n =
  sumᴿ (pow2 n) (λ i → ratℝ (msh a b n) *ᴿ f (pt (dyadic a b n i)))
```

## Exact algebra of the Riemann sums

Finite sums are termwise linear, and the width factors through the
[[distributive law|real-multiplication]], so the Riemann sum of a
pointwise sum splits exactly.

```agda
sumᴿ-add
  : ∀ K (s t : Nat → ℝ)
  → sumᴿ K (λ i → s i +ᴿ t i) ≡ sumᴿ K s +ᴿ sumᴿ K t
sumᴿ-add zero    s t = sym (+ᴿ-idr 0ᴿ)
sumᴿ-add (suc K) s t =
    ap (_+ᴿ (s K +ᴿ t K)) (sumᴿ-add K s t)
  ∙ RI.interᴿ (sumᴿ K s) (sumᴿ K t) (s K) (t K)

Riemann-add
  : ∀ (f g : Fun 1) (a b : Ratio) (n : Nat)
  → Riemann (λ x → f x +ᴿ g x) a b n ≡ Riemann f a b n +ᴿ Riemann g a b n
Riemann-add f g a b n =
    ap (sumᴿ (pow2 n))
      (funext λ i → *ᴿ-distribˡ (ratℝ (msh a b n))
        (f (pt (dyadic a b n i))) (g (pt (dyadic a b n i))))
  ∙ sumᴿ-add (pow2 n)
      (λ i → ratℝ (msh a b n) *ᴿ f (pt (dyadic a b n i)))
      (λ i → ratℝ (msh a b n) *ᴿ g (pt (dyadic a b n i)))
```

Multiplication by a nonnegative real is monotone — the difference is
a nonnegative product — so the Riemann sum is monotone in its
integrand whenever the mesh is nonnegative, i.e. whenever $a \le b$.

```agda
scaleᴿ-mono
  : ∀ {c x y} → 0ᴿ ≤ᴿ c → x ≤ᴿ y → (c *ᴿ x) ≤ᴿ (c *ᴿ y)
scaleᴿ-mono {c} {x} {y} 0≤c x≤y =
  diff-nonneg→≤ᴿ {c *ᴿ x} {c *ᴿ y}
    (subst (0ᴿ ≤ᴿ_) (RI.mul-sub c x y)
      (*ᴿ-nonneg c (y +ᴿ (-ᴿ x)) 0≤c (≤ᴿ→diff-nonneg {x} {y} x≤y)))

private
  0≤half : ∀ {x} → 0 ≤ x → 0 ≤ half x
  0≤half {x} 0≤x = ≤-resp (*ℚ-zerol (invℚ 2)) refl
    (*ℚ-preserves-≤r (invℚ 2) 0≤x (<-weaken (invℚ-pos {2} 0<2)))
    where
    0<2 : 0 < 2
    0<2 = decide!

  msh-nonneg-ℚ : ∀ a b n → a ≤ b → 0 ≤ msh a b n
  msh-nonneg-ℚ a b zero    a≤b =
    ≤-resp (+ℚ-invr a) refl (+ℚ-preserves-≤ a≤b (≤-refl { -ℚ a}))
  msh-nonneg-ℚ a b (suc n) a≤b = 0≤half (msh-nonneg-ℚ a b n a≤b)

msh-nonneg : ∀ a b n → a ≤ b → 0ᴿ ≤ᴿ ratℝ (msh a b n)
msh-nonneg a b n a≤b = ratℝ-mono {0} {msh a b n} (msh-nonneg-ℚ a b n a≤b)

sumᴿ-mono
  : ∀ K (s t : Nat → ℝ) → (∀ i → s i ≤ᴿ t i) → sumᴿ K s ≤ᴿ sumᴿ K t
sumᴿ-mono zero    s t h = ≤ᴿ-refl {0ᴿ}
sumᴿ-mono (suc K) s t h =
  +ᴿ-mono {sumᴿ K s} {sumᴿ K t} {s K} {t K} (sumᴿ-mono K s t h) (h K)

Riemann-mono
  : ∀ (f g : Fun 1) (a b : Ratio) (n : Nat)
  → a ≤ b → (∀ x → f x ≤ᴿ g x)
  → Riemann f a b n ≤ᴿ Riemann g a b n
Riemann-mono f g a b n a≤b fg = sumᴿ-mono (pow2 n) _ _
  (λ i → scaleᴿ-mono {ratℝ (msh a b n)}
    {f (pt (dyadic a b n i))} {g (pt (dyadic a b n i))}
    (msh-nonneg a b n a≤b) (fg (pt (dyadic a b n i))))
```

## Convergence to a limit, and its uniqueness

We say a real $I$ is the **Riemann limit** of $f$ on $[a,b]$ when,
for every slack $\varepsilon$, all sufficiently fine Riemann sums lie
within $\varepsilon$ of $I$. Two Riemann limits of the same
integrand coincide: their difference is bounded by every
$\varepsilon$, hence squeezed to zero.

```agda
is-Rlim : (f : Fun 1) (a b : Ratio) → ℝ → Type
is-Rlim f a b I =
  ∀ ε → 0 < ε →
    ∥ Σ Nat (λ N → (n : Nat) → N Nat.≤ n
      → absᴿ (I +ᴿ (-ᴿ Riemann f a b n)) ≤ᴿ ratℝ ε) ∥

private
  ≤ᴿ-prop : ∀ {a b : ℝ} → is-prop (a ≤ᴿ b)
  ≤ᴿ-prop {a} {b} = Π-is-hlevel 1 λ q → Π-is-hlevel 1 λ _ →
    (b .lower q) .is-tr

  le-plusl : ∀ x y → x Nat.≤ x Nat.+ y
  le-plusl zero    y = Nat.0≤x
  le-plusl (suc x) y = Nat.s≤s (le-plusl x y)

  le-plusr : ∀ x y → y Nat.≤ x Nat.+ y
  le-plusr x y = subst (y Nat.≤_) (Nat.+-commutative y x) (le-plusl y x)

  half-rat : ∀ ε → (ratℝ (half ε) +ᴿ ratℝ (half ε)) ≡ ratℝ ε
  half-rat ε = sym (ratℝ-+ (half ε) (half ε)) ∙ ap ratℝ (half-sum ε)
```

The triangle estimate, packaged once: if $I$ and $R$ are each within
$\tfrac{\varepsilon}{2}$ of a common sum $S$, then $I$ and $R$ are
within $\varepsilon$.

```agda
private
  merge-close
    : ∀ {I S R} ε
    → absᴿ (I +ᴿ (-ᴿ S)) ≤ᴿ ratℝ (half ε)
    → absᴿ (R +ᴿ (-ᴿ S)) ≤ᴿ ratℝ (half ε)
    → absᴿ (I +ᴿ (-ᴿ R)) ≤ᴿ ratℝ ε
  merge-close {I} {S} {R} ε hI hR =
    subst (λ z → absᴿ z ≤ᴿ ratℝ ε) (sym (RI.tele3 I S R))
      (subst (absᴿ ((I +ᴿ (-ᴿ S)) +ᴿ (S +ᴿ (-ᴿ R))) ≤ᴿ_) (half-rat ε)
        (abs-sum {I +ᴿ (-ᴿ S)} {S +ᴿ (-ᴿ R)}
          {ratℝ (half ε)} {ratℝ (half ε)}
          hI
          (subst (λ z → absᴿ z ≤ᴿ ratℝ (half ε)) (RI.neg-sub R S)
            (abs-neg {R +ᴿ (-ᴿ S)} {ratℝ (half ε)} hR))))

Rlim-unique
  : ∀ f a b I I' → is-Rlim f a b I → is-Rlim f a b I' → I ≡ I'
Rlim-unique f a b I I' hI hI' = diff-zero→≡ {I} {I'}
  (squeeze (I +ᴿ (-ᴿ I'))
    λ ε 0<ε →
        abs-out-l {I +ᴿ (-ᴿ I')} {ratℝ ε} (bound ε 0<ε)
      , subst (_≤ᴿ (I +ᴿ (-ᴿ I'))) (ratℝ-neg ε)
          (abs-out-r {I +ᴿ (-ᴿ I')} {ratℝ ε} (bound ε 0<ε)))
  where
  bound : ∀ ε → 0 < ε → absᴿ (I +ᴿ (-ᴿ I')) ≤ᴿ ratℝ ε
  bound ε 0<ε =
    ∥-∥-rec (≤ᴿ-prop {absᴿ (I +ᴿ (-ᴿ I'))} {ratℝ ε})
      (λ (N , bN) →
        ∥-∥-rec (≤ᴿ-prop {absᴿ (I +ᴿ (-ᴿ I'))} {ratℝ ε})
          (λ (N' , bN') →
            let n  = N Nat.+ N'
                sI  = bN  n (le-plusl N N')
                sI' = bN' n (le-plusr N N')
            in merge-close {I} {Riemann f a b n} {I'} ε sI sI')
          (hI' (half ε) (half-pos 0<ε)))
      (hI (half ε) (half-pos 0<ε))
```

## The integral, its linearity and monotonicity

Everything from here on is stated **relative to convergence of the
Riemann sums**: the module below takes, as an explicit hypothesis,
an assignment `∫₀`{.Agda} of a limit to every bounded-smooth
integrand together with a proof `∫-converges`{.Agda} that it *is* the
Riemann limit. This isolates the sole analytic input — that the
dyadic Riemann sums form a Cauchy sequence — from the algebra that
consumes it. Discharging it is the geometric convergence estimate
discussed under *what remains* below.

```agda
module Integration
  (∫₀ : (f : Fun 1) → Smooth⁺ 1 f → (a b : Ratio) → ℝ)
  (∫-converges
    : (f : Fun 1) (sf : Smooth⁺ 1 f) (a b : Ratio)
    → is-Rlim f a b (∫₀ f sf a b))
  where

  ∫ : (f : Fun 1) → Smooth⁺ 1 f → (a b : Ratio) → ℝ
  ∫ = ∫₀
```

The Riemann sums are termwise additive, so the sum of the two
integrals is again a Riemann limit of the sum integrand; uniqueness
then forces the integral to be additive.

```agda
  ∫-linear
    : (f g : Fun 1) (sf : Smooth⁺ 1 f) (sg : Smooth⁺ 1 g) (a b : Ratio)
    → ∫ (λ x → f x +ᴿ g x) (smooth⁺-add sf sg) a b
    ≡ ∫ f sf a b +ᴿ ∫ g sg a b
  ∫-linear f g sf sg a b =
    Rlim-unique (λ x → f x +ᴿ g x) a b
      (∫ (λ x → f x +ᴿ g x) (smooth⁺-add sf sg) a b)
      (∫ f sf a b +ᴿ ∫ g sg a b)
      (∫-converges (λ x → f x +ᴿ g x) (smooth⁺-add sf sg) a b)
      sum-is-Rlim
    where
    If Ig : ℝ
    If = ∫ f sf a b
    Ig = ∫ g sg a b

    sum-is-Rlim : is-Rlim (λ x → f x +ᴿ g x) a b (If +ᴿ Ig)
    sum-is-Rlim ε 0<ε =
      ∥-∥-rec squash
        (λ (Nf , bf) →
          ∥-∥-rec squash
            (λ (Ng , bg) → inc (Nf Nat.+ Ng , λ n N≤n →
              let nf = bf n (Nat.≤-trans (le-plusl Nf Ng) N≤n)
                  ng = bg n (Nat.≤-trans (le-plusr Nf Ng) N≤n)
              in goal n nf ng))
            (∫-converges g sg a b (half ε) (half-pos 0<ε)))
        (∫-converges f sf a b (half ε) (half-pos 0<ε))
      where
      goal
        : ∀ n
        → absᴿ (If +ᴿ (-ᴿ Riemann f a b n)) ≤ᴿ ratℝ (half ε)
        → absᴿ (Ig +ᴿ (-ᴿ Riemann g a b n)) ≤ᴿ ratℝ (half ε)
        → absᴿ ((If +ᴿ Ig) +ᴿ (-ᴿ Riemann (λ x → f x +ᴿ g x) a b n))
          ≤ᴿ ratℝ ε
      goal n nf ng =
        subst (λ z → absᴿ ((If +ᴿ Ig) +ᴿ (-ᴿ z)) ≤ᴿ ratℝ ε)
          (sym (Riemann-add f g a b n))
          (subst (λ z → absᴿ z ≤ᴿ ratℝ ε)
            (sym (RI.rearr If Ig Rf Rg))
            (subst (absᴿ ((If +ᴿ (-ᴿ Rf)) +ᴿ (Ig +ᴿ (-ᴿ Rg))) ≤ᴿ_)
              (half-rat ε)
              (abs-sum {If +ᴿ (-ᴿ Rf)} {Ig +ᴿ (-ᴿ Rg)}
                {ratℝ (half ε)} {ratℝ (half ε)} nf ng)))
        where
        Rf Rg : ℝ
        Rf = Riemann f a b n
        Rg = Riemann g a b n
```

Monotone integrands have monotone Riemann sums; combined with the
one-sided modulus estimates and the one-sided squeeze, the integral
is monotone.

```agda
  ∫-mono
    : (f g : Fun 1) (sf : Smooth⁺ 1 f) (sg : Smooth⁺ 1 g) (a b : Ratio)
    → a ≤ b → (∀ x → f x ≤ᴿ g x)
    → ∫ f sf a b ≤ᴿ ∫ g sg a b
  ∫-mono f g sf sg a b a≤b fg =
    diff-nonneg→≤ᴿ {If} {Ig} (nonneg-limit {Ig +ᴿ (-ᴿ If)} lower-bd)
    where
    If Ig : ℝ
    If = ∫ f sf a b
    Ig = ∫ g sg a b

    lower-bd : ∀ ε → 0 < ε → ratℝ (-ℚ ε) ≤ᴿ (Ig +ᴿ (-ᴿ If))
    lower-bd ε 0<ε =
      ∥-∥-rec (≤ᴿ-prop {ratℝ (-ℚ ε)} {Ig +ᴿ (-ᴿ If)})
        (λ (Nf , bf) →
          ∥-∥-rec (≤ᴿ-prop {ratℝ (-ℚ ε)} {Ig +ᴿ (-ᴿ If)})
            (λ (Ng , bg) →
              let n  = Nf Nat.+ Ng
                  sf' = bf n (le-plusl Nf Ng)
                  sg' = bg n (le-plusr Nf Ng)
              in from-chain n sf' sg')
            (∫-converges g sg a b (half ε) (half-pos 0<ε)))
        (∫-converges f sf a b (half ε) (half-pos 0<ε))
      where
      from-chain
        : ∀ n
        → absᴿ (If +ᴿ (-ᴿ Riemann f a b n)) ≤ᴿ ratℝ (half ε)
        → absᴿ (Ig +ᴿ (-ᴿ Riemann g a b n)) ≤ᴿ ratℝ (half ε)
        → ratℝ (-ℚ ε) ≤ᴿ (Ig +ᴿ (-ᴿ If))
      from-chain n sf' sg' =
        subst₂ _≤ᴿ_ (ratℝ-neg ε) (RI.neg-sub If Ig)
          (negᴿ-anti {If +ᴿ (-ᴿ Ig)} {ratℝ ε} If-If≤ε)
        where
        Rf Rg : ℝ
        Rf = Riemann f a b n
        Rg = Riemann g a b n

        s1 : If ≤ᴿ (Rf +ᴿ ratℝ (half ε))
        s1 = close-upper {If} {Rf} (half ε) sf'

        s2 : (Rf +ᴿ ratℝ (half ε)) ≤ᴿ (Rg +ᴿ ratℝ (half ε))
        s2 = +ᴿ-mono {Rf} {Rg} {ratℝ (half ε)} {ratℝ (half ε)}
          (Riemann-mono f g a b n a≤b fg) (≤ᴿ-refl {ratℝ (half ε)})

        s3 : (Rg +ᴿ ratℝ (half ε)) ≤ᴿ ((Ig +ᴿ ratℝ (half ε)) +ᴿ ratℝ (half ε))
        s3 = +ᴿ-mono {Rg} {Ig +ᴿ ratℝ (half ε)}
          {ratℝ (half ε)} {ratℝ (half ε)}
          (close-lower {Ig} {Rg} (half ε) sg') (≤ᴿ-refl {ratℝ (half ε)})

        s4 : ((Ig +ᴿ ratℝ (half ε)) +ᴿ ratℝ (half ε)) ≡ (Ig +ᴿ ratℝ ε)
        s4 = RI.assoc3 Ig (ratℝ (half ε)) ∙ ap (Ig +ᴿ_) (half-rat ε)

        If≤ : If ≤ᴿ (Ig +ᴿ ratℝ ε)
        If≤ = ≤ᴿ-trans {If} {Rg +ᴿ ratℝ (half ε)} {Ig +ᴿ ratℝ ε}
          (≤ᴿ-trans {If} {Rf +ᴿ ratℝ (half ε)} {Rg +ᴿ ratℝ (half ε)} s1 s2)
          (subst ((Rg +ᴿ ratℝ (half ε)) ≤ᴿ_) s4 s3)

        If-If≤ε : (If +ᴿ (-ᴿ Ig)) ≤ᴿ ratℝ ε
        If-If≤ε = le→sub If Ig (ratℝ ε) If≤
```

## What remains

The construction above is honest but **conditional**: it assumes,
as the module parameter `∫-converges`{.Agda}, that the dyadic
Riemann sums converge. That hypothesis is the one genuine analytic
fact of this development, and closing it is the natural next step.
Its proof is a single geometric estimate. Dyadic bisection makes the
$(n+1)$-partition an exact refinement of the $n$-partition, so
$$
\lvert R_{n} - R_{n+1}\rvert \le \frac{M\,(b-a)^{2}}{4 \cdot 2^{n}},
$$
where $M$ is the depth-one quotient bound of the integrand — the
[[Lipschitz modulus|hadamard-separation]] `A .fst 1 fzero .fst`
carries via `Bd`{.Agda}. Telescoping this geometric bound and
choosing the index by the [[Archimedean property|dedekind-real]]
packages `Riemann f a b` into a `CauchyApprox`{.Agda}, whose
`lim`{.Agda} is `∫₀`{.Agda} and whose `lim-modulus`{.Agda} is
`∫-converges`{.Agda}. It requires a sum-regrouping lemma over the
even/odd dyadic indices, which has no existing template here.

Two further items are recorded as scoped out, in the manner of the
$x \ge 1$ restriction of `sqrt`{.Agda}:

* **Fundamental Theorem, direction 1** — $\int_{a}^{b} F' = F(b) -
  F(a)$. On the dyadic partition the raw Hadamard quotient
  telescopes *exactly* to $F(\mathrm{pt}\,b) - F(\mathrm{pt}\,a)$;
  the Riemann sum of `∂-of F fzero A`{.Agda} differs from that
  telescope termwise by the off-diagonal defect of the quotient,
  bounded by its own Lipschitz modulus (`quot-smooth⁺`{.Agda}) and
  summing to zero. Both the exact telescoping and the vanishing
  defect are within reach once convergence is in hand.

* **Fundamental Theorem, direction 2** — $\frac{d}{dx}\int_{0}^{x} f
  = f$. This needs a fresh total Hadamard quotient manufactured from
  the integral remainder, with hand-proved roundedness and
  boundedness; there is no existing template and it is deliberately
  left open.

The **Constancy Principle** ($F' \equiv 0 \Rightarrow F$ constant) is
then a two-line corollary of direction 1 via `∫-linear`{.Agda} and
the integral of the zero function, and is left to follow it.

General non-Lipschitz, merely uniformly-continuous integration is
declined on purpose: the `Smooth⁺`{.Agda} Lipschitz specialization
above suffices for every physics and power-series consumer.
