<!--
```agda
open import 1Lab.Truncation
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
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Bounds where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
```
-->

# Bound arithmetic for real numbers {defines="real-bounds"}

This module assembles the comparison toolkit that the
bounds-enriched [[Hadamard towers|smooth-function]] consume:
one-sided bounds interact with negation, with sums, and — through
the classic polarisation identities — with products, so that a
rational box bound on each factor yields a rational box bound on
any ring combination.

The ring identities themselves are decided by the [[commutative
ring solver|ring-solver]], instantiated at the ring of Dedekind
reals.

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  prod-minus
    : ∀ a b m n
    → ((m R.* n) R.+ (m R.* n)) R.+ (R.- ((a R.* b) R.+ (a R.* b)))
    ≡ ((m R.+ (R.- a)) R.* (b R.+ (R.- (R.- n))))
      R.+ ((a R.+ (R.- (R.- m))) R.* (n R.+ (R.- b)))
  prod-minus a b m n = cring! S

  prod-plus
    : ∀ a b m n
    → ((a R.* b) R.+ (m R.* n)) R.+ ((a R.* b) R.+ (m R.* n))
    ≡ ((a R.+ (R.- (R.- m))) R.* (b R.+ (R.- (R.- n))))
      R.+ ((m R.+ (R.- a)) R.* (n R.+ (R.- b)))
  prod-plus a b m n = cring! S

  double-diff
    : ∀ x y
    → ((y R.+ y) R.+ (R.- (x R.+ x)))
    ≡ (y R.+ (R.- x)) R.+ (y R.+ (R.- x))
  double-diff x y = cring! S

  neg-sum
    : ∀ a b → R.- (a R.+ b) ≡ (R.- a) R.+ (R.- b)
  neg-sum a b = cring! S

private module RI = Identities ℝ-comm
```
-->

## Order versus the cut structure

The order $x \le y$ is inclusion of lower cuts; by locatedness it
equally implies the reverse inclusion of upper cuts.

```agda
≤ᴿ-upper
  : ∀ {x y} → x ≤ᴿ y → ∀ {r} → ∣ y .upper r ∣ → ∣ x .upper r ∣
≤ᴿ-upper {x} {y} x≤y {r} ur =
  ∥-∥-rec (x .upper r .is-tr)
    (λ (r' , r'<r , ur') →
      ∥-∥-rec (x .upper r .is-tr)
        (λ where
          (inl lr') → absurd (cut.cut-disjoint y r' (x≤y r' lr') ur')
          (inr uxr) → uxr)
        (cut.cut-located x r'<r))
    (cut.upper-round y r ur)

negᴿ-anti : ∀ {x y} → x ≤ᴿ y → (-ᴿ y) ≤ᴿ (-ᴿ x)
negᴿ-anti {x} {y} x≤y q uq = ≤ᴿ-upper {x} {y} x≤y uq
```

A rational witness in the upper cut is exactly a rational upper
bound, and dually for the lower cut.

```agda
upper→≤ratℝ : ∀ {x v} → ∣ x .upper v ∣ → x ≤ᴿ ratℝ v
upper→≤ratℝ {x} {v} uv q lq = lower<upper x lq uv

lower→ratℝ≤ : ∀ {x u} → ∣ x .lower u ∣ → ratℝ u ≤ᴿ x
lower→ratℝ≤ {x} {u} lu q q<u = cut.lower-close x q<u lu

bounded-above : (x : ℝ) → ∥ Σ Ratio (λ v → x ≤ᴿ ratℝ v) ∥
bounded-above x = ∥-∥-map
  (λ (v , uv) → v , upper→≤ratℝ {x} {v} uv)
  (cut.upper-inhab x)
```

## Order versus differences

The order is equivalently nonnegativity of the difference. One
direction squeezes an approximating bracket of $x$; the other plays
the hypothesis against roundedness.

```agda
≤ᴿ→diff-nonneg : ∀ {x y} → x ≤ᴿ y → 0ᴿ ≤ᴿ (y +ᴿ (-ᴿ x))
≤ᴿ→diff-nonneg {x} {y} x≤y q q<0 =
  ∥-∥-rec ((y +ᴿ (-ᴿ x)) .lower q .is-tr)
    (λ (u , w , lu , uw , wu<-q) → inc
      ( u , -ℚ w
      , x≤y u lu
      , subst (λ z → ∣ x .upper z ∣) (sym (negℚ-invol w)) uw
      , flip-diff u w wu<-q))
    (approx x (-ℚ q) 0<-q)
  where
  0<-q : 0 < (-ℚ q)
  0<-q = <-resp refl (+ℚ-idl (-ℚ q)) (<→positive-diff q<0)

  neg-diff-swap : ∀ w u → -ℚ (w +ℚ (-ℚ u)) ≡ u +ℚ (-ℚ w)
  neg-diff-swap w u = rational!

  flip-diff : ∀ u w → (w +ℚ (-ℚ u)) < (-ℚ q) → q < (u +ℚ (-ℚ w))
  flip-diff u w p = <-resp (negℚ-invol q) (neg-diff-swap w u) (negℚ-anti-< p)

diff-nonneg→≤ᴿ : ∀ {x y} → 0ᴿ ≤ᴿ (y +ᴿ (-ᴿ x)) → x ≤ᴿ y
diff-nonneg→≤ᴿ {x} {y} h q lq =
  ∥-∥-rec (y .lower q .is-tr)
    (λ (q' , q<q' , lq') →
      □-rec (y .lower q .is-tr)
        (λ (r , t , lr , ut , qq'<rt) →
          cut.lower-close y (step q' r t lq' ut qq'<rt) lr)
        (h (q +ℚ (-ℚ q')) (qq'<0 q' q<q')))
    (cut.lower-round x q lq)
  where
  neg-diff : ∀ a b → -ℚ (a +ℚ (-ℚ b)) ≡ b +ℚ (-ℚ a)
  neg-diff a b = rational!

  qq'<0 : ∀ q' → q < q' → (q +ℚ (-ℚ q')) < 0
  qq'<0 q' q<q' = <-resp (neg-diff q' q) neg-zero
    (negℚ-anti-< (<→positive-diff q<q'))

  reassoc : ∀ r t q' → q' +ℚ (q +ℚ (-ℚ q')) ≡ q
  reassoc r t q' = rational!

  reassoc' : ∀ r t q' → q' +ℚ (r +ℚ t) ≡ (r +ℚ t) +ℚ q'
  reassoc' r t q' = rational!

  cancel : ∀ t q' → t +ℚ (-ℚ t) ≡ 0
  cancel t q' = rational!

  regroup : ∀ r t q' → r +ℚ (t +ℚ q') ≡ (r +ℚ t) +ℚ q'
  regroup r t q' = rational!

  step
    : ∀ q' r t
    → ∣ x .lower q' ∣ → ∣ x .upper (-ℚ t) ∣
    → (q +ℚ (-ℚ q')) < (r +ℚ t)
    → q < r
  step q' r t lq' ut lt = <-trans s1 s3
    where
    q'<-t : q' < (-ℚ t)
    q'<-t = lower<upper x lq' ut

    s1 : q < ((r +ℚ t) +ℚ q')
    s1 = <-resp (reassoc r t q') (reassoc' r t q')
      (+ℚ-preserves-<l q' lt)

    s2 : (t +ℚ q') < 0
    s2 = <-resp refl (cancel t q') (+ℚ-preserves-<l t q'<-t)

    s3 : ((r +ℚ t) +ℚ q') < r
    s3 = <-resp (regroup r t q') (+ℚ-idr r)
      (+ℚ-preserves-<l r s2)
```

## Halving without dividing

Nonnegativity of a double gives nonnegativity, by a rational
maximum game — so all the polarisation identities below can carry
their factor of two harmlessly.

```agda
half-nonneg : ∀ {z} → 0ᴿ ≤ᴿ (z +ᴿ z) → 0ᴿ ≤ᴿ z
half-nonneg {z} h q q<0 =
  □-rec (z .lower q .is-tr)
    (λ (r , s , lr , ls , q<rs) → pick r s lr ls q<rs)
    (h q q<0)
  where
  pick
    : ∀ r s → ∣ z .lower r ∣ → ∣ z .lower s ∣
    → q < (r +ℚ s) → ∣ z .lower q ∣
  pick r s lr ls q<rs with holds? (q < maxℚ r s)
  ... | yes q<m = cut.lower-close z q<m
    ([ (λ e → subst (λ w → ∣ z .lower w ∣) (sym e) lr)
     , (λ e → subst (λ w → ∣ z .lower w ∣) (sym e) ls) ]
     (maxℚ-choice r s))
  ... | no ¬q<m = absurd (<-irrefl refl q<q)
    where
    m≤q : maxℚ r s ≤ q
    m≤q = ¬<→≥ ¬q<m

    rs≤qq : (r +ℚ s) ≤ (q +ℚ q)
    rs≤qq = +ℚ-preserves-≤
      (≤-trans (maxℚ-≤l {r} {s}) m≤q)
      (≤-trans (maxℚ-≤r {r} {s}) m≤q)

    qq<q : (q +ℚ q) < q
    qq<q = <-resp refl (+ℚ-idr q) (+ℚ-preserves-<l q q<0)

    q<q : q < q
    q<q = <-trans (<-≤-trans q<rs rs≤qq) qq<q

double-≤ : ∀ {x y} → (x +ᴿ x) ≤ᴿ (y +ᴿ y) → x ≤ᴿ y
double-≤ {x} {y} h = diff-nonneg→≤ᴿ {x} {y} d3
  where
  d2 : 0ᴿ ≤ᴿ ((y +ᴿ (-ᴿ x)) +ᴿ (y +ᴿ (-ᴿ x)))
  d2 = subst (0ᴿ ≤ᴿ_) (RI.double-diff x y)
    (≤ᴿ→diff-nonneg {x +ᴿ x} {y +ᴿ y} h)

  d3 : 0ᴿ ≤ᴿ (y +ᴿ (-ᴿ x))
  d3 = half-nonneg {y +ᴿ (-ᴿ x)} d2
```

## Two-sided product bounds

The polarisation identities express $2(MN \pm ab)$ as a sum of two
products of nonnegative differences, so a two-sided bound on each
factor bounds the product on both sides — with no case analysis on
signs, which would be unavailable constructively.

```agda
private
  sum-nonneg
    : ∀ {u v} → 0ᴿ ≤ᴿ u → 0ᴿ ≤ᴿ v → 0ᴿ ≤ᴿ (u +ᴿ v)
  sum-nonneg {u} {v} p q = subst (_≤ᴿ (u +ᴿ v)) (+ᴿ-idr 0ᴿ)
    (+ᴿ-mono {0ᴿ} {u} {0ᴿ} {v} p q)

prod-≤
  : ∀ {a b m n}
  → a ≤ᴿ m → (-ᴿ m) ≤ᴿ a
  → b ≤ᴿ n → (-ᴿ n) ≤ᴿ b
  → ((a *ᴿ b) ≤ᴿ (m *ᴿ n)) × ((-ᴿ (m *ᴿ n)) ≤ᴿ (a *ᴿ b))
prod-≤ {a} {b} {m} {n} a≤m m'≤a b≤n n'≤b = upper-bd , lower-bd
  where
  f₁ : 0ᴿ ≤ᴿ (m +ᴿ (-ᴿ a))
  f₁ = ≤ᴿ→diff-nonneg {a} {m} a≤m

  f₂ : 0ᴿ ≤ᴿ (b +ᴿ (-ᴿ (-ᴿ n)))
  f₂ = ≤ᴿ→diff-nonneg { -ᴿ n} {b} n'≤b

  f₃ : 0ᴿ ≤ᴿ (a +ᴿ (-ᴿ (-ᴿ m)))
  f₃ = ≤ᴿ→diff-nonneg { -ᴿ m} {a} m'≤a

  f₄ : 0ᴿ ≤ᴿ (n +ᴿ (-ᴿ b))
  f₄ = ≤ᴿ→diff-nonneg {b} {n} b≤n

  upper-bd : (a *ᴿ b) ≤ᴿ (m *ᴿ n)
  upper-bd = double-≤ {a *ᴿ b} {m *ᴿ n} $
    diff-nonneg→≤ᴿ {(a *ᴿ b) +ᴿ (a *ᴿ b)} {(m *ᴿ n) +ᴿ (m *ᴿ n)} $
    subst (0ᴿ ≤ᴿ_) (sym (RI.prod-minus a b m n)) $
    sum-nonneg
      {u = (m +ᴿ (-ᴿ a)) *ᴿ (b +ᴿ (-ᴿ (-ᴿ n)))}
      {v = (a +ᴿ (-ᴿ (-ᴿ m))) *ᴿ (n +ᴿ (-ᴿ b))}
      (*ᴿ-nonneg (m +ᴿ (-ᴿ a)) (b +ᴿ (-ᴿ (-ᴿ n))) f₁ f₂)
      (*ᴿ-nonneg (a +ᴿ (-ᴿ (-ᴿ m))) (n +ᴿ (-ᴿ b)) f₃ f₄)

  lower-bd : (-ᴿ (m *ᴿ n)) ≤ᴿ (a *ᴿ b)
  lower-bd = diff-nonneg→≤ᴿ { -ᴿ (m *ᴿ n)} {a *ᴿ b} $
    subst (λ w → 0ᴿ ≤ᴿ ((a *ᴿ b) +ᴿ w))
      (sym (-ᴿ-invol (m *ᴿ n))) $
    half-nonneg {(a *ᴿ b) +ᴿ (m *ᴿ n)} $
    subst (0ᴿ ≤ᴿ_) (sym (RI.prod-plus a b m n)) $
    sum-nonneg
      {u = (a +ᴿ (-ᴿ (-ᴿ m))) *ᴿ (b +ᴿ (-ᴿ (-ᴿ n)))}
      {v = (m +ᴿ (-ᴿ a)) *ᴿ (n +ᴿ (-ᴿ b))}
      (*ᴿ-nonneg (a +ᴿ (-ᴿ (-ᴿ m))) (b +ᴿ (-ᴿ (-ᴿ n))) f₃ f₂)
      (*ᴿ-nonneg (m +ᴿ (-ᴿ a)) (n +ᴿ (-ᴿ b)) f₁ f₄)
```

## The absolute-value toolkit

A two-sided bound is the same thing as a bound on the [[absolute
value|real-absolute-value]], and the bounds propagate through
negation, sums and products.

```agda
abs-≤ : ∀ {x b} → x ≤ᴿ b → (-ᴿ b) ≤ᴿ x → absᴿ x ≤ᴿ b
abs-≤ {x} {b} p q = maxᴿ-universal {x} { -ᴿ x} {b} p
  (subst ((-ᴿ x) ≤ᴿ_) (-ᴿ-invol b) (negᴿ-anti { -ᴿ b} {x} q))

abs-out-l : ∀ {x b} → absᴿ x ≤ᴿ b → x ≤ᴿ b
abs-out-l {x} {b} p = ≤ᴿ-trans {x} {absᴿ x} {b} (maxᴿ-≤l x (-ᴿ x)) p

abs-out-r : ∀ {x b} → absᴿ x ≤ᴿ b → (-ᴿ b) ≤ᴿ x
abs-out-r {x} {b} p = subst ((-ᴿ b) ≤ᴿ_) (-ᴿ-invol x)
  (negᴿ-anti { -ᴿ x} {b}
    (≤ᴿ-trans { -ᴿ x} {absᴿ x} {b} (maxᴿ-≤r x (-ᴿ x)) p))

abs-neg : ∀ {x b} → absᴿ x ≤ᴿ b → absᴿ (-ᴿ x) ≤ᴿ b
abs-neg {x} {b} p = abs-≤ { -ᴿ x} {b}
  (≤ᴿ-trans { -ᴿ x} {absᴿ x} {b} (maxᴿ-≤r x (-ᴿ x)) p)
  (negᴿ-anti {x} {b} (abs-out-l {x} {b} p))

abs-sum
  : ∀ {x y bx by}
  → absᴿ x ≤ᴿ bx → absᴿ y ≤ᴿ by
  → absᴿ (x +ᴿ y) ≤ᴿ (bx +ᴿ by)
abs-sum {x} {y} {bx} {by} p q = abs-≤ {x +ᴿ y} {bx +ᴿ by}
  (+ᴿ-mono {x} {bx} {y} {by}
    (abs-out-l {x} {bx} p) (abs-out-l {y} {by} q))
  (subst (_≤ᴿ (x +ᴿ y)) (sym (RI.neg-sum bx by))
    (+ᴿ-mono { -ᴿ bx} {x} { -ᴿ by} {y}
      (abs-out-r {x} {bx} p) (abs-out-r {y} {by} q)))

abs-prod
  : ∀ {x y m n}
  → absᴿ x ≤ᴿ m → absᴿ y ≤ᴿ n
  → absᴿ (x *ᴿ y) ≤ᴿ (m *ᴿ n)
abs-prod {x} {y} {m} {n} p q =
  abs-≤ {x *ᴿ y} {m *ᴿ n} (bd .fst) (bd .snd)
  where
  bd = prod-≤ {x} {y} {m} {n}
    (abs-out-l {x} {m} p) (abs-out-r {x} {m} p)
    (abs-out-l {y} {n} q) (abs-out-r {y} {n} q)
```
