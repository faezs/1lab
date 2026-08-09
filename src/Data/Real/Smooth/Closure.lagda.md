<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Truncation
open import 1Lab.Resizing
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Reciprocal
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Partial
open import Data.Real.Sqrt
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Closure where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
open positive-bounds

private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  mul-sub
    : ∀ a b c
    → a R.* (b R.+ (R.- c)) ≡ (a R.* b) R.+ (R.- (a R.* c))
  mul-sub a b c = cring! S

  recip-quot
    : ∀ r r' u u'
    → (r R.* (u' R.* r')) R.+ (R.- ((u R.* r) R.* r'))
    ≡ (R.- (u R.+ (R.- u'))) R.* (r R.* r')
  recip-quot r r' u u' = cring! S

  neg-pull
    : ∀ a b c → (R.- (a R.* b)) R.* c ≡ a R.* (R.- (b R.* c))
  neg-pull a b c = cring! S

  diff-sq
    : ∀ s s'
    → (s R.+ (R.- s')) R.* (s R.+ s')
    ≡ (s R.* s) R.+ (R.- (s' R.* s'))
  diff-sq s s' = cring! S

  factor-right
    : ∀ a b c → (a R.* c) R.+ (R.- (b R.* c)) ≡ (a R.+ (R.- b)) R.* c
  factor-right a b c = cring! S

  add-factor
    : ∀ a b c → (a R.* c) R.+ (b R.* c) ≡ (a R.+ b) R.* c
  add-factor a b c = cring! S

  neg-sq : ∀ a → (R.- a) R.* (R.- a) ≡ a R.* a
  neg-sq a = cring! S

  sqrt-quot
    : ∀ s s' p
    → (s R.+ (R.- s')) R.* ((s' R.+ s) R.* p)
    ≡ ((s R.* s) R.+ (R.- (s' R.* s'))) R.* p
  sqrt-quot s s' p = cring! S

  diff-sq-assoc
    : ∀ a b p
    → (a R.+ (R.- b)) R.* ((a R.+ b) R.* p)
    ≡ ((a R.* a) R.+ (R.- (b R.* b))) R.* p
  diff-sq-assoc a b p = cring! S

private module RI = Identities ℝ-comm

private abstract
  neg-mul : ∀ u v → ((-ℚ u) *ℚ (-ℚ v)) ≡ (u *ℚ v)
  neg-mul u v = rational!

  neg-mul-l : ∀ u v → (-ℚ ((-ℚ u) *ℚ v)) ≡ (u *ℚ v)
  neg-mul-l u v = rational!
```
-->

# Closure of bounded-smoothness under reciprocals and roots {defines="smooth-reciprocal smooth-square-root patch-map"}

The [[smooth calculus|hadamard-tower]] closes under the ring
operations, renaming and composition; the good-cover
diffeomorphisms of the site need two more combinators, both
*partial* in general but *total* on functions bounded below by
$1$: the reciprocal $1/f$ and the square root $\sqrt f$. This
module builds their [[Hadamard towers|hadamard-tower]] and
[[bound towers|bounds-tower]], and assembles the **patch map**
$x \mapsto x/\sqrt{1 + x^2}$ — the diffeomorphism $\bR \cong
(-1, 1)$ that the differentiably good covers are made of — as a
[[bounded-smooth function|bounded-smooth-function]].

## Reciprocals of reals at least one

A real $z \ge 1$ is strictly positive with explicit rational
bounds: $\tfrac12$ below (since $\tfrac12 < 1 \le z$) and any
upper witness above. The hypothesis $1 \le z$ is a *proposition*,
so the truncated bounds feed the [[proof-irrelevant
reciprocal|partial-smooth-function]] `recip∥`{.Agda} directly.

```agda
≥1-pos-bounds : (z : ℝ) → ratℝ 1 ≤ᴿ z → ∥ positive-bounds z ∥
≥1-pos-bounds z p = ∥-∥-map mk (cut.upper-inhab z) where
  mk : Σ Ratio (λ v → ∣ z .upper v ∣) → positive-bounds z
  mk (v , uv) = record
    { lo     = half 1
    ; hi     = v
    ; lo-mem = p (half 1) (half-lt 0<1')
    ; hi-mem = uv
    ; lo-pos = half-pos 0<1'
    }

recip≥1 : (z : ℝ) → ratℝ 1 ≤ᴿ z → ℝ
recip≥1 z p = recip∥ z (≥1-pos-bounds z p)

recip≥1-invr : ∀ z (p : ratℝ 1 ≤ᴿ z) → z *ᴿ recip≥1 z p ≡ 1ᴿ
recip≥1-invr z p = recip∥-invr z (≥1-pos-bounds z p)
```

Since inverses in a commutative ring are unique, the reciprocal
depends on nothing but the real itself:

```agda
recip≥1-ap
  : ∀ {z z'} (e : z ≡ z') (p : ratℝ 1 ≤ᴿ z) (p' : ratℝ 1 ≤ᴿ z')
  → recip≥1 z p ≡ recip≥1 z' p'
recip≥1-ap {z} {z'} e p p' =
  inverse-unique z (recip≥1 z p) (recip≥1 z' p')
    (recip≥1-invr z p)
    (subst (λ w → w *ᴿ recip≥1 z' p' ≡ 1ᴿ) (sym e)
      (recip≥1-invr z' p'))
```

## Order facts for the reciprocal

The reciprocal of $z \ge 1$ sits inside $[0, 1]$. Nonnegativity is
read off the reciprocal's cut — a rational $q < 0$ is below $1/z$
with any positive upper witness of $z$, since $q \cdot b \le 0 <
1$ — after eliminating the truncated bounds, which is legitimate
because the order is a proposition.

<!--
```agda
private abstract
  ratℝ-mono : ∀ {p q} → p ≤ q → ratℝ p ≤ᴿ ratℝ q
  ratℝ-mono p≤q r r<p = <-≤-trans r<p p≤q

  0≤1ᴿ : 0ᴿ ≤ᴿ ratℝ 1
  0≤1ᴿ q q<0 = <-trans q<0 0<1'

  negrat≤0 : ∀ {m} → 0 ≤ m → (-ᴿ ratℝ m) ≤ᴿ 0ᴿ
  negrat≤0 {m} 0≤m q lm = <-≤-trans
    (<-resp (negℚ-invol q) refl (negℚ-anti-< lm))
    (≤-resp refl neg-zero (negℚ-anti-≤ 0≤m))

≥1→0≤ : ∀ {z} → ratℝ 1 ≤ᴿ z → 0ᴿ ≤ᴿ z
≥1→0≤ {z} p = ≤ᴿ-trans {0ᴿ} {ratℝ 1} {z} 0≤1ᴿ p

sum-≥1
  : ∀ (a b : ℝ) → ratℝ 1 ≤ᴿ a → 0ᴿ ≤ᴿ b → ratℝ 1 ≤ᴿ (a +ᴿ b)
sum-≥1 a b pa pb = subst (_≤ᴿ (a +ᴿ b)) (+ᴿ-idr (ratℝ 1))
  (+ᴿ-mono {ratℝ 1} {a} {0ᴿ} {b} pa pb)
```
-->

```agda
recip≥1-nonneg : ∀ z (p : ratℝ 1 ≤ᴿ z) → 0ᴿ ≤ᴿ recip≥1 z p
recip≥1-nonneg z p = go (≥1-pos-bounds z p) where
  go : (w : ∥ positive-bounds z ∥) → 0ᴿ ≤ᴿ recip∥ z w
  go = ∥-∥-elim
    (λ w → Π-is-hlevel 1 λ q → Π-is-hlevel 1 λ _ →
      (recip∥ z w .lower q) .is-tr)
    step
    where
    step : (pb : positive-bounds z) → 0ᴿ ≤ᴿ recip∥ z (inc pb)
    step pb q q<0 = inc (pb .hi , pb .hi-mem , 0<hi , qhi<1)
      where
      0<hi : 0 < pb .hi
      0<hi = <-trans (pb .lo-pos)
        (lower<upper z (pb .lo-mem) (pb .hi-mem))

      qhi≤0 : (q *ℚ pb .hi) ≤ 0
      qhi≤0 = ≤-resp refl (*ℚ-zerol (pb .hi))
        (*ℚ-preserves-≤r (pb .hi) (<-weaken q<0) (<-weaken 0<hi))

      qhi<1 : (q *ℚ pb .hi) < 1
      qhi<1 = ≤-<-trans qhi≤0 0<1'
```

For the upper bound, multiply the nonnegative difference $z - 1$
by the nonnegative reciprocal $v$ and use $z \cdot v = 1$: the
product is $1 - v$, so $v \le 1$.

```agda
recip≥1-≤1 : ∀ z (p : ratℝ 1 ≤ᴿ z) → recip≥1 z p ≤ᴿ ratℝ 1
recip≥1-≤1 z p = diff-nonneg→≤ᴿ {recip≥1 z p} {ratℝ 1} nn
  where
  v : ℝ
  v = recip≥1 z p

  path : v *ᴿ (z −ᴿ ratℝ 1) ≡ ratℝ 1 −ᴿ v
  path = RI.mul-sub v z (ratℝ 1)
    ∙ ap₂ _−ᴿ_ (*ᴿ-comm v z ∙ recip≥1-invr z p) (*ᴿ-idr v)

  nn : 0ᴿ ≤ᴿ (ratℝ 1 +ᴿ (-ᴿ v))
  nn = subst (0ᴿ ≤ᴿ_) path
    (*ᴿ-nonneg v (z −ᴿ ratℝ 1)
      (recip≥1-nonneg z p)
      (≤ᴿ→diff-nonneg {ratℝ 1} {z} p))

recip≥1-abs : ∀ z (p : ratℝ 1 ≤ᴿ z) → absᴿ (recip≥1 z p) ≤ᴿ ratℝ 1
recip≥1-abs z p = abs-≤ {recip≥1 z p} {ratℝ 1}
  (recip≥1-≤1 z p)
  (≤ᴿ-trans { -ᴿ ratℝ 1} {0ᴿ} {recip≥1 z p}
    (negrat≤0 0≤1')
    (recip≥1-nonneg z p))
```

## The Hadamard tower of the reciprocal

The quotient of $1/f$ in direction $i$ is the calculus rule
$-f'/f^2$ in Hadamard clothing: the two reciprocal factors are
evaluated at the two frames of the fresh variable — the moved
point through $\sigma_i$ and the unmoved point through
$\mathrm{fsuc}$ — so that the whole quotient is again a ring
combination of renamed copies of $f$, its quotient, and *smaller*
reciprocal towers. The recursion is on the depth $k$ only.

```agda
tower-recip
  : ∀ k n (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → TowerTo k n f
  → TowerTo k n (λ x → recip≥1 (f x) (lb x))
tower-recip zero    n f lb T = lift tt
tower-recip (suc k) n f lb T i = g , quot , rec where
  fq : Fun (suc n)
  fq = T i .fst

  qf : Quot n f i fq
  qf = T i .snd .fst

  T' : TowerTo k (suc n) fq
  T' = T i .snd .snd

  f-σ f-suc : Fun (suc n)
  f-σ   y = f (λ j → y (σᵢ i j))
  f-suc y = f (λ j → y (fsuc j))

  lb-σ : ∀ y → ratℝ 1 ≤ᴿ f-σ y
  lb-σ y = lb (λ j → y (σᵢ i j))

  lb-suc : ∀ y → ratℝ 1 ≤ᴿ f-suc y
  lb-suc y = lb (λ j → y (fsuc j))

  rf-σ rf-suc : Fun (suc n)
  rf-σ   y = recip≥1 (f-σ y) (lb-σ y)
  rf-suc y = recip≥1 (f-suc y) (lb-suc y)

  g : Fun (suc n)
  g y = -ᴿ (fq y *ᴿ (rf-suc y *ᴿ rf-σ y))
```

The quotient law multiplies the difference of reciprocals by
$1 = u u^{-1}$ on both sides, collapses the result to $-(u - u')
\cdot (r r')$ by a ring identity, and then factors $u - u'$
through the quotient of $f$ itself. Only the $\sigma_i$-frame
reciprocal needs a rewrite along `σᵢ-set`{.Agda}; the
$\mathrm{fsuc}$-frame one is the unmoved reciprocal on the nose.

```agda
  quot : Quot n (λ x → recip≥1 (f x) (lb x)) i g
  quot x t =
      ap₂ _−ᴿ_
        (sym (*ᴿ-idr r) ∙ ap (r *ᴿ_) (sym (recip≥1-invr u' p')))
        (sym (*ᴿ-idl r') ∙ ap (_*ᴿ r') (sym (recip≥1-invr u p)))
    ∙ RI.recip-quot r r' u u'
    ∙ ap (λ w → (-ᴿ w) *ᴿ (r *ᴿ r')) (qf x t)
    ∙ RI.neg-pull (x i −ᴿ t) (fq (cons t x)) (r *ᴿ r')
    ∙ ap (λ w → (x i −ᴿ t) *ᴿ (-ᴿ (fq (cons t x) *ᴿ (r *ᴿ w))))
        (sym rw)
    where
    u u' : ℝ
    u  = f x
    u' = f (set x i t)

    p : ratℝ 1 ≤ᴿ u
    p = lb x

    p' : ratℝ 1 ≤ᴿ u'
    p' = lb (set x i t)

    r r' : ℝ
    r  = recip≥1 u p
    r' = recip≥1 u' p'

    rw : rf-σ (cons t x) ≡ r'
    rw = ap (λ w → recip≥1 (f w) (lb w)) (σᵢ-set i x t)

  rec : TowerTo k (suc n) g
  rec = tower-neg k (suc n) (λ y → fq y *ᴿ (rf-suc y *ᴿ rf-σ y))
    (tower-mul k (suc n) fq (λ y → rf-suc y *ᴿ rf-σ y) T'
      (tower-mul k (suc n) rf-suc rf-σ
        (tower-recip k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)))
        (tower-recip k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)))))
```

## Bounds for the reciprocal tower

Since the reciprocal of a real at least $1$ lies in $[0,1]$, the
function $1/f$ is bounded by the *constant* $1$ on every box — no
bound on $f$ is consumed at the node. The bound tower then mirrors
the raw recursion clause for clause, spending the bound of $f$
only where the raw tower spends $f$'s quotients.

```agda
bd-recip≥1
  : ∀ {n} (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → Bd n (λ x → recip≥1 (f x) (lb x))
bd-recip≥1 f lb R = inc (1 , λ x _ → recip≥1-abs (f x) (lb x))

bdt-recip
  : ∀ k n (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → (T : TowerTo k n f) → Bd n f → BdTower k n f T
  → BdTower k n (λ x → recip≥1 (f x) (lb x)) (tower-recip k n f lb T)
bdt-recip zero    n f lb T bf BT = lift tt
bdt-recip (suc k) n f lb T bf BT i = node , rec where
  fq : Fun (suc n)
  fq = T i .fst

  T' : TowerTo k (suc n) fq
  T' = T i .snd .snd

  f-σ f-suc : Fun (suc n)
  f-σ   y = f (λ j → y (σᵢ i j))
  f-suc y = f (λ j → y (fsuc j))

  lb-σ : ∀ y → ratℝ 1 ≤ᴿ f-σ y
  lb-σ y = lb (λ j → y (σᵢ i j))

  lb-suc : ∀ y → ratℝ 1 ≤ᴿ f-suc y
  lb-suc y = lb (λ j → y (fsuc j))

  rf-σ rf-suc : Fun (suc n)
  rf-σ   y = recip≥1 (f-σ y) (lb-σ y)
  rf-suc y = recip≥1 (f-suc y) (lb-suc y)

  node : Bd (suc n) (λ y → -ᴿ (fq y *ᴿ (rf-suc y *ᴿ rf-σ y)))
  node = bd-neg (λ y → fq y *ᴿ (rf-suc y *ᴿ rf-σ y))
    (bd-mul fq (λ y → rf-suc y *ᴿ rf-σ y)
      (BT i .fst)
      (bd-mul rf-suc rf-σ
        (bd-recip≥1 f-suc lb-suc)
        (bd-recip≥1 f-σ lb-σ)))

  rec : BdTower k (suc n)
    (λ y → -ᴿ (fq y *ᴿ (rf-suc y *ᴿ rf-σ y)))
    (tower-recip (suc k) n f lb T i .snd .snd)
  rec = bdt-neg k (suc n) (λ y → fq y *ᴿ (rf-suc y *ᴿ rf-σ y))
    (tower-mul k (suc n) fq (λ y → rf-suc y *ᴿ rf-σ y) T'
      (tower-mul k (suc n) rf-suc rf-σ
        (tower-recip k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)))
        (tower-recip k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)))))
    (bdt-mul k (suc n) fq (λ y → rf-suc y *ᴿ rf-σ y) T'
      (tower-mul k (suc n) rf-suc rf-σ
        (tower-recip k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)))
        (tower-recip k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T))))
      (BT i .fst)
      (bd-mul rf-suc rf-σ
        (bd-recip≥1 f-suc lb-suc)
        (bd-recip≥1 f-σ lb-σ))
      (BT i .snd)
      (bdt-mul k (suc n) rf-suc rf-σ
        (tower-recip k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)))
        (tower-recip k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)))
        (bd-recip≥1 f-suc lb-suc)
        (bd-recip≥1 f-σ lb-σ)
        (bdt-recip k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T))
          (bd-rename fsuc f bf)
          (bdt-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)
            (bdt-trunc k T BT)))
        (bdt-recip k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T))
          (bd-rename (σᵢ i) f bf)
          (bdt-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)
            (bdt-trunc k T BT)))))

smooth⁺-recip
  : ∀ {n} {f : Fun n} (A : Smooth⁺ n f) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → Smooth⁺ n (λ x → recip≥1 (f x) (lb x))
smooth⁺-recip {n} {f} (S , bf , BT) lb =
    (λ k → tower-recip k n f lb (S k))
  , bd-recip≥1 f lb
  , (λ k → bdt-recip k n f lb (S k) bf (BT k))
```

## Sums bounded below by one

Two reals at least $1$ sum to at least $1$ — indeed at least $2$,
but the weaker bound is what the square root's normalising
denominator $\sqrt{f} + \sqrt{f'}$ needs to stay in the domain of
the reciprocal.

```agda
sum-≥1'
  : ∀ (a b : ℝ) → ratℝ 1 ≤ᴿ a → ratℝ 1 ≤ᴿ b → ratℝ 1 ≤ᴿ (a +ᴿ b)
sum-≥1' a b pa pb = sum-≥1 a b pa (≥1→0≤ {b} pb)
```

## The Hadamard tower of the square root

The derivative of $\sqrt f$ is $f' / (\sqrt f + \sqrt{f'})$: the
difference of roots, multiplied by $1 = (\sqrt f + \sqrt{f'})
\rho$ for $\rho$ the reciprocal of the sum of roots, factors
through the difference of *squares* — which `sqrt-square`{.Agda}
identifies with the difference of the function's values, whence
the quotient of $f$ takes over. The sum of roots is at least $1$
by `sum-≥1`{.Agda}, so its reciprocal is total, and the whole
normalising factor is one *named* function of the tuple — the
proof only ever rewrites the tuple, never the proposition riding
along inside `recip≥1`{.Agda}.

```agda
tower-sqrt
  : ∀ k n (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → TowerTo k n f
  → TowerTo k n (λ x → sqrt (f x) (lb x))
tower-sqrt zero    n f lb T = lift tt
tower-sqrt (suc k) n f lb T i = g , quot , rec where
  fq : Fun (suc n)
  fq = T i .fst

  qf : Quot n f i fq
  qf = T i .snd .fst

  T' : TowerTo k (suc n) fq
  T' = T i .snd .snd

  f-σ f-suc : Fun (suc n)
  f-σ   y = f (λ j → y (σᵢ i j))
  f-suc y = f (λ j → y (fsuc j))

  lb-σ : ∀ y → ratℝ 1 ≤ᴿ f-σ y
  lb-σ y = lb (λ j → y (σᵢ i j))

  lb-suc : ∀ y → ratℝ 1 ≤ᴿ f-suc y
  lb-suc y = lb (λ j → y (fsuc j))

  S-σ S-suc : Fun (suc n)
  S-σ   y = sqrt (f-σ y) (lb-σ y)
  S-suc y = sqrt (f-suc y) (lb-suc y)

  sum-lb : ∀ y → ratℝ 1 ≤ᴿ (S-σ y +ᴿ S-suc y)
  sum-lb y = sum-≥1 (S-σ y) (S-suc y)
    (sqrt-≥1 (f-σ y) (lb-σ y))
    (≥1→0≤ {S-suc y} (sqrt-≥1 (f-suc y) (lb-suc y)))

  ρfun : Fun (suc n)
  ρfun y = recip≥1 (S-σ y +ᴿ S-suc y) (sum-lb y)

  g : Fun (suc n)
  g y = fq y *ᴿ ρfun y

  quot : Quot n (λ x → sqrt (f x) (lb x)) i g
  quot x t =
      sym (*ᴿ-idr (s −ᴿ s'))
    ∙ ap ((s −ᴿ s') *ᴿ_)
        (sym (recip≥1-invr (S-σ (cons t x) +ᴿ s) (sum-lb (cons t x))))
    ∙ ap (λ w → (s −ᴿ s') *ᴿ ((w +ᴿ s) *ᴿ ρ)) sw
    ∙ RI.sqrt-quot s s' ρ
    ∙ ap₂ (λ a b → (a −ᴿ b) *ᴿ ρ)
        (sqrt-square (f x) (lb x))
        (sqrt-square (f (set x i t)) (lb (set x i t)))
    ∙ ap (_*ᴿ ρ) (qf x t)
    ∙ *ᴿ-assoc (x i −ᴿ t) (fq (cons t x)) ρ
    where
    s s' : ℝ
    s  = sqrt (f x) (lb x)
    s' = sqrt (f (set x i t)) (lb (set x i t))

    ρ : ℝ
    ρ = ρfun (cons t x)

    sw : S-σ (cons t x) ≡ s'
    sw = ap (λ w → sqrt (f w) (lb w)) (σᵢ-set i x t)

  rec : TowerTo k (suc n) g
  rec = tower-mul k (suc n) fq ρfun T'
    (tower-recip k (suc n) (λ y → S-σ y +ᴿ S-suc y) sum-lb
      (tower-add k (suc n) S-σ S-suc
        (tower-sqrt k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)))
        (tower-sqrt k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)))))
```

## Bounds for the square root tower

If $|f| \le M$ on a box then $\sqrt f \le \max(M, 1)$ there: with
$c$ the constant at $\max(M,1)$, monotony gives $f \le c \le c^2$
— the latter by the two-sided product comparison against $1 \cdot
c$ — so $c^2 - (\sqrt f)^2 \ge 0$, and multiplying by the
nonnegative reciprocal of $c + \sqrt f \ge 1$ cancels the squares:
$c - \sqrt f = (c^2 - (\sqrt f)^2) \cdot \rho \ge 0$. The lower
side is just $-c \le 0 \le 1 \le \sqrt f$.

```agda
bd-sqrt
  : ∀ {n} (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → Bd n f → Bd n (λ x → sqrt (f x) (lb x))
bd-sqrt {n} f lb bf R = ∥-∥-map upgrade (bf R) where
  upgrade
    : Σ Ratio (λ M → (x : Fin n → ℝ) → InBox n R x
        → absᴿ (f x) ≤ᴿ ratℝ M)
    → Σ Ratio (λ M → (x : Fin n → ℝ) → InBox n R x
        → absᴿ (sqrt (f x) (lb x)) ≤ᴿ ratℝ M)
  upgrade (M , h) = maxℚ M 1 , bound where
    c : ℝ
    c = ratℝ (maxℚ M 1)

    1≤c : ratℝ 1 ≤ᴿ c
    1≤c = ratℝ-mono (maxℚ-≤r {M} {1})

    -c≤1 : (-ᴿ c) ≤ᴿ ratℝ 1
    -c≤1 = ≤ᴿ-trans { -ᴿ c} {0ᴿ} {ratℝ 1}
      (negrat≤0 (≤-trans 0≤1' (maxℚ-≤r {M} {1})))
      0≤1ᴿ

    -c≤c : (-ᴿ c) ≤ᴿ c
    -c≤c = ≤ᴿ-trans { -ᴿ c} {ratℝ 1} {c} -c≤1 1≤c

    c≤cc : c ≤ᴿ (c *ᴿ c)
    c≤cc = subst (_≤ᴿ (c *ᴿ c)) (*ᴿ-idl c)
      (prod-≤ {ratℝ 1} {c} {c} {c} 1≤c -c≤1 (≤ᴿ-refl {c}) -c≤c .fst)

    bound
      : (x : Fin n → ℝ) → InBox n R x
      → absᴿ (sqrt (f x) (lb x)) ≤ᴿ ratℝ (maxℚ M 1)
    bound x xb = abs-≤ {z} {c} z≤c -c≤z where
      z : ℝ
      z = sqrt (f x) (lb x)

      1≤z : ratℝ 1 ≤ᴿ z
      1≤z = sqrt-≥1 (f x) (lb x)

      fx≤cc : f x ≤ᴿ (c *ᴿ c)
      fx≤cc = ≤ᴿ-trans {f x} {c} {c *ᴿ c}
        (≤ᴿ-trans {f x} {ratℝ M} {c}
          (abs-out-l {f x} {ratℝ M} (h x xb))
          (ratℝ-mono (maxℚ-≤l {M} {1})))
        c≤cc

      zz≤cc : (z *ᴿ z) ≤ᴿ (c *ᴿ c)
      zz≤cc = subst (_≤ᴿ (c *ᴿ c)) (sym (sqrt-square (f x) (lb x))) fx≤cc

      slb : ratℝ 1 ≤ᴿ (c +ᴿ z)
      slb = sum-≥1 c z 1≤c (≥1→0≤ {z} 1≤z)

      ρ : ℝ
      ρ = recip≥1 (c +ᴿ z) slb

      path : c −ᴿ z ≡ ((c *ᴿ c) −ᴿ (z *ᴿ z)) *ᴿ ρ
      path =
          sym (*ᴿ-idr (c −ᴿ z))
        ∙ ap ((c −ᴿ z) *ᴿ_) (sym (recip≥1-invr (c +ᴿ z) slb))
        ∙ RI.diff-sq-assoc c z ρ

      z≤c : z ≤ᴿ c
      z≤c = diff-nonneg→≤ᴿ {z} {c} (subst (0ᴿ ≤ᴿ_) (sym path)
        (*ᴿ-nonneg ((c *ᴿ c) −ᴿ (z *ᴿ z)) ρ
          (≤ᴿ→diff-nonneg {z *ᴿ z} {c *ᴿ c} zz≤cc)
          (recip≥1-nonneg (c +ᴿ z) slb)))

      -c≤z : (-ᴿ c) ≤ᴿ z
      -c≤z = ≤ᴿ-trans { -ᴿ c} {ratℝ 1} {z} -c≤1 1≤z
```

The bound tower mirrors the raw recursion; the reciprocal factor
contributes its constant bound, so no bound for the sum of roots
is ever demanded at the node.

```agda
bdt-sqrt
  : ∀ k n (f : Fun n) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → (T : TowerTo k n f) → Bd n f → BdTower k n f T
  → BdTower k n (λ x → sqrt (f x) (lb x)) (tower-sqrt k n f lb T)
bdt-sqrt zero    n f lb T bf BT = lift tt
bdt-sqrt (suc k) n f lb T bf BT i = node , rec where
  fq : Fun (suc n)
  fq = T i .fst

  T' : TowerTo k (suc n) fq
  T' = T i .snd .snd

  f-σ f-suc : Fun (suc n)
  f-σ   y = f (λ j → y (σᵢ i j))
  f-suc y = f (λ j → y (fsuc j))

  lb-σ : ∀ y → ratℝ 1 ≤ᴿ f-σ y
  lb-σ y = lb (λ j → y (σᵢ i j))

  lb-suc : ∀ y → ratℝ 1 ≤ᴿ f-suc y
  lb-suc y = lb (λ j → y (fsuc j))

  S-σ S-suc : Fun (suc n)
  S-σ   y = sqrt (f-σ y) (lb-σ y)
  S-suc y = sqrt (f-suc y) (lb-suc y)

  sum-lb : ∀ y → ratℝ 1 ≤ᴿ (S-σ y +ᴿ S-suc y)
  sum-lb y = sum-≥1 (S-σ y) (S-suc y)
    (sqrt-≥1 (f-σ y) (lb-σ y))
    (≥1→0≤ {S-suc y} (sqrt-≥1 (f-suc y) (lb-suc y)))

  ρfun : Fun (suc n)
  ρfun y = recip≥1 (S-σ y +ᴿ S-suc y) (sum-lb y)

  MσT : TowerTo k (suc n) S-σ
  MσT = tower-sqrt k (suc n) f-σ lb-σ
    (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T))

  MsucT : TowerTo k (suc n) S-suc
  MsucT = tower-sqrt k (suc n) f-suc lb-suc
    (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T))

  Madd : TowerTo k (suc n) (λ y → S-σ y +ᴿ S-suc y)
  Madd = tower-add k (suc n) S-σ S-suc MσT MsucT

  node : Bd (suc n) (λ y → fq y *ᴿ ρfun y)
  node = bd-mul fq ρfun (BT i .fst)
    (bd-recip≥1 (λ y → S-σ y +ᴿ S-suc y) sum-lb)

  rec : BdTower k (suc n) (λ y → fq y *ᴿ ρfun y)
    (tower-sqrt (suc k) n f lb T i .snd .snd)
  rec = bdt-mul k (suc n) fq ρfun T'
    (tower-recip k (suc n) (λ y → S-σ y +ᴿ S-suc y) sum-lb Madd)
    (BT i .fst)
    (bd-recip≥1 (λ y → S-σ y +ᴿ S-suc y) sum-lb)
    (BT i .snd)
    (bdt-recip k (suc n) (λ y → S-σ y +ᴿ S-suc y) sum-lb Madd
      (bd-add S-σ S-suc
        (bd-sqrt f-σ lb-σ (bd-rename (σᵢ i) f bf))
        (bd-sqrt f-suc lb-suc (bd-rename fsuc f bf)))
      (bdt-add k (suc n) S-σ S-suc MσT MsucT
        (bdt-sqrt k (suc n) f-σ lb-σ
          (tower-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T))
          (bd-rename (σᵢ i) f bf)
          (bdt-rename k (σᵢ i) (σᵢ-inj i) f (tower-trunc k T)
            (bdt-trunc k T BT)))
        (bdt-sqrt k (suc n) f-suc lb-suc
          (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T))
          (bd-rename fsuc f bf)
          (bdt-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)
            (bdt-trunc k T BT)))))

smooth⁺-sqrt
  : ∀ {n} {f : Fun n} (A : Smooth⁺ n f) (lb : ∀ x → ratℝ 1 ≤ᴿ f x)
  → Smooth⁺ n (λ x → sqrt (f x) (lb x))
smooth⁺-sqrt {n} {f} (S , bf , BT) lb =
    (λ k → tower-sqrt k n f lb (S k))
  , bd-sqrt f lb bf
  , (λ k → bdt-sqrt k n f lb (S k) bf (BT k))
```

## Squares are nonnegative

The remaining ingredient for the patch map's domain condition is
that squares of reals are nonnegative — constructively, a
rational $q < 0$ must be trapped under a corner bracket of $z
\cdot z$. Approximate $z$ to a width $\delta$ below both $-q$ and
$1$: if the bracket $[a,b]$ sits entirely on one side of zero,
every corner is a product of same-signed rationals, hence
nonnegative and above $q$; and if it straddles zero, then both
endpoints lie in $(-\delta, \delta)$, so the mixed corners exceed
$-\delta^2 > q$ — witnessed by the decomposition $ab + \delta^2 =
(\delta + a)b + \delta(\delta - b)$, a sum of products of visibly
nonnegative factors.

<!--
```agda
private abstract
  nonpos-mul : ∀ {u v} → u ≤ 0 → v ≤ 0 → 0 ≤ (u *ℚ v)
  nonpos-mul {u} {v} u≤0 v≤0 = ≤-resp refl (neg-mul u v)
    (*ℚ-nonnegative
      (≤-resp neg-zero refl (negℚ-anti-≤ u≤0))
      (≤-resp neg-zero refl (negℚ-anti-≤ v≤0)))

  shuffle-diff
    : ∀ d u v → (d +ℚ (-ℚ (v +ℚ (-ℚ u)))) ≡ ((d +ℚ u) +ℚ (-ℚ v))
  shuffle-diff d u v = rational!

  mixed-corner
    : ∀ u v d
    → (((d +ℚ u) *ℚ v) +ℚ (d *ℚ (d +ℚ (-ℚ v))))
    ≡ ((u *ℚ v) +ℚ (d *ℚ d))
  mixed-corner u v d = rational!

  cancel-shift
    : ∀ u v d
    → ((-ℚ (d *ℚ d)) +ℚ ((u *ℚ v) +ℚ (d *ℚ d))) ≡ (u *ℚ v)
  cancel-shift u v d = rational!
```
-->

```agda
sq-nonneg : ∀ (z : ℝ) → 0ᴿ ≤ᴿ (z *ᴿ z)
sq-nonneg z q q<0 =
  ∥-∥-rec ((z *ᴿ z) .lower q .is-tr) mk (approx z δ 0<δ)
  where
  0<-q : 0 < (-ℚ q)
  0<-q = <-resp refl (+ℚ-idl (-ℚ q)) (<→positive-diff q<0)

  m δ : Ratio
  m = minℚ (-ℚ q) 1
  δ = half m

  0<m : 0 < m
  0<m = minℚ-glb 0<-q 0<1'

  0<δ : 0 < δ
  0<δ = half-pos 0<m

  0≤δ : 0 ≤ δ
  0≤δ = <-weaken 0<δ

  δ<-q : δ < (-ℚ q)
  δ<-q = <-≤-trans (half-lt 0<m) (minℚ-≤l { -ℚ q} {1})

  δ≤1 : δ ≤ 1
  δ≤1 = <-weaken (<-≤-trans (half-lt 0<m) (minℚ-≤r { -ℚ q} {1}))

  δδ≤δ : (δ *ℚ δ) ≤ δ
  δδ≤δ = ≤-resp refl (*ℚ-idr δ) (*ℚ-preserves-≤l δ 0≤δ δ≤1)

  q<-δδ : q < (-ℚ (δ *ℚ δ))
  q<-δδ = <-resp (negℚ-invol q) refl
    (negℚ-anti-< (≤-<-trans δδ≤δ δ<-q))

  mk
    : Σ Ratio (λ u → Σ Ratio (λ v →
        ∣ z .lower u ∣ × ∣ z .upper v ∣ × ((v +ℚ (-ℚ u)) < δ)))
    → ∣ (z *ᴿ z) .lower q ∣
  mk (a , b , la , ub , width) with holds? (a < 0)
  ... | no ¬a<0 = inc (a , b , a , b , la , ub , la , ub , q<min)
    where
    0≤a : 0 ≤ a
    0≤a = ¬<→≥ ¬a<0

    0≤b : 0 ≤ b
    0≤b = ≤-trans 0≤a (<-weaken (lower<upper z la ub))

    q<min : q < min₄ (a *ℚ a) (a *ℚ b) (b *ℚ a) (b *ℚ b)
    q<min = min₄-univ-<
      (<-≤-trans q<0 (*ℚ-nonnegative 0≤a 0≤a))
      (<-≤-trans q<0 (*ℚ-nonnegative 0≤a 0≤b))
      (<-≤-trans q<0 (*ℚ-nonnegative 0≤b 0≤a))
      (<-≤-trans q<0 (*ℚ-nonnegative 0≤b 0≤b))
  ... | yes a<0 with holds? (0 < b)
  ...   | no ¬0<b = inc (a , b , a , b , la , ub , la , ub , q<min)
    where
    a≤0 : a ≤ 0
    a≤0 = <-weaken a<0

    b≤0 : b ≤ 0
    b≤0 = ¬<→≥ ¬0<b

    q<min : q < min₄ (a *ℚ a) (a *ℚ b) (b *ℚ a) (b *ℚ b)
    q<min = min₄-univ-<
      (<-≤-trans q<0 (nonpos-mul a≤0 a≤0))
      (<-≤-trans q<0 (nonpos-mul a≤0 b≤0))
      (<-≤-trans q<0 (nonpos-mul b≤0 a≤0))
      (<-≤-trans q<0 (nonpos-mul b≤0 b≤0))
  ...   | yes 0<b = inc (a , b , a , b , la , ub , la , ub , q<min)
    where
    a≤0 : a ≤ 0
    a≤0 = <-weaken a<0

    0≤b : 0 ≤ b
    0≤b = <-weaken 0<b

    0<-a : 0 < (-ℚ a)
    0<-a = <-resp neg-zero refl (negℚ-anti-< a<0)

    b<δ : b < δ
    b<δ = <-trans (add-pos-< b (-ℚ a) 0<-a) width

    0≤δ-b : 0 ≤ (δ +ℚ (-ℚ b))
    0≤δ-b = <-weaken (<→positive-diff b<δ)

    -b≤0 : (-ℚ b) ≤ 0
    -b≤0 = ≤-resp refl neg-zero (negℚ-anti-≤ 0≤b)

    0≤δ+a : 0 ≤ (δ +ℚ a)
    0≤δ+a = <-weaken (<-≤-trans
      (<-resp refl (shuffle-diff δ a b) (<→positive-diff width))
      (≤-resp refl (+ℚ-idr (δ +ℚ a))
        (+ℚ-preserves-≤ (≤-refl {δ +ℚ a}) -b≤0)))

    ab+δδ : 0 ≤ ((a *ℚ b) +ℚ (δ *ℚ δ))
    ab+δδ = ≤-resp (+ℚ-idr 0) (mixed-corner a b δ)
      (+ℚ-preserves-≤
        (*ℚ-nonnegative 0≤δ+a 0≤b)
        (*ℚ-nonnegative 0≤δ 0≤δ-b))

    q<ab : q < (a *ℚ b)
    q<ab = <-≤-trans q<-δδ
      (≤-resp (+ℚ-idr (-ℚ (δ *ℚ δ))) (cancel-shift a b δ)
        (+ℚ-preserves-≤ (≤-refl { -ℚ (δ *ℚ δ)}) ab+δδ))

    q<min : q < min₄ (a *ℚ a) (a *ℚ b) (b *ℚ a) (b *ℚ b)
    q<min = min₄-univ-<
      (<-≤-trans q<0 (nonpos-mul a≤0 a≤0))
      q<ab
      (<-resp refl (*ℚ-commutative a b) q<ab)
      (<-≤-trans q<0 (*ℚ-nonnegative 0≤b 0≤b))
```

Consequently $1 + h^2 \ge 1$ pointwise, for any real-valued $h$ —
the normalising argument of the patch map lives in the domain of
both the square root and the reciprocal. Since `1ᴿ`{.Agda} *is*
`ratℝ 1`{.Agda}, no bridging path is needed.

```agda
one-plus-sq-lb
  : ∀ {n} (h : Fun n) (x : Fin n → ℝ)
  → ratℝ 1 ≤ᴿ (1ᴿ +ᴿ (h x *ᴿ h x))
one-plus-sq-lb h x =
  sum-≥1 1ᴿ (h x *ᴿ h x) (≤ᴿ-refl {ratℝ 1}) (sq-nonneg (h x))
```

## The patch map

Everything assembles into the **patch map** $x \mapsto x /
\sqrt{1 + x^2}$, the diffeomorphism $\bR \cong (-1,1)$ from which
the differentiably good covers are built. Its domain conditions
are supplied by `one-plus-sq-lb`{.Agda} and `sqrt-≥1`{.Agda}, and
its [[bounded-smoothness|bounded-smooth-function]] is the literal
composite of the closure combinators: the underlying function of
that composite *is* the definition of `patch-fun`{.Agda}, so the
packaging is definitional.

```agda
patch-norm-lb
  : (x : Fin 1 → ℝ) → ratℝ 1 ≤ᴿ (1ᴿ +ᴿ (x fzero *ᴿ x fzero))
patch-norm-lb = one-plus-sq-lb (λ v → v fzero)

patch-sqrt-lb
  : (x : Fin 1 → ℝ)
  → ratℝ 1 ≤ᴿ sqrt (1ᴿ +ᴿ (x fzero *ᴿ x fzero)) (patch-norm-lb x)
patch-sqrt-lb x = sqrt-≥1 (1ᴿ +ᴿ (x fzero *ᴿ x fzero)) (patch-norm-lb x)

patch-fun : Fun 1
patch-fun x =
  x fzero *ᴿ
    recip≥1 (sqrt (1ᴿ +ᴿ (x fzero *ᴿ x fzero)) (patch-norm-lb x))
      (patch-sqrt-lb x)

patch-smooth⁺ : Smooth⁺ 1 patch-fun
patch-smooth⁺ = smooth⁺-mul {1} {λ x → x fzero}
  {λ x → recip≥1 (sqrt (1ᴿ +ᴿ (x fzero *ᴿ x fzero)) (patch-norm-lb x))
      (patch-sqrt-lb x)}
  (smooth⁺-proj fzero)
  (smooth⁺-recip {1} {λ x → sqrt (1ᴿ +ᴿ (x fzero *ᴿ x fzero)) (patch-norm-lb x)}
    (smooth⁺-sqrt {1} {λ x → 1ᴿ +ᴿ (x fzero *ᴿ x fzero)}
      (smooth⁺-add {1} {λ _ → 1ᴿ} {λ x → x fzero *ᴿ x fzero}
        (smooth⁺-const 1ᴿ)
        (smooth⁺-mul {1} {λ x → x fzero} {λ x → x fzero}
          (smooth⁺-proj fzero) (smooth⁺-proj fzero)))
      patch-norm-lb)
    patch-sqrt-lb)
```
