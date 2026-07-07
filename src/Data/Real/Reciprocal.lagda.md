<!--
```agda
open import 1Lab.Truncation
open import 1Lab.Resizing
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base
open import Data.Real.Rational
open import Data.Sum
open import Data.Dec
```
-->

<!--
```agda
-- Four-fold minimum lower bounds, re-exposed by name for the
-- inversion argument (the copies in `Rational` suffice; listed here
-- for readability of the corner estimates below).
```
-->

```agda
module Data.Real.Reciprocal where
```

# Reciprocals of positive real numbers {defines="real-reciprocal"}

A [[Dedekind real|dedekind-real]] $x$ that is **strictly positive** —
bounded away from zero below by a positive rational — has a
multiplicative inverse $1/x$, itself a real number, and the product
$x \cdot (1/x)$ is $1$. The construction is the reciprocal of the
[[interval product|real-multiplication]]: where multiplication brackets
each factor and takes the four corner products, inversion brackets the
single factor by a *positive* interval $0 < a \le x \le b$ and reads
off the reciprocal interval $1/b \le 1/x \le 1/a$.

The sign obstruction that makes general reciprocals delicate — $1/x$
is undefined, and its cut ill-behaved, exactly where $x$ can be zero —
is sidestepped here by *carrying the positivity witness as data*. A
positive real is presented together with an explicit rational lower
bound $a_0 > 0$ and upper bound $b_0$, so that every bracket we take
can be intersected with $[a_0, b_0]$ and stays uniformly away from
zero. This makes the locatedness budget — the one genuinely analytic
field of the cut — clean: the spread of the reciprocal interval is
$1/a - 1/b = (b-a)/(ab) \le (b-a)/a_0^2$, controlled by a single
approximation of $x$.

The general apartness case (a real that is merely *nonzero*, i.e.
$x <ᴿ 0ᴿ$ or $0ᴿ <ᴿ x$ decided constructively) is left as future work:
it requires a sign case-split on an apartness witness, threading two
reciprocal constructions through a decidable choice, and is not treated
below.

## The multiplicative comparison lemmas

The reciprocal cut is stated multiplicatively — "$t \cdot b < 1$"
rather than "$t < 1/b$" — to keep `Nonzero`{.Agda} instances out of
the cut data. These two forms are interchangeable whenever $b > 0$,
and translating between them is the only place division appears. We
also need that multiplication by a positive rational *reflects* the
strict order, the converse of `*ℚ-preserves-<r`{.Agda}.

<!--
```agda
private abstract
  *ℚ-reflects-<r : ∀ {u v} w → 0 < w → (u *ℚ w) < (v *ℚ w) → u < v
  *ℚ-reflects-<r {u} {v} w 0<w p with holds? (u < v)
  ... | yes q = q
  ... | no ¬q = absurd (<-irrefl refl (≤-<-trans
      (*ℚ-preserves-≤r w (¬<→≥ ¬q) (<-weaken 0<w)) p))

  mul<1→<inv
    : ∀ t b ⦃ nz : Nonzero b ⦄ → 0 < b → (t *ℚ b) < 1 → t < invℚ b ⦃ nz ⦄
  mul<1→<inv t b ⦃ nz ⦄ 0<b p = *ℚ-reflects-<r b 0<b
    (<-resp refl (sym (*ℚ-invl {b} ⦃ nz ⦄)) p)

  <inv→mul<1
    : ∀ t b ⦃ nz : Nonzero b ⦄ → 0 < b → t < invℚ b ⦃ nz ⦄ → (t *ℚ b) < 1
  <inv→mul<1 t b ⦃ nz ⦄ 0<b p = <-resp refl (*ℚ-invl {b} ⦃ nz ⦄)
    (*ℚ-preserves-<r b p 0<b)

  mul>1→inv<
    : ∀ t a ⦃ nz : Nonzero a ⦄ → 0 < a → 1 < (t *ℚ a) → invℚ a ⦃ nz ⦄ < t
  mul>1→inv< t a ⦃ nz ⦄ 0<a p = *ℚ-reflects-<r a 0<a
    (<-resp (sym (*ℚ-invl {a} ⦃ nz ⦄)) refl p)

  inv<→mul>1
    : ∀ t a ⦃ nz : Nonzero a ⦄ → 0 < a → invℚ a ⦃ nz ⦄ < t → 1 < (t *ℚ a)
  inv<→mul>1 t a ⦃ nz ⦄ 0<a p = <-resp (*ℚ-invl {a} ⦃ nz ⦄) refl
    (*ℚ-preserves-<r a p 0<a)
```
-->

## Positive reals as data

We package a real together with explicit rational bounds pinning it
strictly between $0$ and a finite bound. Everything downstream reads
these off; nothing merely-exists.

```agda
record positive-bounds (x : ℝ) : Type where
  no-eta-equality
  field
    lo hi   : Ratio
    lo-mem  : ∣ x .lower lo ∣
    hi-mem  : ∣ x .upper hi ∣
    lo-pos  : 0 < lo
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

open positive-bounds

private abstract
  bounds-lo<hi : ∀ {x} (p : positive-bounds x) → p .lo < p .hi
  bounds-lo<hi {x} p = lower<upper x (p .lo-mem) (p .hi-mem)

  bounds-hi-pos : ∀ {x} (p : positive-bounds x) → 0 < p .hi
  bounds-hi-pos p = <-trans (p .lo-pos) (bounds-lo<hi p)

  -- A maximum of two lower-cut members is a lower-cut member
  -- (inlined; the `Multiplication` copy is private).
  maxℚ-lower-mem
    : ∀ (z : ℝ) {u v} → ∣ z .lower u ∣ → ∣ z .lower v ∣ → ∣ z .lower (maxℚ u v) ∣
  maxℚ-lower-mem z {u} {v} lu lv with holds? (u ≤ v)
  ... | yes _ = lv
  ... | no _  = lu

  -- The core budget identity, factored out so the ring solver runs on
  -- an abstract goal.
  recip-gap-eq
    : ∀ q r a b → (r *ℚ a) +ℚ (-ℚ (q *ℚ b))
                ≡ ((r +ℚ (-ℚ q)) *ℚ a) +ℚ (q *ℚ (a +ℚ (-ℚ b)))
  recip-gap-eq q r a b = rational!

  -- If a ≥ a₀ > 0 and q > 0, the (r-q)·a term dominates the q·(a-b)
  -- term once the width b-a is small enough (packaged in `budget`).
  recip-gap-pos
    : ∀ q r a b a₀ → q < r → 0 < a₀ → a₀ ≤ a
    → (q *ℚ (b +ℚ (-ℚ a))) < ((r +ℚ (-ℚ q)) *ℚ a₀)
    → (q *ℚ b) < (r *ℚ a)
  recip-gap-pos q r a b a₀ q<r 0<a₀ a₀≤a budget =
    positive-diff→< (<-resp refl (sym (recip-gap-eq q r a b)) gap-pos)
    where
    0<r-q : 0 < (r +ℚ (-ℚ q))
    0<r-q = <→positive-diff q<r
    step1 : (q *ℚ (b +ℚ (-ℚ a))) < ((r +ℚ (-ℚ q)) *ℚ a)
    step1 = <-≤-trans budget
      (*ℚ-preserves-≤l (r +ℚ (-ℚ q)) (<-weaken 0<r-q) a₀≤a)
    gap-pos : 0 < (((r +ℚ (-ℚ q)) *ℚ a) +ℚ (q *ℚ (a +ℚ (-ℚ b))))
    gap-pos = <-resp (+ℚ-invr (q *ℚ (b +ℚ (-ℚ a)))) neg-flip
      (+ℚ-preserves-<r (-ℚ (q *ℚ (b +ℚ (-ℚ a)))) step1)
      where
      neg-flip
        : ((r +ℚ (-ℚ q)) *ℚ a) +ℚ (-ℚ (q *ℚ (b +ℚ (-ℚ a))))
        ≡ ((r +ℚ (-ℚ q)) *ℚ a) +ℚ (q *ℚ (a +ℚ (-ℚ b)))
      neg-flip = ap (((r +ℚ (-ℚ q)) *ℚ a) +ℚ_) lemma
        where
        lemma : (-ℚ (q *ℚ (b +ℚ (-ℚ a)))) ≡ (q *ℚ (a +ℚ (-ℚ b)))
        lemma = rational!

  -- The located decision at a positive-and-tight bracket: commit to
  -- q below or r above, given the width budget.
  recip-decide
    : ∀ q r a b a₀ → q < r → 0 < a₀ → a₀ ≤ a
    → (q *ℚ (b +ℚ (-ℚ a))) < ((r +ℚ (-ℚ q)) *ℚ a₀)
    → ((q *ℚ b) < 1) ⊎ (1 < (r *ℚ a))
  recip-decide q r a b a₀ q<r 0<a₀ a₀≤a budget
    with holds? (q *ℚ b < 1)
  ... | yes p = inl p
  ... | no ¬p = inr (≤-<-trans (¬<→≥ ¬p)
    (recip-gap-pos q r a b a₀ q<r 0<a₀ a₀≤a budget))
```
-->

## The reciprocal cut

A rational $t$ is *below* $1/x$ when $t \cdot b < 1$ for some positive
upper bound $b$ of $x$; dually $t$ is *above* $1/x$ when $1 < t \cdot
a$ for some positive lower bound $a$ of $x$.

```agda
module _ (x : ℝ) (px : positive-bounds x) where
  private
    Lo Up : Ratio → Type
    Lo t = Σ[ b ∈ Ratio ] ∣ x .upper b ∣ × (0 < b) × (t *ℚ b < 1)
    Up t = Σ[ a ∈ Ratio ] ∣ x .lower a ∣ × (0 < a) × (1 < t *ℚ a)
```

<!--
```agda
    b₀ : Ratio
    b₀ = px .hi
    a₀ : Ratio
    a₀ = px .lo
    0<b₀ : 0 < b₀
    0<b₀ = bounds-hi-pos px
    0<a₀ : 0 < a₀
    0<a₀ = px .lo-pos
    a₀-nz : Nonzero a₀
    a₀-nz = inc (positive→nonzero (to-positive 0<a₀))
```
-->

The bookkeeping fields are elementary. For inhabitation of the lower
cut, the recorded upper bound $b_0 > 0$ makes $t = 0$ a witness ($0
\cdot b_0 = 0 < 1$); for the upper cut, $t = 2/a_0$ gives $t \cdot a_0
= 2 > 1$. Roundedness pushes $t$ towards $1/b$ (resp. $1/a$) by a
midpoint, using the comparison lemmas; closure is monotonicity of $t
\mapsto t \cdot b$.

<!--
```agda
    lo-inhab : ∥ Σ Ratio (λ t → □ (Lo t)) ∥
    lo-inhab = inc (0 , inc (b₀ , px .hi-mem , 0<b₀ , 0·b₀<1))
      where
      0·b₀<1 : (0 *ℚ b₀) < 1
      0·b₀<1 = <-resp (sym (*ℚ-zerol b₀)) refl 0<1'

    up-inhab : ∥ Σ Ratio (λ t → □ (Up t)) ∥
    up-inhab = inc (t , inc (a₀ , px .lo-mem , 0<a₀ , 1<t·a₀))
      where
      t : Ratio
      t = 2 *ℚ invℚ a₀ ⦃ a₀-nz ⦄
      t·a₀≡2 : (t *ℚ a₀) ≡ 2
      t·a₀≡2 =
          sym (*ℚ-associative 2 (invℚ a₀ ⦃ a₀-nz ⦄) a₀)
        ∙ ap (2 *ℚ_) (*ℚ-invl {a₀} ⦃ a₀-nz ⦄)
        ∙ *ℚ-idr 2
      two : Ratio
      two = 2
      1<2 : 1 < two
      1<2 = decide!
      1<t·a₀ : 1 < (t *ℚ a₀)
      1<t·a₀ = <-resp refl (sym t·a₀≡2) 1<2

    lo-round : ∀ t → □ (Lo t) → ∥ Σ Ratio (λ s → (t < s) × □ (Lo s)) ∥
    lo-round t = □-rec squash λ (b , ub , 0<b , tb<1) →
      let
        b-nz : Nonzero b
        b-nz = inc (positive→nonzero (to-positive 0<b))
        t<ib : t < invℚ b ⦃ b-nz ⦄
        t<ib = mul<1→<inv t b ⦃ b-nz ⦄ 0<b tb<1
        s : Ratio
        s = midpoint t (invℚ b ⦃ b-nz ⦄)
        sb<1 : (s *ℚ b) < 1
        sb<1 = <inv→mul<1 s b ⦃ b-nz ⦄ 0<b (mid-<r t<ib)
      in inc (s , mid-<l t<ib , inc (b , ub , 0<b , sb<1))

    up-round : ∀ t → □ (Up t) → ∥ Σ Ratio (λ s → (s < t) × □ (Up s)) ∥
    up-round t = □-rec squash λ (a , la , 0<a , 1<ta) →
      let
        a-nz : Nonzero a
        a-nz = inc (positive→nonzero (to-positive 0<a))
        ia<t : invℚ a ⦃ a-nz ⦄ < t
        ia<t = mul>1→inv< t a ⦃ a-nz ⦄ 0<a 1<ta
        s : Ratio
        s = midpoint (invℚ a ⦃ a-nz ⦄) t
        1<sa : 1 < (s *ℚ a)
        1<sa = inv<→mul>1 s a ⦃ a-nz ⦄ 0<a (mid-<l ia<t)
      in inc (s , mid-<r ia<t , inc (a , la , 0<a , 1<sa))

    lo-close : ∀ {q r} → q < r → □ (Lo r) → □ (Lo q)
    lo-close q<r = □-map λ (b , ub , 0<b , rb<1) →
      (b , ub , 0<b , <-trans (*ℚ-preserves-<r b q<r 0<b) rb<1)

    up-close : ∀ {q r} → q < r → □ (Up q) → □ (Up r)
    up-close q<r = □-map λ (a , la , 0<a , 1<qa) →
      (a , la , 0<a , <-trans 1<qa (*ℚ-preserves-<r a q<r 0<a))
```
-->

Disjointness: if $t$ is both below and above $1/x$, we have a positive
upper bound $b$ with $t \cdot b < 1$ and a positive lower bound $a$
with $1 < t \cdot a$. Since $a$ is a lower and $b$ an upper witness of
$x$, `lower<upper`{.Agda} gives $a < b$; and $1 < t \cdot a$ forces $t
> 0$, so $t \cdot a < t \cdot b$, whence $1 < t \cdot a < t \cdot b <
1$ — absurd.

<!--
```agda
    disj : ∀ t → □ (Lo t) → □ (Up t) → ⊥
    disj t = □-rec (hlevel 1) λ (b , ub , 0<b , tb<1) →
             □-rec (hlevel 1) λ (a , la , 0<a , 1<ta) →
      let
        a<b : a < b
        a<b = lower<upper x la ub
        0<t : 0 < t
        0<t = *ℚ-reflects-<r a 0<a (<-resp (sym (*ℚ-zerol a)) refl
          (<-trans 0<1' 1<ta))
        ta<tb : (t *ℚ a) < (t *ℚ b)
        ta<tb = <-resp (*ℚ-commutative a t) (*ℚ-commutative b t)
          (*ℚ-preserves-<r t a<b 0<t)
      in <-irrefl refl (<-trans (<-trans 1<ta ta<tb) tb<1)
```
-->

## Locatedness

Given rationals $q < r$, we must commit: either $q \cdot b < 1$ for
some positive upper bound $b$ (so $q$ is below $1/x$), or $1 < r \cdot
a$ for some positive lower bound $a$ (so $r$ is above $1/x$).

If $q \le 0$ this is immediate: $q \cdot b_0 \le 0 < 1$. Otherwise
$0 < q < r$, and we bracket $x$ to width below $\delta = (r-q) \cdot
a_0 / r$, intersecting the lower endpoint with the recorded bound
$a_0$ so it stays $\ge a_0 > 0$. Then we decide $q \cdot b < 1$:
- if yes, $q$ is below $1/x$;
- if no, then $1 \le q \cdot b$, and the width budget gives $q \cdot b
  < r \cdot a$ (from $r a - q b = (r-q) a + q(a - b)$, with
  $(r-q)a \ge (r-q)a_0 \ge r\delta > q(b-a)$), so $1 < r \cdot a$ and
  $r$ is above $1/x$.

<!--
```agda
    -- q ≤ 0 branch: q·b₀ ≤ 0 < 1.
    located-nonpos : ∀ {q} → q ≤ 0 → □ (Lo q)
    located-nonpos {q} q≤0 = inc (b₀ , px .hi-mem , 0<b₀ , qb₀<1)
      where
      qb₀≤0 : (q *ℚ b₀) ≤ 0
      qb₀≤0 = ≤-resp refl (*ℚ-zerol b₀) (*ℚ-preserves-≤r b₀ q≤0 (<-weaken 0<b₀))
      qb₀<1 : (q *ℚ b₀) < 1
      qb₀<1 = ≤-<-trans qb₀≤0 0<1'

    located : ∀ {q r} → q < r → ∥ □ (Lo q) ⊎ □ (Up r) ∥
    located {q} {r} q<r with holds? (0 < q)
    ... | no ¬0<q = inc (inl (located-nonpos (¬<→≥ ¬0<q)))
    ... | yes 0<q = do
      let
        0<r : 0 < r
        0<r = <-trans 0<q q<r
        r-nz : Nonzero r
        r-nz = inc (positive→nonzero (to-positive 0<r))
        gap : Ratio
        gap = r +ℚ (-ℚ q)
        0<gap : 0 < gap
        0<gap = <→positive-diff q<r
        -- δ = (r-q)·a₀ / r, positive
        δ : Ratio
        δ = ((gap *ℚ a₀) /ℚ r) ⦃ r-nz ⦄
        0<δ : 0 < δ
        0<δ = div-pos (gap *ℚ a₀) r ⦃ r-nz ⦄
          (from-positive (*ℚ-positive (to-positive 0<gap) (to-positive 0<a₀)))
          0<r
      (a₁ , b₁ , la₁ , ub₁ , w₁) ← approx x δ 0<δ
      let
        a : Ratio
        a = maxℚ a₀ a₁
        b : Ratio
        b = b₁
        la : ∣ x .lower a ∣
        la = maxℚ-lower-mem x (px .lo-mem) la₁
        ub : ∣ x .upper b ∣
        ub = ub₁
        a₀≤a : a₀ ≤ a
        a₀≤a = maxℚ-≤l {a₀} {a₁}
        0<a : 0 < a
        0<a = <-≤-trans 0<a₀ a₀≤a
        a<b : a < b
        a<b = lower<upper x la ub
        -- width b - a ≤ b₁ - a₁ < δ
        w≤ : (b +ℚ (-ℚ a)) ≤ (b₁ +ℚ (-ℚ a₁))
        w≤ = +ℚ-preserves-≤ ≤-refl (negℚ-anti-≤ (maxℚ-≤r {a₀} {a₁}))
        w<δ : (b +ℚ (-ℚ a)) < δ
        w<δ = ≤-<-trans w≤ w₁
        0<b : 0 < b
        0<b = <-trans 0<a a<b
        0<w : 0 < (b +ℚ (-ℚ a))
        0<w = <→positive-diff a<b
        rδ≡ : (r *ℚ δ) ≡ ((r +ℚ (-ℚ q)) *ℚ a₀)
        rδ≡ = *ℚ-commutative r δ ∙ /ℚ-cancel (gap *ℚ a₀) r ⦃ r-nz ⦄
        q·w<r·δ : (q *ℚ (b +ℚ (-ℚ a))) < (r *ℚ δ)
        q·w<r·δ = <-trans
          (*ℚ-preserves-<r (b +ℚ (-ℚ a)) q<r 0<w)
          (<-resp (*ℚ-commutative (b +ℚ (-ℚ a)) r) (*ℚ-commutative δ r)
            (*ℚ-preserves-<r r w<δ 0<r))
        budget : (q *ℚ (b +ℚ (-ℚ a))) < ((r +ℚ (-ℚ q)) *ℚ a₀)
        budget = <-resp refl rδ≡ q·w<r·δ
      pure ([ (λ qb<1 → inl (inc (b , ub , 0<b , qb<1)))
            , (λ 1<ra → inr (inc (a , la , 0<a , 1<ra))) ]
            (recip-decide q r a b a₀ q<r 0<a₀ a₀≤a budget))
```
-->

Assembling the eight fields gives the reciprocal cut.

```agda
  recip-cut : ℝ
  recip-cut .lower t = elΩ (Lo t)
  recip-cut .upper t = elΩ (Up t)
  recip-cut .has-is-cut = record
    { lower-inhab  = lo-inhab
    ; upper-inhab  = up-inhab
    ; lower-round  = lo-round
    ; lower-close  = lo-close
    ; upper-round  = up-round
    ; upper-close  = up-close
    ; cut-disjoint = disj
    ; cut-located  = located
    }
```

The reciprocal of a positive real, packaged with its bounds.

```agda
recip : (x : ℝ) → positive-bounds x → ℝ
recip x px = recip-cut x px
```

## Inversion: $x \cdot (1/x) \le 1$

Half of the inverse law is clean. The product's lower cut at $q$ hands
us a bracket $a \le x \le b$ of $x$ and $c \le 1/x \le d$ of its
reciprocal, with $q$ below all four corner products. Unfolding the
reciprocal's *lower* witness $c$ exposes a positive upper bound $\beta$
of $x$ with $c \cdot \beta < 1$, and since $a < \beta$, a two-case
split on the sign of $c$ pins one corner strictly below $1$: if
$c \ge 0$ then $a \cdot c \le \beta \cdot c < 1$, and if $c < 0$ then
$b \cdot c < 0 < 1$ (both $b, \beta > 0$). Either way the four-fold
minimum — hence $q$ — is below $1$.

<!--
```agda
private abstract
  -- 0 < b for any upper bound b of a positive real.
  upper-pos : ∀ (x : ℝ) (px : positive-bounds x) {b} → ∣ x .upper b ∣ → 0 < b
  upper-pos x px {b} ub = <-trans (px .lo-pos) (lower<upper x (px .lo-mem) ub)

  -- The corner estimate: the four-fold minimum of the product bracket
  -- is below 1, using a positive upper bound β of x with c·β < 1.
  corner-<1
    : ∀ a b c d β → 0 < b → 0 < β → a < β → (c *ℚ β) < 1
    → min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) < 1
  corner-<1 a b c d β 0<b 0<β a<β cβ<1 with holds? (0 ≤ c)
  ... | yes 0≤c = ≤-<-trans
    (min₄-≤₁ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}) ac<1
    where
    -- a·c ≤ β·c = c·β < 1
    ac≤βc : (a *ℚ c) ≤ (β *ℚ c)
    ac≤βc = *ℚ-preserves-≤r c (<-weaken a<β) 0≤c
    ac<1 : (a *ℚ c) < 1
    ac<1 = ≤-<-trans ac≤βc (<-resp (*ℚ-commutative c β) refl cβ<1)
  ... | no ¬0≤c = ≤-<-trans
    (min₄-≤₃ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}) bc<1
    where
    c≤0 : c ≤ 0
    c≤0 = ≤-is-weakly-total 0 c ¬0≤c
    bc≤0 : (b *ℚ c) ≤ 0
    bc≤0 = ≤-resp refl (*ℚ-zeror b) (*ℚ-preserves-≤l b (<-weaken 0<b) c≤0)
    bc<1 : (b *ℚ c) < 1
    bc<1 = ≤-<-trans bc≤0 0<1'
```
-->

The forward inclusion assembles the corner estimate: unfold the
reciprocal's lower witness for $\beta$, then apply `corner-<1`{.Agda}.

```agda
recip-invr-≤ : ∀ x (px : positive-bounds x) → (x *ᴿ recip x px) ≤ᴿ 1ᴿ
recip-invr-≤ x px q = □-rec ((1ᴿ .lower q) .is-tr)
  λ (a , b , c , d , la , ub , lc , ud , q<m) →
    □-rec ((1ᴿ .lower q) .is-tr)
      (λ (β , uβ , 0<β , cβ<1) →
        <-trans q<m
          (corner-<1 a b c d β
            (upper-pos x px ub) 0<β
            (lower<upper x la uβ) cβ<1))
      lc
```

## Inversion: $1 \le x \cdot (1/x)$

The reverse inclusion is the budget direction. Given $q < 1$, we
bracket $x$ by a positive interval $a_0 \le a \le x \le b$ so tight
that $q \cdot b < a$, then read off a reciprocal bracket for $1/x$:
take $c$ a midpoint between $q/a$ and $1/b$ (so $q < a \cdot c$ and
$c \cdot b < 1$, the latter certifying $c$ is *below* $1/x$ with
witness $b$), and $d = 2/a$ (so $1 < d \cdot a$, certifying $d$ is
*above* $1/x$ with witness $a$). With $c, d > 0$ and $a, b > 0$ every
corner exceeds $q$: the binding one is $a \cdot c > a \cdot (q/a) = q$.

The tightness $q \cdot b < a$ is where a single approximation of $x$ is
spent: with width $b - a < \varepsilon$ and $a \ge a_0$, we have
$q b < q a + q\varepsilon$, and choosing $\varepsilon$ below
$a_0 (1 - q) / (1 + |q|)$ keeps this below $a$. For $q \le 0$ the
condition is immediate ($qb \le 0 < a$).

<!--
```agda
private abstract
  -- a · (q · a⁻¹) = q.
  a·q/a≡q : ∀ a q ⦃ nz : Nonzero a ⦄ → (a *ℚ (q *ℚ invℚ a ⦃ nz ⦄)) ≡ q
  a·q/a≡q a q ⦃ nz ⦄ =
      ap (a *ℚ_) (*ℚ-commutative q (invℚ a ⦃ nz ⦄))
    ∙ *ℚ-associative a (invℚ a ⦃ nz ⦄) q
    ∙ ap (_*ℚ q) (*ℚ-invr {a} {nz})
    ∙ *ℚ-idl q

  -- q/a < 1/b from the tightness q·b < a (a,b > 0).
  tight→recip-< : ∀ a b q ⦃ na : Nonzero a ⦄ ⦃ nb : Nonzero b ⦄
    → 0 < a → 0 < b → (q *ℚ b) < a
    → (q *ℚ invℚ a ⦃ na ⦄) < invℚ b ⦃ nb ⦄
  tight→recip-< a b q ⦃ na ⦄ ⦃ nb ⦄ 0<a 0<b qb<a =
    *ℚ-reflects-<r b 0<b (<-resp (sym qa-eq) (sym ib-eq) qb·<)
    where
    0<ia : 0 < invℚ a ⦃ na ⦄
    0<ia = invℚ-pos ⦃ na ⦄ 0<a
    -- (q·a⁻¹)·b < 1 : since q·b < a, multiply by a⁻¹>0 and cancel.
    qb·< : ((q *ℚ b) *ℚ invℚ a ⦃ na ⦄) < (a *ℚ invℚ a ⦃ na ⦄)
    qb·< = *ℚ-preserves-<r (invℚ a ⦃ na ⦄) qb<a 0<ia
    qa-eq : (q *ℚ invℚ a ⦃ na ⦄) *ℚ b ≡ (q *ℚ b) *ℚ invℚ a ⦃ na ⦄
    qa-eq = rational!
    ib-eq : invℚ b ⦃ nb ⦄ *ℚ b ≡ (a *ℚ invℚ a ⦃ na ⦄)
    ib-eq = *ℚ-invl {b} ⦃ nb ⦄ ∙ sym (*ℚ-invr {a} {na})

  -- With ε = a₀·(1-q) and a ≥ a₀ > 0, a bracket of width b - a < ε
  -- around a positive real gives the tightness q·b < a (case q > 0).
  tightness
    : ∀ a₀ a b q → 0 < a₀ → a₀ ≤ a → 0 < q → q < 1
    → (b +ℚ (-ℚ a)) < (a₀ *ℚ (1 +ℚ (-ℚ q)))
    → (q *ℚ b) < a
  tightness a₀ a b q 0<a₀ a₀≤a 0<q q<1 w<ε =
    positive-diff→< (<-resp refl (sym gap-eq) 0<gap)
    where
    W E A : Ratio
    W = b +ℚ (-ℚ a)
    E = a₀ *ℚ (1 +ℚ (-ℚ q))
    A = a *ℚ (1 +ℚ (-ℚ q))
    0<1-q : 0 < (1 +ℚ (-ℚ q))
    0<1-q = <→positive-diff q<1
    0<E : 0 < E
    0<E = from-positive (*ℚ-positive (to-positive 0<a₀) (to-positive 0<1-q))
    -- q·W < q·E < E ≤ A
    qW<qE : (q *ℚ W) < (q *ℚ E)
    qW<qE = <-resp (*ℚ-commutative W q) (*ℚ-commutative E q)
      (*ℚ-preserves-<r q w<ε 0<q)
    qE<E : (q *ℚ E) < E
    qE<E = <-resp refl (*ℚ-idl E)
      (*ℚ-preserves-<r E q<1 0<E)
    E≤A : E ≤ A
    E≤A = *ℚ-preserves-≤r (1 +ℚ (-ℚ q)) a₀≤a (<-weaken 0<1-q)
    qW<A : (q *ℚ W) < A
    qW<A = <-≤-trans (<-trans qW<qE qE<E) E≤A
    gap-eq : (a +ℚ (-ℚ (q *ℚ b))) ≡ (A +ℚ (-ℚ (q *ℚ W)))
    gap-eq = rational!
    0<gap : 0 < (A +ℚ (-ℚ (q *ℚ W)))
    0<gap = <→positive-diff qW<A
```
-->

Given a positive bracket $a \le x \le b$ satisfying the tightness
$q \cdot b < a$, the core builds the product witness: $c$ is a midpoint
between $\max(0, q/a)$ and $1/b$ (so $0 < c$, $c \cdot b < 1$, and
$q < a \cdot c$), and $d = 2/a$ (so $1 < d \cdot a$). All four corners
exceed $q$.

<!--
```agda
private
  invr-core
    : ∀ (x : ℝ) (px : positive-bounds x) q a b
    → ∣ x .lower a ∣ → ∣ x .upper b ∣ → 0 < a → a < b → q < 1
    → (q *ℚ b) < a
    → ∣ (x *ᴿ recip x px) .lower q ∣
  invr-core x px q a b la ub 0<a a<b q<1 qb<a =
    inc (a , b , c , d , la , ub , lc , ud , q<min)
    where
    0<b : 0 < b
    0<b = <-trans 0<a a<b
    a-nz : Nonzero a
    a-nz = inc (positive→nonzero (to-positive 0<a))
    b-nz : Nonzero b
    b-nz = inc (positive→nonzero (to-positive 0<b))
    ia ib : Ratio
    ia = invℚ a ⦃ a-nz ⦄
    ib = invℚ b ⦃ b-nz ⦄
    0<ib : 0 < ib
    0<ib = invℚ-pos ⦃ b-nz ⦄ 0<b
    m : Ratio
    m = maxℚ 0 (q *ℚ ia)
    q/a<ib : (q *ℚ ia) < ib
    q/a<ib = tight→recip-< a b q ⦃ a-nz ⦄ ⦃ b-nz ⦄ 0<a 0<b qb<a
    m<ib : m < ib
    m<ib = maxℚ-lub 0<ib q/a<ib
    c d : Ratio
    c = midpoint m ib
    d = 2 *ℚ ia
    0≤m : 0 ≤ m
    0≤m = maxℚ-≤l {0} {q *ℚ ia}
    m<c : m < c
    m<c = mid-<l m<ib
    0<c : 0 < c
    0<c = ≤-<-trans 0≤m m<c
    c<ib : c < ib
    c<ib = mid-<r m<ib
    -- membership of c in recip's lower cut (witness b)
    cb<1 : (c *ℚ b) < 1
    cb<1 = <inv→mul<1 c b ⦃ b-nz ⦄ 0<b c<ib
    lc : ∣ recip x px .lower c ∣
    lc = inc (b , ub , 0<b , cb<1)
    -- membership of d in recip's upper cut (witness a): d·a = 2 > 1
    d·a≡2 : (d *ℚ a) ≡ 2
    d·a≡2 =
        sym (*ℚ-associative 2 ia a)
      ∙ ap (2 *ℚ_) (*ℚ-invl {a} ⦃ a-nz ⦄)
      ∙ *ℚ-idr 2
    two : Ratio
    two = 2
    1<2 : 1 < two
    1<2 = decide!
    1<d·a : 1 < (d *ℚ a)
    1<d·a = <-resp refl (sym d·a≡2) 1<2
    ud : ∣ recip x px .upper d ∣
    ud = inc (a , la , 0<a , 1<d·a)
    -- the four corner estimates, all above q
    q/a<c : (q *ℚ ia) < c
    q/a<c = ≤-<-trans (maxℚ-≤r {0} {q *ℚ ia}) m<c
    q<ac : q < (a *ℚ c)
    q<ac = <-resp
      (*ℚ-commutative (q *ℚ ia) a ∙ a·q/a≡q a q ⦃ a-nz ⦄)
      (*ℚ-commutative c a)
      (*ℚ-preserves-<r a q/a<c 0<a)
    q<bc : q < (b *ℚ c)
    q<bc = <-trans q<ac (*ℚ-preserves-<r c a<b 0<c)
    0<ia : 0 < ia
    0<ia = invℚ-pos ⦃ a-nz ⦄ 0<a
    0<d : 0 < d
    0<d = from-positive (*ℚ-positive (to-positive 0<2) (to-positive 0<ia))
      where
      twoR : Ratio
      twoR = 2
      0<2 : 0 < twoR
      0<2 = decide!
    q<da : q < (d *ℚ a)
    q<da = <-trans q<1 1<d·a
    q<ad : q < (a *ℚ d)
    q<ad = <-resp refl (*ℚ-commutative d a) q<da
    q<bd : q < (b *ℚ d)
    q<bd = <-trans q<ad (*ℚ-preserves-<r d a<b 0<d)
    q<min : q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    q<min = min₄-univ-< q<ac q<ad q<bc q<bd
```
-->

The wrapper supplies the bracket. For $q \le 0$ the recorded bounds
$a_0 \le x \le b_0$ already satisfy $q \cdot b_0 \le 0 < a_0$; for
$0 < q < 1$ we approximate $x$ to width $\varepsilon = a_0 (1 - q)$,
intersect the lower endpoint with $a_0$, and read off tightness from
`tightness`{.Agda}.

```agda
recip-invr-≥ : ∀ x (px : positive-bounds x) → 1ᴿ ≤ᴿ (x *ᴿ recip x px)
recip-invr-≥ x px q q<1 with holds? (0 < q)
... | no ¬0<q = invr-core x px q (px .lo) (px .hi)
      (px .lo-mem) (px .hi-mem) (px .lo-pos)
      (lower<upper x (px .lo-mem) (px .hi-mem)) q<1 qb₀<a₀
  where
  q≤0 : q ≤ 0
  q≤0 = ¬<→≥ ¬0<q
  0<b₀ : 0 < px .hi
  0<b₀ = <-trans (px .lo-pos) (lower<upper x (px .lo-mem) (px .hi-mem))
  qb₀≤0 : (q *ℚ px .hi) ≤ 0
  qb₀≤0 = ≤-resp refl (*ℚ-zerol (px .hi))
    (*ℚ-preserves-≤r (px .hi) q≤0 (<-weaken 0<b₀))
  qb₀<a₀ : (q *ℚ px .hi) < px .lo
  qb₀<a₀ = ≤-<-trans qb₀≤0 (px .lo-pos)
... | yes 0<q = ∥-∥-rec ((x *ᴿ recip x px) .lower q .is-tr) mk (approx x ε 0<ε)
  where
  a₀ : Ratio
  a₀ = px .lo
  0<a₀ : 0 < a₀
  0<a₀ = px .lo-pos
  0<1-q : 0 < (1 +ℚ (-ℚ q))
  0<1-q = <→positive-diff q<1
  ε : Ratio
  ε = a₀ *ℚ (1 +ℚ (-ℚ q))
  0<ε : 0 < ε
  0<ε = from-positive (*ℚ-positive (to-positive 0<a₀) (to-positive 0<1-q))
  mk : Σ Ratio (λ u → Σ Ratio (λ v →
         ∣ x .lower u ∣ × ∣ x .upper v ∣ × ((v +ℚ (-ℚ u)) < ε)))
     → ∣ (x *ᴿ recip x px) .lower q ∣
  mk (a₁ , b₁ , la₁ , ub₁ , w₁) =
    invr-core x px q a b la ub 0<a a<b q<1 qb<a
    where
    a : Ratio
    a = maxℚ a₀ a₁
    b : Ratio
    b = b₁
    la : ∣ x .lower a ∣
    la = maxℚ-lower-mem x (px .lo-mem) la₁
    ub : ∣ x .upper b ∣
    ub = ub₁
    a₀≤a : a₀ ≤ a
    a₀≤a = maxℚ-≤l {a₀} {a₁}
    0<a : 0 < a
    0<a = <-≤-trans 0<a₀ a₀≤a
    a<b : a < b
    a<b = lower<upper x la ub
    w≤ : (b +ℚ (-ℚ a)) ≤ (b₁ +ℚ (-ℚ a₁))
    w≤ = +ℚ-preserves-≤ ≤-refl (negℚ-anti-≤ (maxℚ-≤r {a₀} {a₁}))
    w<ε : (b +ℚ (-ℚ a)) < ε
    w<ε = ≤-<-trans w≤ w₁
    qb<a : (q *ℚ b) < a
    qb<a = tightness a₀ a b q 0<a₀ a₀≤a 0<q q<1 w<ε
```

## The inverse law

Antisymmetry of the real order combines the two inequalities into the
inverse law: a strictly positive real, multiplied by its reciprocal,
is $1$.

```agda
recip-invr : ∀ x (px : positive-bounds x) → x *ᴿ recip x px ≡ 1ᴿ
recip-invr x px = ≤ᴿ-antisym (recip-invr-≤ x px) (recip-invr-≥ x px)
```

## What is proven, and what is not

The reciprocal `recip`{.Agda} of a strictly positive real (presented
with explicit rational bounds `positive-bounds`{.Agda}) is a genuine
[[Dedekind real|dedekind-real]] — all eight cut axioms, including the
analytic `cut-located`{.Agda}, hold with **zero postulates** — and it
satisfies the full inverse law `recip-invr`{.Agda}: $x \cdot (1/x) = 1$.

Two directions of generality are deliberately *not* treated here, and
are honest gaps rather than hidden assumptions:

- **Apartness / the general sign case.** Only strictly positive reals
  are inverted. A merely *nonzero* real — one apart from $0$, i.e.
  $x <ᴿ 0ᴿ$ or $0ᴿ <ᴿ x$ constructively decided — would require a sign
  case-split on the apartness witness and a mirrored construction for
  the negative branch. This is left as future work.

- **Bounds as data, not as a proposition.** `positive-bounds`{.Agda}
  carries explicit rational witnesses $a_0, b_0$. A cleaner interface
  would derive them from the mere positivity $0ᴿ <ᴿ x$ (which supplies
  a positive lower bound) together with the real's own
  `upper-inhab`{.Agda} (an upper bound), packaging positivity as a
  proposition; the reciprocal is independent of the chosen bounds by
  `≤ᴿ-antisym`{.Agda}, but that invariance is not formalized here.
```

