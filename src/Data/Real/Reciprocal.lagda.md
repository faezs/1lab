<!--
```agda
open import 1Lab.Truncation
open import 1Lab.Resizing
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Arithmetic
open import Data.Real.Base
open import Data.Real.Rational
open import Data.Sum
open import Data.Dec
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
