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
open import Data.Real.Reciprocal
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Base
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Sqrt where
```

# Square roots of real numbers at least one {defines="real-square-root"}

A [[Dedekind real|dedekind-real]] $x \ge 1$ has a square root, itself a
real number $\sqrt x \ge 1$, and squaring recovers $x$ on the nose. The
restriction to $x \ge 1$ is deliberate: the downstream consumer is the
patch normalisation $\sqrt{1 + \sum_i x_i^2}$ of the good-cover
diffeomorphisms, whose argument is at least $1$ by construction — and
the restriction makes the cut *clean*, since $\sqrt x \ge 1$ too, so
every rational below $1$ is automatically below the root, and every
rational above the root exceeds $1$.

The cut is stated square-wise: a rational $s$ is *below* $\sqrt x$ when
either $s < 1$ or $s^2$ is below $x$; and $s$ is *above* $\sqrt x$ when
$1 < s$ *and* $s^2$ is above $x$. The hypothesis $1 \le x$ enters in
exactly two places: it makes every $s < 1$ a genuine lower witness
(since $s < 1$ implies $s$ is below $x$, let alone below $\sqrt x$),
and it lets locatedness reduce, for $1 \le q < r$, to locating $x$
between the *squares* $q^2 < r^2$ — a comparison that is monotone
precisely because both sides are nonnegative.

## The square-comparison toolkit

Everything quantitative in this module rests on three pieces of
rational arithmetic: squaring is monotone on nonnegatives, $s \le s^2$
for $s \ge 1$, and a factor of a product exceeding $q \ge 1$ is
positive whenever the other factor is. The expansion identities for
$(s \pm \delta)^2$ and the telescoping identity behind the final
squeeze are decided by the rational ring solver.

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private abstract
  sq-mono-< : ∀ {q r} → 0 ≤ q → q < r → (q *ℚ q) < (r *ℚ r)
  sq-mono-< {q} {r} 0≤q q<r = ≤-<-trans
    (*ℚ-preserves-≤l q 0≤q (<-weaken q<r))
    (*ℚ-preserves-<r r q<r (≤-<-trans 0≤q q<r))

  sq-≥ : ∀ {s} → 1 ≤ s → s ≤ (s *ℚ s)
  sq-≥ {s} 1≤s = ≤-resp (*ℚ-idl s) refl
    (*ℚ-preserves-≤r s 1≤s (≤-trans 0≤1' 1≤s))

  -- A factor of a product exceeding q ≥ 1 is positive whenever the
  -- other factor is: were a ≤ 0, the product a·d would sit at or
  -- below zero, under 1 ≤ q < a·d.
  pos-factor : ∀ q a d → 1 ≤ q → q < (a *ℚ d) → 0 < d → 0 < a
  pos-factor q a d 1≤q q<ad 0<d with holds? (0 < a)
  ... | yes p = p
  ... | no ¬p = absurd (<-irrefl refl
      (<-≤-trans (<-trans (<-≤-trans 0<1' 1≤q) q<ad)
        (≤-resp refl (*ℚ-zerol d)
          (*ℚ-preserves-≤r d (¬<→≥ ¬p) (<-weaken 0<d)))))

  maxℚ-lower-mem
    : ∀ (z : ℝ) {u v} → ∣ z .lower u ∣ → ∣ z .lower v ∣
    → ∣ z .lower (maxℚ u v) ∣
  maxℚ-lower-mem z {u} {v} lu lv with holds? (u ≤ v)
  ... | yes _ = lv
  ... | no _  = lu

  minℚ-upper-mem
    : ∀ (z : ℝ) {u v} → ∣ z .upper u ∣ → ∣ z .upper v ∣
    → ∣ z .upper (minℚ u v) ∣
  minℚ-upper-mem z {u} {v} uu uv with holds? (u ≤ v)
  ... | yes _ = uu
  ... | no _  = uv

  -- (s + δ)² = s² + δ((s+s) + δ), stated without numeral coefficients.
  sq-expand
    : ∀ s d → ((s +ℚ d) *ℚ (s +ℚ d))
            ≡ ((s *ℚ s) +ℚ (d *ℚ ((s +ℚ s) +ℚ d)))
  sq-expand s d = rational!

  -- (s - δ)² = (s² - δ(s+s)) + δ².
  sq-shrink
    : ∀ s d → ((s +ℚ (-ℚ d)) *ℚ (s +ℚ (-ℚ d)))
            ≡ (((s *ℚ s) +ℚ (-ℚ (d *ℚ (s +ℚ s)))) +ℚ (d *ℚ d))
  sq-shrink s d = rational!

  cancel-diff : ∀ a b → (a +ℚ (b +ℚ (-ℚ a))) ≡ b
  cancel-diff a b = rational!

  cancel-neg-diff : ∀ a b → (a +ℚ (-ℚ (a +ℚ (-ℚ b)))) ≡ b
  cancel-neg-diff a b = rational!

  shuffle-neg
    : ∀ s d → ((s +ℚ (-ℚ 1)) +ℚ (-ℚ d)) ≡ ((s +ℚ (-ℚ d)) +ℚ (-ℚ 1))
  shuffle-neg s d = rational!

  -- b² - a² factors through the bracket width b - a.
  diff-sq-factor
    : ∀ a b → ((b +ℚ (-ℚ a)) *ℚ (b +ℚ a))
            ≡ ((b *ℚ b) +ℚ (-ℚ (a *ℚ a)))
  diff-sq-factor a b = rational!

  -- The final squeeze: (q'-q) - (b²-a²) plus b²-q' telescopes to a²-q.
  sq-final
    : ∀ q q' u v
    → (((q' +ℚ (-ℚ q)) +ℚ (-ℚ (v +ℚ (-ℚ u)))) +ℚ (v +ℚ (-ℚ q')))
    ≡ (u +ℚ (-ℚ q))
  sq-final q q' u v = rational!
```
-->

## The cut

A rational $s$ is below $\sqrt x$ when $s < 1$ or $s^2$ is below $x$;
above when $1 < s$ and $s^2$ is above $x$. The lower alternative is
resized into $\Omega$; the upper conjunction is already a proposition.

```agda
module _ (x : ℝ) (x≥1 : ratℝ 1 ≤ᴿ x) where
  private
    Lo Up : Ratio → Type
    Lo s = (s < 1) ⊎ ∣ x .lower (s *ℚ s) ∣
    Up s = (1 < s) × ∣ x .upper (s *ℚ s) ∣

    Up-is-prop : ∀ s → is-prop (Up s)
    Up-is-prop s = ×-is-hlevel 1 (hlevel 1) ((x .upper (s *ℚ s)) .is-tr)
```

The bookkeeping fields: $0$ inhabits the lower cut through the left
disjunct, and for the upper cut we push any upper witness $V$ of $x$ up
to $r = \max(V, 1) + 1$, which satisfies both $1 < r$ and $V < r \le
r^2$ (the last step is $s \le s^2$ for $s \ge 1$). Closure under
shrinking (resp. growing) is monotonicity of squaring, after a
decidable case split on which disjunct applies.

<!--
```agda
    lo-inhab : ∥ Σ Ratio (λ s → □ (Lo s)) ∥
    lo-inhab = inc (0 , inc (inl 0<1'))

    up-inhab : ∥ Σ Ratio (λ r → Up r) ∥
    up-inhab = ∥-∥-map mk (cut.upper-inhab x)
      where
      mk : Σ Ratio (λ V → ∣ x .upper V ∣) → Σ Ratio Up
      mk (V , uV) = r , 1<r , cut.upper-close x V<r² uV
        where
        r : Ratio
        r = maxℚ V 1 +ℚ 1
        m<r : maxℚ V 1 < r
        m<r = add-pos-< (maxℚ V 1) 1 0<1'
        1<r : 1 < r
        1<r = ≤-<-trans (maxℚ-≤r {V} {1}) m<r
        V<r² : V < (r *ℚ r)
        V<r² = <-≤-trans (≤-<-trans (maxℚ-≤l {V} {1}) m<r)
          (sq-≥ (<-weaken 1<r))

    lo-close : ∀ {q r} → q < r → □ (Lo r) → □ (Lo q)
    lo-close {q} {r} q<r = □-map go
      where
      go : Lo r → Lo q
      go (inl r<1) = inl (<-trans q<r r<1)
      go (inr lr²) with holds? (q < 1)
      ... | yes q<1 = inl q<1
      ... | no ¬q<1 = inr (cut.lower-close x
          (sq-mono-< (≤-trans 0≤1' (¬<→≥ ¬q<1)) q<r) lr²)

    up-close : ∀ {q r} → q < r → Up q → Up r
    up-close {q} {r} q<r (1<q , uq²) =
      <-trans 1<q q<r ,
      cut.upper-close x (sq-mono-< (≤-trans 0≤1' (<-weaken 1<q)) q<r) uq²

    disj : ∀ s → □ (Lo s) → Up s → ⊥
    disj s w (1<s , us²) = □-rec (hlevel 1) go w
      where
      go : Lo s → ⊥
      go (inl s<1) = <-irrefl refl (<-trans s<1 1<s)
      go (inr ls²) = cut.cut-disjoint x (s *ℚ s) ls² us²
```
-->

Roundedness is the quantitative part. To push a lower witness $s \ge 1$
strictly upwards, round $x$'s lower cut at $s^2$ to get $s^2 < q'$
still below $x$, and take $\delta$ to be half the minimum of $1$ and
$(q' - s^2)/(2s + 1)$: then

$$
(s + \delta)^2 = s^2 + \delta\,(2s + \delta)
  \le s^2 + \delta\,(2s + 1) < s^2 + (q' - s^2) = q',
$$

where the middle step uses $\delta \le 1$ and the strict step uses
$\delta < (q'-s^2)/(2s+1)$ against the positive denominator. Pushing an
upper witness downwards is mirror-symmetric — $r = s - \delta$ with
$\delta$ below both $(s^2 - q')/2s$ and $s - 1$, the latter keeping $1 <
r$ — using $(s-\delta)^2 = s^2 - \delta \cdot 2s + \delta^2 \ge s^2 -
\delta \cdot 2s$.

<!--
```agda
    lo-round : ∀ s → □ (Lo s) → ∥ Σ Ratio (λ r → (s < r) × □ (Lo r)) ∥
    lo-round s w with holds? (s < 1)
    ... | yes s<1 = inc (midpoint s 1 , mid-<l s<1 , inc (inl (mid-<r s<1)))
    ... | no ¬s<1 = □-rec squash go w
      where
      1≤s : 1 ≤ s
      1≤s = ¬<→≥ ¬s<1

      0<s : 0 < s
      0<s = <-≤-trans 0<1' 1≤s

      go : Lo s → ∥ Σ Ratio (λ r → (s < r) × □ (Lo r)) ∥
      go (inl s<1) = absurd (¬s<1 s<1)
      go (inr ls²) = ∥-∥-map mk (cut.lower-round x (s *ℚ s) ls²)
        where
        mk : Σ Ratio (λ q' → ((s *ℚ s) < q') × ∣ x .lower q' ∣)
           → Σ Ratio (λ r → (s < r) × □ (Lo r))
        mk (q' , s²<q' , lq') =
          s +ℚ δ , add-pos-< s δ 0<δ , inc (inr l-new)
          where
          g D : Ratio
          g = q' +ℚ (-ℚ (s *ℚ s))
          D = (s +ℚ s) +ℚ 1

          0<g : 0 < g
          0<g = <→positive-diff s²<q'

          0<D : 0 < D
          0<D = <-trans (<-trans 0<s (add-pos-< s s 0<s))
            (add-pos-< (s +ℚ s) 1 0<1')

          D-nz : Nonzero D
          D-nz = inc (positive→nonzero (to-positive 0<D))

          gD : Ratio
          gD = (g /ℚ D) ⦃ D-nz ⦄

          m δ : Ratio
          m = minℚ 1 gD
          δ = half m

          0<m : 0 < m
          0<m = minℚ-glb 0<1' (div-pos g D ⦃ D-nz ⦄ 0<g 0<D)

          0<δ : 0 < δ
          0<δ = half-pos 0<m

          δ≤1 : δ ≤ 1
          δ≤1 = <-weaken (<-≤-trans (half-lt 0<m) (minℚ-≤l {1} {gD}))

          δ<gD : δ < gD
          δ<gD = <-≤-trans (half-lt 0<m) (minℚ-≤r {1} {gD})

          small : (δ *ℚ ((s +ℚ s) +ℚ δ)) < g
          small = ≤-<-trans
            (*ℚ-preserves-≤l δ (<-weaken 0<δ)
              (+ℚ-preserves-≤ (≤-refl {s +ℚ s}) δ≤1))
            (<-resp refl (/ℚ-cancel g D ⦃ D-nz ⦄)
              (*ℚ-preserves-<r D δ<gD 0<D))

          key : ((s +ℚ δ) *ℚ (s +ℚ δ)) < q'
          key = <-resp (sym (sq-expand s δ)) (cancel-diff (s *ℚ s) q')
            (+ℚ-preserves-<l (s *ℚ s) small)

          l-new : ∣ x .lower ((s +ℚ δ) *ℚ (s +ℚ δ)) ∣
          l-new = cut.lower-close x key lq'

    up-round : ∀ s → Up s → ∥ Σ Ratio (λ r → (r < s) × Up r) ∥
    up-round s (1<s , us²) = ∥-∥-map mk (cut.upper-round x (s *ℚ s) us²)
      where
      0<s : 0 < s
      0<s = <-trans 0<1' 1<s

      mk : Σ Ratio (λ q' → (q' < (s *ℚ s)) × ∣ x .upper q' ∣)
         → Σ Ratio (λ r → (r < s) × Up r)
      mk (q' , q'<s² , uq') =
        s +ℚ (-ℚ δ) , sub-pos-< s δ 0<δ , 1<r , u-new
        where
        g D : Ratio
        g = (s *ℚ s) +ℚ (-ℚ q')
        D = s +ℚ s

        0<g : 0 < g
        0<g = <→positive-diff q'<s²

        0<D : 0 < D
        0<D = <-trans 0<s (add-pos-< s s 0<s)

        D-nz : Nonzero D
        D-nz = inc (positive→nonzero (to-positive 0<D))

        gD : Ratio
        gD = (g /ℚ D) ⦃ D-nz ⦄

        m δ : Ratio
        m = minℚ gD (s +ℚ (-ℚ 1))
        δ = half m

        0<m : 0 < m
        0<m = minℚ-glb (div-pos g D ⦃ D-nz ⦄ 0<g 0<D)
          (<→positive-diff 1<s)

        0<δ : 0 < δ
        0<δ = half-pos 0<m

        δ<gD : δ < gD
        δ<gD = <-≤-trans (half-lt 0<m) (minℚ-≤l {gD} {s +ℚ (-ℚ 1)})

        δ<s-1 : δ < (s +ℚ (-ℚ 1))
        δ<s-1 = <-≤-trans (half-lt 0<m) (minℚ-≤r {gD} {s +ℚ (-ℚ 1)})

        r : Ratio
        r = s +ℚ (-ℚ δ)

        1<r : 1 < r
        1<r = positive-diff→< {1} {r}
          (<-resp refl (shuffle-neg s δ) (<→positive-diff δ<s-1))

        δD<g : (δ *ℚ D) < g
        δD<g = <-resp refl (/ℚ-cancel g D ⦃ D-nz ⦄)
          (*ℚ-preserves-<r D δ<gD 0<D)

        step1 : q' < ((s *ℚ s) +ℚ (-ℚ (δ *ℚ (s +ℚ s))))
        step1 = <-resp (cancel-neg-diff (s *ℚ s) q') refl
          (+ℚ-preserves-<l (s *ℚ s) (negℚ-anti-< δD<g))

        0≤δδ : 0 ≤ (δ *ℚ δ)
        0≤δδ = <-weaken (from-positive
          (*ℚ-positive (to-positive 0<δ) (to-positive 0<δ)))

        step2 : ((s *ℚ s) +ℚ (-ℚ (δ *ℚ (s +ℚ s)))) ≤ (r *ℚ r)
        step2 = ≤-resp
          (+ℚ-idr ((s *ℚ s) +ℚ (-ℚ (δ *ℚ (s +ℚ s)))))
          (sym (sq-shrink s δ))
          (+ℚ-preserves-≤
            (≤-refl {(s *ℚ s) +ℚ (-ℚ (δ *ℚ (s +ℚ s)))}) 0≤δδ)

        u-new : ∣ x .upper (r *ℚ r) ∣
        u-new = cut.upper-close x (<-≤-trans step1 step2) uq'
```
-->

## Locatedness

Given $q < r$, decide whether $q < 1$. If so, $q$ is below $\sqrt x$
outright. If not, then $0 < 1 \le q < r$, so squaring is strictly
monotone across the gap: $q^2 < r^2$, and locating $x$ between the
squares either puts $q^2$ below $x$ — the right disjunct for $q$ — or
$r^2$ above $x$, which together with $1 \le q < r$ certifies $r$ as an
upper witness.

```agda
    located : ∀ {q r} → q < r → ∥ □ (Lo q) ⊎ Up r ∥
    located {q} {r} q<r with holds? (q < 1)
    ... | yes q<1 = inc (inl (inc (inl q<1)))
    ... | no ¬q<1 = ∥-∥-map pick-side
        (cut.cut-located x (sq-mono-< (≤-trans 0≤1' (¬<→≥ ¬q<1)) q<r))
      where
      pick-side
        : ∣ x .lower (q *ℚ q) ∣ ⊎ ∣ x .upper (r *ℚ r) ∣
        → □ (Lo q) ⊎ Up r
      pick-side (inl l) = inl (inc (inr l))
      pick-side (inr u) = inr (≤-<-trans (¬<→≥ ¬q<1) q<r , u)
```

Assembling the eight fields gives the square-root cut.

```agda
  sqrt-cut : ℝ
  sqrt-cut .lower s = elΩ (Lo s)
  sqrt-cut .upper s = el (Up s) (Up-is-prop s)
  sqrt-cut .has-is-cut = record
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

The root is at least $1$, by the left disjunct.

```agda
  sqrt-cut-≥1 : ratℝ 1 ≤ᴿ sqrt-cut
  sqrt-cut-≥1 q q<1 = inc (inl q<1)
```

## Squaring the root: the easy inclusion

The lower cut of $\sqrt x \cdot \sqrt x$ at $q$ hands us a bracket
$a, c$ below and $b, d$ above the root, with $q$ under all four corner
products. If $q < 1$ then $q$ is below $x$ directly, since $x \ge 1$.
Otherwise $1 \le q$, and both lower witnesses are forced positive
($a \le 0$ would put the corner $a \cdot d$ at or below zero, under
$q$). Now split on the two lower disjuncts: if $a < 1$ then $q < a c <
c$ forces $1 < c$, whose own disjunct must then be the square witness
$c^2$, and $q < c \le c^2$ lands $q$ below $x$; symmetrically for $c <
1$; and if both roots of witnesses are at hand, $q < a c \le M^2$ for
$M = \max(a,c)$, whose square is below $x$ whichever maximum is
chosen.

```agda
  sqrt-cut-sq-≤ : (sqrt-cut *ᴿ sqrt-cut) ≤ᴿ x
  sqrt-cut-sq-≤ q w with holds? (q < 1)
  ... | yes q<1 = x≥1 q q<1
  ... | no ¬q<1 = □-rec (x .lower q .is-tr) main w
    where
    1≤q : 1 ≤ q
    1≤q = ¬<→≥ ¬q<1

    main
      : Σ[ a ∈ Ratio ] Σ[ b ∈ Ratio ] Σ[ c ∈ Ratio ] Σ[ d ∈ Ratio ]
        ∣ sqrt-cut .lower a ∣ × ∣ sqrt-cut .upper b ∣ ×
        ∣ sqrt-cut .lower c ∣ × ∣ sqrt-cut .upper d ∣ ×
        (q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
      → ∣ x .lower q ∣
    main (a , b , c , d , la , ub , lc , ud , q<m) =
      □-rec (x .lower q .is-tr)
        (λ pa → □-rec (x .lower q .is-tr) (go pa) lc)
        la
      where
      0<b : 0 < b
      0<b = <-trans 0<1' (ub .fst)

      0<d : 0 < d
      0<d = <-trans 0<1' (ud .fst)

      q<ac : q < (a *ℚ c)
      q<ac = <-≤-trans q<m (min₄-≤₁ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d})

      q<ad : q < (a *ℚ d)
      q<ad = <-≤-trans q<m (min₄-≤₂ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d})

      q<bc : q < (b *ℚ c)
      q<bc = <-≤-trans q<m (min₄-≤₃ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d})

      0<a : 0 < a
      0<a = pos-factor q a d 1≤q q<ad 0<d

      0<c : 0 < c
      0<c = pos-factor q c b 1≤q
        (<-resp refl (*ℚ-commutative b c) q<bc) 0<b

      go : ((a < 1) ⊎ ∣ x .lower (a *ℚ a) ∣)
         → ((c < 1) ⊎ ∣ x .lower (c *ℚ c) ∣)
         → ∣ x .lower q ∣
      go (inl a<1) pc = from-big-c pc
        where
        q<c : q < c
        q<c = <-trans q<ac
          (<-resp refl (*ℚ-idl c) (*ℚ-preserves-<r c a<1 0<c))

        1<c : 1 < c
        1<c = ≤-<-trans 1≤q q<c

        from-big-c
          : ((c < 1) ⊎ ∣ x .lower (c *ℚ c) ∣) → ∣ x .lower q ∣
        from-big-c (inl c<1) = absurd (<-irrefl refl (<-trans 1<c c<1))
        from-big-c (inr lc²) = cut.lower-close x
          (<-≤-trans q<c (sq-≥ (<-weaken 1<c))) lc²
      go (inr la²) (inl c<1) = cut.lower-close x
          (<-≤-trans q<a (sq-≥ (<-weaken (≤-<-trans 1≤q q<a)))) la²
        where
        q<a : q < a
        q<a = <-trans q<ac
          (<-resp (*ℚ-commutative c a) (*ℚ-idl a)
            (*ℚ-preserves-<r a c<1 0<a))
      go (inr la²) (inr lc²) = cut.lower-close x q<MM lM²
        where
        M : Ratio
        M = maxℚ a c

        0≤M : 0 ≤ M
        0≤M = ≤-trans (<-weaken 0<a) (maxℚ-≤l {a} {c})

        q<MM : q < (M *ℚ M)
        q<MM = <-≤-trans q<ac (≤-trans
          (*ℚ-preserves-≤r c (maxℚ-≤l {a} {c}) (<-weaken 0<c))
          (*ℚ-preserves-≤l M 0≤M (maxℚ-≤r {a} {c})))

        lM² : ∣ x .lower (M *ℚ M) ∣
        lM² with maxℚ-choice a c
        ... | inl e = subst (λ w → ∣ x .lower (w *ℚ w) ∣) (sym e) la²
        ... | inr e = subst (λ w → ∣ x .lower (w *ℚ w) ∣) (sym e) lc²
```

## Squaring the root: the squeeze

For the reverse inclusion, a rational $q$ below $x$ must be exhibited
under a corner bracket of $\sqrt x \cdot \sqrt x$. Round $q$ up to $q'$
still below $x$, fix any upper witness $b_0$ of the root (so $1 <
b_0$), and [[approximate|approx]] the root to width $\delta = (q' -
q)/(b_0 + b_0)$. Intersecting the upper endpoint with $b_0$ and raising
the lower endpoint to at least $\tfrac12$ — legitimate since every
rational below $1$ is below the root — yields a positive bracket $0 < a
< b \le b_0$ of width under $\delta$. The whole game is then the
factorisation

$$
b^2 - a^2 = (b - a)(b + a) < \delta \cdot (b_0 + b_0) = q' - q,
$$

which, combined with $q' < b^2$ (as $b^2$ is above $x$ and $q'$ below),
squeezes $q < a^2$: the diagonal bracket $(a, b, a, b)$ has all four
corners at least $a^2$, so $q$ is below the product.

```agda
  sqrt-cut-sq-≥ : x ≤ᴿ (sqrt-cut *ᴿ sqrt-cut)
  sqrt-cut-sq-≥ q lq =
    ∥-∥-rec sq-prop step1 (cut.lower-round x q lq)
    where
    sq-prop : is-prop ∣ (sqrt-cut *ᴿ sqrt-cut) .lower q ∣
    sq-prop = ((sqrt-cut *ᴿ sqrt-cut) .lower q) .is-tr

    step1
      : Σ Ratio (λ q' → (q < q') × ∣ x .lower q' ∣)
      → ∣ (sqrt-cut *ᴿ sqrt-cut) .lower q ∣
    step1 (q' , q<q' , lq') = ∥-∥-rec sq-prop step2 (cut.upper-inhab sqrt-cut)
      where
      step2
        : Σ Ratio (λ b₀ → ∣ sqrt-cut .upper b₀ ∣)
        → ∣ (sqrt-cut *ᴿ sqrt-cut) .lower q ∣
      step2 (b₀ , ub₀) = ∥-∥-rec sq-prop mk (approx sqrt-cut δ 0<δ)
        where
        0<b₀ : 0 < b₀
        0<b₀ = <-trans 0<1' (ub₀ .fst)

        S : Ratio
        S = b₀ +ℚ b₀

        0<S : 0 < S
        0<S = <-trans 0<b₀ (add-pos-< b₀ b₀ 0<b₀)

        S-nz : Nonzero S
        S-nz = inc (positive→nonzero (to-positive 0<S))

        δ : Ratio
        δ = ((q' +ℚ (-ℚ q)) /ℚ S) ⦃ S-nz ⦄

        0<δ : 0 < δ
        0<δ = div-pos (q' +ℚ (-ℚ q)) S ⦃ S-nz ⦄
          (<→positive-diff q<q') 0<S

        mk
          : Σ Ratio (λ u → Σ Ratio (λ v →
              ∣ sqrt-cut .lower u ∣ × ∣ sqrt-cut .upper v ∣ ×
              ((v +ℚ (-ℚ u)) < δ)))
          → ∣ (sqrt-cut *ᴿ sqrt-cut) .lower q ∣
        mk (a₁ , b₁ , la₁ , ub₁ , w₁) =
          inc (a , b , a , b , la , ub , la , ub , q<min)
          where
          h : Ratio
          h = half 1

          lh : ∣ sqrt-cut .lower h ∣
          lh = inc (inl (half-lt 0<1'))

          a b : Ratio
          a = maxℚ a₁ h
          b = minℚ b₀ b₁

          la : ∣ sqrt-cut .lower a ∣
          la = maxℚ-lower-mem sqrt-cut la₁ lh

          ub : ∣ sqrt-cut .upper b ∣
          ub = minℚ-upper-mem sqrt-cut ub₀ ub₁

          0<a : 0 < a
          0<a = <-≤-trans (half-pos 0<1') (maxℚ-≤r {a₁} {h})

          a<b : a < b
          a<b = lower<upper sqrt-cut la ub

          0<b : 0 < b
          0<b = <-trans 0<a a<b

          b≤b₀ : b ≤ b₀
          b≤b₀ = minℚ-≤l {b₀} {b₁}

          a≤b₀ : a ≤ b₀
          a≤b₀ = <-weaken (<-≤-trans a<b b≤b₀)

          width : (b +ℚ (-ℚ a)) < δ
          width = ≤-<-trans
            (+ℚ-preserves-≤ (minℚ-≤r {b₀} {b₁})
              (negℚ-anti-≤ (maxℚ-≤l {a₁} {h})))
            w₁

          0<b+a : 0 < (b +ℚ a)
          0<b+a = <-trans 0<b (add-pos-< b a 0<a)

          sq-gap : ((b *ℚ b) +ℚ (-ℚ (a *ℚ a))) < (q' +ℚ (-ℚ q))
          sq-gap = <-resp (diff-sq-factor a b)
            (/ℚ-cancel (q' +ℚ (-ℚ q)) S ⦃ S-nz ⦄)
            (<-≤-trans
              (*ℚ-preserves-<r (b +ℚ a) width 0<b+a)
              (*ℚ-preserves-≤l δ (<-weaken 0<δ)
                (+ℚ-preserves-≤ b≤b₀ a≤b₀)))

          q'<b² : q' < (b *ℚ b)
          q'<b² = lower<upper x lq' (ub .snd)

          X Y : Ratio
          X = (q' +ℚ (-ℚ q)) +ℚ (-ℚ ((b *ℚ b) +ℚ (-ℚ (a *ℚ a))))
          Y = (b *ℚ b) +ℚ (-ℚ q')

          0<XY : 0 < (X +ℚ Y)
          0<XY = from-positive (+ℚ-positive
            (to-positive (<→positive-diff sq-gap))
            (to-positive (<→positive-diff q'<b²)))

          q<aa : q < (a *ℚ a)
          q<aa = positive-diff→< {q} {a *ℚ a}
            (<-resp refl (sq-final q q' (a *ℚ a) (b *ℚ b)) 0<XY)

          aa≤ab : (a *ℚ a) ≤ (a *ℚ b)
          aa≤ab = *ℚ-preserves-≤l a (<-weaken 0<a) (<-weaken a<b)

          aa≤ba : (a *ℚ a) ≤ (b *ℚ a)
          aa≤ba = *ℚ-preserves-≤r a (<-weaken a<b) (<-weaken 0<a)

          aa≤bb : (a *ℚ a) ≤ (b *ℚ b)
          aa≤bb = ≤-trans aa≤ba
            (*ℚ-preserves-≤l b (<-weaken 0<b) (<-weaken a<b))

          q<min : q < min₄ (a *ℚ a) (a *ℚ b) (b *ℚ a) (b *ℚ b)
          q<min = min₄-univ-< q<aa
            (<-≤-trans q<aa aa≤ab)
            (<-≤-trans q<aa aa≤ba)
            (<-≤-trans q<aa aa≤bb)
```

## The square root

The exported interface: the root, its lower bound, and the square law,
the latter by [[antisymmetry|dedekind-real]] of the real order.

```agda
sqrt : (x : ℝ) → ratℝ 1 ≤ᴿ x → ℝ
sqrt = sqrt-cut

sqrt-≥1 : ∀ x (p : ratℝ 1 ≤ᴿ x) → ratℝ 1 ≤ᴿ sqrt x p
sqrt-≥1 = sqrt-cut-≥1

sqrt-square : ∀ x (p : ratℝ 1 ≤ᴿ x) → sqrt x p *ᴿ sqrt x p ≡ x
sqrt-square x p = ≤ᴿ-antisym {sqrt x p *ᴿ sqrt x p} {x}
  (sqrt-cut-sq-≤ x p) (sqrt-cut-sq-≥ x p)
```

Since $\tfrac12 < 1$ is always below the root and the upper cut is
(merely) inhabited, the root of a real at least $1$ is a positive real
in the sense of [[reciprocals|real-reciprocal]] — the packaging that
the downstream normalisation $1/\sqrt{1 + \sum_i x_i^2}$ consumes.

```agda
sqrt-bounds : ∀ x (p : ratℝ 1 ≤ᴿ x) → ∥ positive-bounds (sqrt x p) ∥
sqrt-bounds x p = ∥-∥-map mk (cut.upper-inhab (sqrt x p))
  where
  mk : Σ Ratio (λ b → ∣ sqrt x p .upper b ∣) → positive-bounds (sqrt x p)
  mk (b , ub) = record
    { lo     = half 1
    ; hi     = b
    ; lo-mem = inc (inl (half-lt 0<1'))
    ; hi-mem = ub
    ; lo-pos = half-pos 0<1'
    }
```
