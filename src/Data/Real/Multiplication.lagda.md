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
module Data.Real.Multiplication where
```

# Multiplication of real numbers {defines="real-multiplication interval-product"}

Multiplying [[Dedekind cuts|dedekind-cut]] is notoriously more
delicate than [[adding|real-addition]] them: the naive "product of
lower cuts" fails as soon as a factor can be negative, and the
textbook constructive fix — a case analysis on the signs of the
factors — is unavailable here, since the sign of a real number is
not decidable. We instead follow the **interval product** (or Moore
product) recipe from interval arithmetic: a rational $q$ is below
$x \cdot y$ when, for some rational bracket $a < x < b$, $c < y < d$
around the factors, $q$ is below *all four* of the products $ac, ad,
bc, bd$ — and dually, $q$ is above $x \cdot y$ when it is above all
four. No sign analysis ever happens: the four products
conservatively cover every possible sign configuration at once.

The whole construction rests on a single piece of rational
arithmetic, the **bracketing lemma**: if $a \le u \le b$ and $c \le
v \le d$, then

$$
\min(ac, ad, bc, bd) \;\le\; uv \;\le\; \max(ac, ad, bc, bd).
$$

Classically one proves this by (many) sign cases. Constructively we
can do better, and the proof is genuinely pretty: since the order on
$\bQ$ *is* decidable, we may assume $c < d$ strictly (else the
bracket collapses and the claim is trivial), write $v$ as a **convex
combination** $v = tc + (1-t)d$ with $t = (d-v)/(d-c) \in [0,1]$,
and observe that multiplication by $u$ sends convex combinations to
convex combinations, which stay between the min and the max of
their endpoints. Everything else in this module — well-definedness
of the cut, disjointness, and the $\varepsilon$-management for
locatedness — is bookkeeping on top of this lemma.

## The rational toolkit

The strict-order arithmetic, halving, monotonicity of multiplication,
and the binary and four-fold extrema that the interval product needs
are collected once in the [[rational toolkit|rational-toolkit]]
module, which we import. The only facts specific to the reals are
that a maximum of two lower bounds is a lower bound, and dually a
minimum of two upper bounds is an upper bound.

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private abstract
  maxℚ-lower-mem : ∀ (z : ℝ) {u v} → ∣ z .lower u ∣ → ∣ z .lower v ∣ → ∣ z .lower (maxℚ u v) ∣
  maxℚ-lower-mem z {u} {v} lu lv with holds? (u ≤ v)
  ... | yes _ = lv
  ... | no _  = lu

  minℚ-upper-mem : ∀ (z : ℝ) {u v} → ∣ z .upper u ∣ → ∣ z .upper v ∣ → ∣ z .upper (minℚ u v) ∣
  minℚ-upper-mem z {u} {v} uu uv with holds? (u ≤ v)
  ... | yes _ = uu
  ... | no _  = uv
```
-->

## Convex combinations and the bracketing lemma

A convex combination $tp + (1-t)q$ with $0 \le t \le 1$ lies between
$\min(p,q)$ and $\max(p,q)$: multiply the two inequalities
$\min(p,q) \le p$ and $\min(p,q) \le q$ by the nonnegative weights
$t$ and $1-t$ and add. If additionally $c < d$ strictly, any $v$
with $c \le v \le d$ *is* a convex combination of $c$ and $d$, with
weight $t = (d-v)/(d-c)$ — this is where rational division enters,
and where the interval product earns its freedom from sign
analysis. The one-variable bracketing lemma follows: for any
rational scalar $p$,

$$
\min(pc, pd) \;\le\; pv \;\le\; \max(pc, pd),
$$

with the degenerate case $\neg(c < d)$ handled by antisymmetry
($c = v = d$, so the claim is reflexivity). Applying the
one-variable lemma three times — once in the scalar, twice in the
point — gives the two-variable bracketing lemma announced above.

<!--
```agda
private abstract
  convex-lower
    : ∀ p q t → 0 ≤ t → t ≤ 1
    → minℚ p q ≤ ((t *ℚ p) +ℚ ((1 +ℚ (-ℚ t)) *ℚ q))
  convex-lower p q t h0 h1 = ≤-resp collapse refl (+ℚ-preserves-≤ s1 s2)
    where
    m : Ratio
    m = minℚ p q

    s1 : (t *ℚ m) ≤ (t *ℚ p)
    s1 = *ℚ-preserves-≤l t h0 (minℚ-≤l {p} {q})

    s2 : ((1 +ℚ (-ℚ t)) *ℚ m) ≤ ((1 +ℚ (-ℚ t)) *ℚ q)
    s2 = *ℚ-preserves-≤l (1 +ℚ (-ℚ t)) (≤→diff-nonneg h1) (minℚ-≤r {p} {q})

    collapse : ((t *ℚ m) +ℚ ((1 +ℚ (-ℚ t)) *ℚ m)) ≡ m
    collapse = rational!

  convex-upper
    : ∀ p q t → 0 ≤ t → t ≤ 1
    → ((t *ℚ p) +ℚ ((1 +ℚ (-ℚ t)) *ℚ q)) ≤ maxℚ p q
  convex-upper p q t h0 h1 = ≤-resp refl collapse (+ℚ-preserves-≤ s1 s2)
    where
    m : Ratio
    m = maxℚ p q

    s1 : (t *ℚ p) ≤ (t *ℚ m)
    s1 = *ℚ-preserves-≤l t h0 (maxℚ-≤l {p} {q})

    s2 : ((1 +ℚ (-ℚ t)) *ℚ q) ≤ ((1 +ℚ (-ℚ t)) *ℚ m)
    s2 = *ℚ-preserves-≤l (1 +ℚ (-ℚ t)) (≤→diff-nonneg h1) (maxℚ-≤r {p} {q})

    collapse : ((t *ℚ m) +ℚ ((1 +ℚ (-ℚ t)) *ℚ m)) ≡ m
    collapse = rational!

  /ℚ-≤-one
    : ∀ u w (nz : Nonzero w) → 0 ≤ u → u ≤ w → 0 < w
    → ((u /ℚ w) ⦃ nz ⦄ ≤ 1)
  /ℚ-≤-one u w nz h0 hw pw = ≤-resp
    (sym (/ℚ-def {u} {w} ⦃ nz ⦄)) (*ℚ-invr {w} {nz})
    (*ℚ-preserves-≤r (invℚ w ⦃ nz ⦄) hw inv-nn)
    where
    inv-nn : 0 ≤ invℚ w ⦃ nz ⦄
    inv-nn = invℚ-nonnegative ⦃ nz ⦄ (<-weaken pw)

  interp-mul-eq
    : ∀ c d v p (nz : Nonzero (d +ℚ (-ℚ c)))
    → (((((d +ℚ (-ℚ v)) /ℚ (d +ℚ (-ℚ c))) ⦃ nz ⦄) *ℚ (p *ℚ c)) +ℚ
       ((1 +ℚ (-ℚ (((d +ℚ (-ℚ v)) /ℚ (d +ℚ (-ℚ c))) ⦃ nz ⦄))) *ℚ (p *ℚ d)))
      ≡ (p *ℚ v)
  interp-mul-eq c d v p nz = rational!

  bracket₁-lower
    : ∀ p v c d → c ≤ v → v ≤ d
    → minℚ (p *ℚ c) (p *ℚ d) ≤ (p *ℚ v)
  bracket₁-lower p v c d cv vd with holds? (c < d)
  bracket₁-lower p v c d cv vd | yes c<d =
    ≤-resp refl (interp-mul-eq c d v p nz) (convex-lower (p *ℚ c) (p *ℚ d) t t0 t1)
    where
    nz : Nonzero (d +ℚ (-ℚ c))
    nz = inc (positive→nonzero (to-positive (<→positive-diff c<d)))

    t : Ratio
    t = ((d +ℚ (-ℚ v)) /ℚ (d +ℚ (-ℚ c))) ⦃ nz ⦄

    t0 : 0 ≤ t
    t0 = /ℚ-nonnegative ⦃ nz ⦄ (≤→diff-nonneg vd) (<-weaken (<→positive-diff c<d))

    t1 : t ≤ 1
    t1 = /ℚ-≤-one (d +ℚ (-ℚ v)) (d +ℚ (-ℚ c)) nz
      (≤→diff-nonneg vd)
      (+ℚ-preserves-≤ ≤-refl (negℚ-anti-≤ cv))
      (<→positive-diff c<d)
  bracket₁-lower p v c d cv vd | no ¬p =
    subst (λ z → minℚ (p *ℚ c) (p *ℚ d) ≤ (p *ℚ z)) (sym v≡c) (minℚ-≤l {p *ℚ c} {p *ℚ d})
    where
    v≡c : v ≡ c
    v≡c = ≤-antisym (≤-trans vd (¬<→≥ ¬p)) cv

  bracket₁-upper
    : ∀ p v c d → c ≤ v → v ≤ d
    → (p *ℚ v) ≤ maxℚ (p *ℚ c) (p *ℚ d)
  bracket₁-upper p v c d cv vd with holds? (c < d)
  bracket₁-upper p v c d cv vd | yes c<d =
    ≤-resp (interp-mul-eq c d v p nz) refl (convex-upper (p *ℚ c) (p *ℚ d) t t0 t1)
    where
    nz : Nonzero (d +ℚ (-ℚ c))
    nz = inc (positive→nonzero (to-positive (<→positive-diff c<d)))

    t : Ratio
    t = ((d +ℚ (-ℚ v)) /ℚ (d +ℚ (-ℚ c))) ⦃ nz ⦄

    t0 : 0 ≤ t
    t0 = /ℚ-nonnegative ⦃ nz ⦄ (≤→diff-nonneg vd) (<-weaken (<→positive-diff c<d))

    t1 : t ≤ 1
    t1 = /ℚ-≤-one (d +ℚ (-ℚ v)) (d +ℚ (-ℚ c)) nz
      (≤→diff-nonneg vd)
      (+ℚ-preserves-≤ ≤-refl (negℚ-anti-≤ cv))
      (<→positive-diff c<d)
  bracket₁-upper p v c d cv vd | no ¬p =
    subst (λ z → (p *ℚ z) ≤ maxℚ (p *ℚ c) (p *ℚ d)) (sym v≡c) (maxℚ-≤l {p *ℚ c} {p *ℚ d})
    where
    v≡c : v ≡ c
    v≡c = ≤-antisym (≤-trans vd (¬<→≥ ¬p)) cv

  bracket-lower
    : ∀ u v a b c d → a ≤ u → u ≤ b → c ≤ v → v ≤ d
    → min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (u *ℚ v)
  bracket-lower u v a b c d au ub cv vd =
    ≤-trans (minℚ-glb-≤ m-uc m-ud) (bracket₁-lower u v c d cv vd)
    where
    m-uc : min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (u *ℚ c)
    m-uc = ≤-resp refl (*ℚ-commutative c u)
      (≤-trans
        (minℚ-glb-≤
          (≤-resp refl (*ℚ-commutative a c) (min₄-≤₁ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
          (≤-resp refl (*ℚ-commutative b c) (min₄-≤₃ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d})))
        (bracket₁-lower c u a b au ub))

    m-ud : min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (u *ℚ d)
    m-ud = ≤-resp refl (*ℚ-commutative d u)
      (≤-trans
        (minℚ-glb-≤
          (≤-resp refl (*ℚ-commutative a d) (min₄-≤₂ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
          (≤-resp refl (*ℚ-commutative b d) (min₄-≤₄ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d})))
        (bracket₁-lower d u a b au ub))

  bracket-upper
    : ∀ u v a b c d → a ≤ u → u ≤ b → c ≤ v → v ≤ d
    → (u *ℚ v) ≤ max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
  bracket-upper u v a b c d au ub cv vd =
    ≤-trans (bracket₁-upper u v c d cv vd) (maxℚ-lub-≤ m-uc m-ud)
    where
    m-uc : (u *ℚ c) ≤ max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    m-uc = ≤-resp (*ℚ-commutative c u) refl
      (≤-trans
        (bracket₁-upper c u a b au ub)
        (maxℚ-lub-≤
          (≤-resp (*ℚ-commutative a c) refl (max₄-≥₁ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
          (≤-resp (*ℚ-commutative b c) refl (max₄-≥₃ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))))

    m-ud : (u *ℚ d) ≤ max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    m-ud = ≤-resp (*ℚ-commutative d u) refl
      (≤-trans
        (bracket₁-upper d u a b au ub)
        (maxℚ-lub-≤
          (≤-resp (*ℚ-commutative a d) refl (max₄-≥₂ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
          (≤-resp (*ℚ-commutative b d) refl (max₄-≥₄ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))))
```
-->

## Bounding the spread of a bracket

For disjointness the bracketing lemma is already enough, but
locatedness needs a quantitative refinement: how far apart can the
four products of a bracket be? Telescoping, for factors $u, u'$
bounded in absolute value by $B_2$ and $v, v'$ bounded by $B_1$,

$$
uv - u'v' \;=\; u(v - v') + v'(u - u'),
$$

so if moreover the differences are bounded by the widths of the
respective brackets, the spread $\max_4 - \min_4$ is at most $B_2
\cdot (d - c) + B_1 \cdot (b - a)$. Absolute values are avoided
throughout: "$|z| \le B$" is systematically tracked as the pair
$-B \le z$ and $z \le B$, and the only fact needed about such
two-sided bounds is that they multiply, which is one decidable case
split on the sign of the second factor.

<!--
```agda
private abstract
  abs-mul-bound
    : ∀ z w B W
    → ((-ℚ B) ≤ z) → (z ≤ B) → ((-ℚ W) ≤ w) → (w ≤ W) → 0 ≤ B
    → ((z *ℚ w) ≤ (B *ℚ W))
  abs-mul-bound z w B W lo hi wlo whi nnB with holds? (0 ≤ w)
  abs-mul-bound z w B W lo hi wlo whi nnB | yes h =
    ≤-trans (*ℚ-preserves-≤r w hi h) (*ℚ-preserves-≤l B nnB whi)
  abs-mul-bound z w B W lo hi wlo whi nnB | no ¬h =
    ≤-resp flip-sign refl (≤-trans (*ℚ-preserves-≤r (-ℚ w) negz nw-nn) (*ℚ-preserves-≤l B nnB nwW))
    where
    w≤0 : w ≤ 0
    w≤0 = ≤-is-weakly-total 0 w ¬h

    nw-nn : 0 ≤ (-ℚ w)
    nw-nn = ≤-resp neg-zero refl (negℚ-anti-≤ w≤0)

    negz : (-ℚ z) ≤ B
    negz = ≤-resp refl (negℚ-invol B) (negℚ-anti-≤ lo)

    nwW : (-ℚ w) ≤ W
    nwW = ≤-resp refl (negℚ-invol W) (negℚ-anti-≤ wlo)

    flip-sign : ((-ℚ z) *ℚ (-ℚ w)) ≡ (z *ℚ w)
    flip-sign = rational!

  abs-mul-lower
    : ∀ z w B W
    → ((-ℚ B) ≤ z) → (z ≤ B) → ((-ℚ W) ≤ w) → (w ≤ W) → 0 ≤ B
    → ((-ℚ (B *ℚ W)) ≤ (z *ℚ w))
  abs-mul-lower z w B W lo hi wlo whi nnB = ≤-resp refl unflip (negℚ-anti-≤ ub)
    where
    h1 : (-ℚ W) ≤ (-ℚ w)
    h1 = negℚ-anti-≤ whi

    h2 : (-ℚ w) ≤ W
    h2 = ≤-resp refl (negℚ-invol W) (negℚ-anti-≤ wlo)

    ub : (z *ℚ (-ℚ w)) ≤ (B *ℚ W)
    ub = abs-mul-bound z (-ℚ w) B W lo hi h1 h2 nnB

    unflip : (-ℚ (z *ℚ (-ℚ w))) ≡ (z *ℚ w)
    unflip = rational!

  diff-ub : ∀ {c d} v v' → v ≤ d → c ≤ v' → ((v +ℚ (-ℚ v')) ≤ (d +ℚ (-ℚ c)))
  diff-ub v v' h1 h2 = +ℚ-preserves-≤ h1 (negℚ-anti-≤ h2)

  diff-lb : ∀ {c d} v v' → c ≤ v → v' ≤ d → ((-ℚ (d +ℚ (-ℚ c))) ≤ (v +ℚ (-ℚ v')))
  diff-lb {c} {d} v v' h1 h2 = ≤-resp eq refl (+ℚ-preserves-≤ h1 (negℚ-anti-≤ h2))
    where
    eq : (c +ℚ (-ℚ d)) ≡ (-ℚ (d +ℚ (-ℚ c)))
    eq = rational!

  tele-bound
    : ∀ u v u' v' B₁ B₂ W₁ W₂
    → ((-ℚ B₂) ≤ u) → (u ≤ B₂)
    → ((-ℚ B₁) ≤ v') → (v' ≤ B₁)
    → 0 ≤ B₁ → 0 ≤ B₂
    → ((v +ℚ (-ℚ v')) ≤ W₂) → ((-ℚ W₂) ≤ (v +ℚ (-ℚ v')))
    → ((u +ℚ (-ℚ u')) ≤ W₁) → ((-ℚ W₁) ≤ (u +ℚ (-ℚ u')))
    → ((u *ℚ v) ≤ ((u' *ℚ v') +ℚ ((B₂ *ℚ W₂) +ℚ (B₁ *ℚ W₁))))
  tele-bound u v u' v' B₁ B₂ W₁ W₂ ulo uhi vlo vhi nn₁ nn₂ dv-ub dv-lb du-ub du-lb =
    ≤-resp (sym key) refl
      (+ℚ-preserves-≤ (≤-refl {u' *ℚ v'}) (+ℚ-preserves-≤ b1 b2))
    where
    key : (u *ℚ v) ≡ ((u' *ℚ v') +ℚ ((u *ℚ (v +ℚ (-ℚ v'))) +ℚ (v' *ℚ (u +ℚ (-ℚ u')))))
    key = rational!

    b1 : (u *ℚ (v +ℚ (-ℚ v'))) ≤ (B₂ *ℚ W₂)
    b1 = abs-mul-bound u (v +ℚ (-ℚ v')) B₂ W₂ ulo uhi dv-lb dv-ub nn₂

    b2 : (v' *ℚ (u +ℚ (-ℚ u'))) ≤ (B₁ *ℚ W₁)
    b2 = abs-mul-bound v' (u +ℚ (-ℚ u')) B₁ W₁ vlo vhi du-lb du-ub nn₁

  spread-bound
    : ∀ a b c d B₁ B₂
    → a ≤ b → c ≤ d
    → ((-ℚ B₂) ≤ a) → (b ≤ B₂) → 0 ≤ B₂
    → ((-ℚ B₁) ≤ c) → (d ≤ B₁) → 0 ≤ B₁
    → (max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
       ≤ (min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) +ℚ
          ((B₂ *ℚ (d +ℚ (-ℚ c))) +ℚ (B₁ *ℚ (b +ℚ (-ℚ a))))))
  spread-bound a b c d B₁ B₂ a≤b c≤d lo₂ hi₂ nn₂ lo₁ hi₁ nn₁ =
    go (min₄-choice (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
    where
    S : Ratio
    S = (B₂ *ℚ (d +ℚ (-ℚ c))) +ℚ (B₁ *ℚ (b +ℚ (-ℚ a)))

    bd
      : ∀ u' v' → a ≤ u' → u' ≤ b → c ≤ v' → v' ≤ d
      → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ ((u' *ℚ v') +ℚ S)
    bd u' v' h1 h2 h3 h4 = max₄-univ
      (tele-bound a c u' v' B₁ B₂ (b +ℚ (-ℚ a)) (d +ℚ (-ℚ c))
        lo₂ (≤-trans a≤b hi₂) (≤-trans lo₁ h3) (≤-trans h4 hi₁) nn₁ nn₂
        (diff-ub c v' c≤d h3) (diff-lb c v' ≤-refl h4)
        (diff-ub a u' a≤b h1) (diff-lb a u' ≤-refl h2))
      (tele-bound a d u' v' B₁ B₂ (b +ℚ (-ℚ a)) (d +ℚ (-ℚ c))
        lo₂ (≤-trans a≤b hi₂) (≤-trans lo₁ h3) (≤-trans h4 hi₁) nn₁ nn₂
        (diff-ub d v' ≤-refl h3) (diff-lb d v' c≤d h4)
        (diff-ub a u' a≤b h1) (diff-lb a u' ≤-refl h2))
      (tele-bound b c u' v' B₁ B₂ (b +ℚ (-ℚ a)) (d +ℚ (-ℚ c))
        (≤-trans lo₂ a≤b) hi₂ (≤-trans lo₁ h3) (≤-trans h4 hi₁) nn₁ nn₂
        (diff-ub c v' c≤d h3) (diff-lb c v' ≤-refl h4)
        (diff-ub b u' ≤-refl h1) (diff-lb b u' a≤b h2))
      (tele-bound b d u' v' B₁ B₂ (b +ℚ (-ℚ a)) (d +ℚ (-ℚ c))
        (≤-trans lo₂ a≤b) hi₂ (≤-trans lo₁ h3) (≤-trans h4 hi₁) nn₁ nn₂
        (diff-ub d v' ≤-refl h3) (diff-lb d v' c≤d h4)
        (diff-ub b u' ≤-refl h1) (diff-lb b u' a≤b h2))

    go
      : (min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≡ (a *ℚ c))
        ⊎ ((min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≡ (a *ℚ d))
        ⊎ ((min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≡ (b *ℚ c))
        ⊎ (min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≡ (b *ℚ d))))
      → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
        ≤ (min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) +ℚ S)
    go (inl e) = subst
      (λ w → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (w +ℚ S))
      (sym e) (bd a c ≤-refl a≤b ≤-refl c≤d)
    go (inr (inl e)) = subst
      (λ w → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (w +ℚ S))
      (sym e) (bd a d ≤-refl a≤b c≤d ≤-refl)
    go (inr (inr (inl e))) = subst
      (λ w → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (w +ℚ S))
      (sym e) (bd b c a≤b ≤-refl ≤-refl c≤d)
    go (inr (inr (inr e))) = subst
      (λ w → max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (w +ℚ S))
      (sym e) (bd b d a≤b ≤-refl c≤d ≤-refl)
```
-->

## The locatedness budget

The two key consequences of the spread bound, packaged for use in
the cut construction. First: a bracket whose endpoints are bounded
by $B_1, B_2$ and whose spread-budget is below half the target gap
$r - q$ must commit — either $q$ is below the four-fold minimum, or
the four-fold maximum is below $r$. Second: if both bracket widths
are below $\delta = \frac{(r-q)/2}{B_1 + B_2}$, the budget *is*
below half the gap. Finally, disjointness of the product cut
reduces to evaluating two brackets at a common rational point.

<!--
```agda
private abstract
  located-upper-bound
    : ∀ q r a b c d B₁ B₂
    → q < r → a ≤ b → c ≤ d
    → ((-ℚ B₂) ≤ a) → (b ≤ B₂) → 0 ≤ B₂
    → ((-ℚ B₁) ≤ c) → (d ≤ B₁) → 0 ≤ B₁
    → (((B₂ *ℚ (d +ℚ (-ℚ c))) +ℚ (B₁ *ℚ (b +ℚ (-ℚ a)))) ≤ half (r +ℚ (-ℚ q)))
    → (min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ q)
    → (max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) < r)
  located-upper-bound q r a b c d B₁ B₂ q<r a≤b c≤d lo₂ hi₂ nn₂ lo₁ hi₁ nn₁ S≤h m≤q =
    ≤-<-trans step1 step2
    where
    step1
      : max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
      ≤ (q +ℚ half (r +ℚ (-ℚ q)))
    step1 = ≤-trans
      (spread-bound a b c d B₁ B₂ a≤b c≤d lo₂ hi₂ nn₂ lo₁ hi₁ nn₁)
      (+ℚ-preserves-≤ m≤q S≤h)

    eq : (q +ℚ (r +ℚ (-ℚ q))) ≡ r
    eq = rational!

    step2 : (q +ℚ half (r +ℚ (-ℚ q))) < r
    step2 = <-resp refl eq (+ℚ-preserves-<l q (half-lt (<→positive-diff q<r)))

  width-budget
    : ∀ gap B₁ B₂ wx wy (BBp : Positive (B₁ +ℚ B₂))
    → 0 ≤ B₁ → 0 ≤ B₂
    → (wx ≤ ((half gap /ℚ (B₁ +ℚ B₂)) ⦃ inc (positive→nonzero BBp) ⦄))
    → (wy ≤ ((half gap /ℚ (B₁ +ℚ B₂)) ⦃ inc (positive→nonzero BBp) ⦄))
    → (((B₂ *ℚ wy) +ℚ (B₁ *ℚ wx)) ≤ half gap)
  width-budget gap B₁ B₂ wx wy BBp nn₁ nn₂ hwx hwy =
    ≤-resp refl collect
      (+ℚ-preserves-≤ (*ℚ-preserves-≤l B₂ nn₂ hwy) (*ℚ-preserves-≤l B₁ nn₁ hwx))
    where
    δ : Ratio
    δ = (half gap /ℚ (B₁ +ℚ B₂)) ⦃ inc (positive→nonzero BBp) ⦄

    collect : ((B₂ *ℚ δ) +ℚ (B₁ *ℚ δ)) ≡ half gap
    collect =
        sym (*ℚ-distribr δ B₂ B₁)
      ∙ ap (_*ℚ δ) (+ℚ-commutative B₂ B₁)
      ∙ *ℚ-commutative (B₁ +ℚ B₂) δ
      ∙ /ℚ-cancel (half gap) (B₁ +ℚ B₂) ⦃ inc (positive→nonzero BBp) ⦄

  located-decide
    : ∀ q r a b c d B₁ B₂
    → q < r → a ≤ b → c ≤ d
    → ((-ℚ B₂) ≤ a) → (b ≤ B₂) → 0 ≤ B₂
    → ((-ℚ B₁) ≤ c) → (d ≤ B₁) → 0 ≤ B₁
    → (((B₂ *ℚ (d +ℚ (-ℚ c))) +ℚ (B₁ *ℚ (b +ℚ (-ℚ a)))) ≤ half (r +ℚ (-ℚ q)))
    → ((q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
      ⊎ (max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) < r))
  located-decide q r a b c d B₁ B₂ q<r a≤b c≤d lo₂ hi₂ nn₂ lo₁ hi₁ nn₁ S≤h
    with holds? (q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
  ... | yes p = inl p
  ... | no ¬p = inr (located-upper-bound q r a b c d B₁ B₂
      q<r a≤b c≤d lo₂ hi₂ nn₂ lo₁ hi₁ nn₁ S≤h (¬<→≥ ¬p))

  bound-nn : ∀ u v → 0 ≤ maxℚ 1 (maxℚ v (-ℚ u))
  bound-nn u v = ≤-trans 0≤1' (maxℚ-≤l {1} {maxℚ v (-ℚ u)})

  bound-pos : ∀ u v → 0 < maxℚ 1 (maxℚ v (-ℚ u))
  bound-pos u v = <-≤-trans 0<1' (maxℚ-≤l {1} {maxℚ v (-ℚ u)})

  bound-hi : ∀ u v → v ≤ maxℚ 1 (maxℚ v (-ℚ u))
  bound-hi u v = ≤-trans (maxℚ-≤l {v} { -ℚ u}) (maxℚ-≤r {1} {maxℚ v (-ℚ u)})

  bound-lo : ∀ u v → ((-ℚ (maxℚ 1 (maxℚ v (-ℚ u)))) ≤ u)
  bound-lo u v = ≤-resp refl (negℚ-invol u)
    (negℚ-anti-≤ (≤-trans (maxℚ-≤r {v} { -ℚ u}) (maxℚ-≤r {1} {maxℚ v (-ℚ u)})))

  disjoint-key
    : ∀ q a b c d a' b' c' d'
    → a < b → a < b' → a' < b → a' < b'
    → c < d → c < d' → c' < d → c' < d'
    → (q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
    → (max₄ (a' *ℚ c') (a' *ℚ d') (b' *ℚ c') (b' *ℚ d') < q)
    → ⊥
  disjoint-key q a b c d a' b' c' d' ab ab' a'b a'b' cd cd' c'd c'd' q<m m'<q =
    <-irrefl refl (<-trans (<-≤-trans (<-≤-trans q<m lower-part) upper-part) m'<q)
    where
    u : Ratio
    u = maxℚ a a'

    v : Ratio
    v = maxℚ c c'

    lower-part : min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) ≤ (u *ℚ v)
    lower-part = bracket-lower u v a b c d
      (maxℚ-≤l {a} {a'}) (<-weaken (maxℚ-lub ab a'b))
      (maxℚ-≤l {c} {c'}) (<-weaken (maxℚ-lub cd c'd))

    upper-part : (u *ℚ v) ≤ max₄ (a' *ℚ c') (a' *ℚ d') (b' *ℚ c') (b' *ℚ d')
    upper-part = bracket-upper u v a' b' c' d'
      (maxℚ-≤r {a} {a'}) (<-weaken (maxℚ-lub ab' a'b'))
      (maxℚ-≤r {c} {c'}) (<-weaken (maxℚ-lub cd' c'd'))
```
-->

With the rational groundwork laid, the construction of the product
cut itself follows. A rational $q$ is *below* $x \cdot y$ when it is
below all four products of some bracket around the factors, and
*above* when it is above all four; both are propositions once
resized into $\Omega$.

```agda
module _ (x y : ℝ) where
  private
    Lo Up : Ratio → Type
    Lo q = Σ[ a ∈ Ratio ] Σ[ b ∈ Ratio ] Σ[ c ∈ Ratio ] Σ[ d ∈ Ratio ]
      ∣ x .lower a ∣ × ∣ x .upper b ∣ × ∣ y .lower c ∣ × ∣ y .upper d ∣ ×
      (q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d))
    Up q = Σ[ a ∈ Ratio ] Σ[ b ∈ Ratio ] Σ[ c ∈ Ratio ] Σ[ d ∈ Ratio ]
      ∣ x .lower a ∣ × ∣ x .upper b ∣ × ∣ y .lower c ∣ × ∣ y .upper d ∣ ×
      (max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) < q)
```

The two easy halves — inhabitation, roundedness and closure — follow
the same pattern as [[addition|real-addition]]: shift the four-fold
extremum by a unit for a witness, take midpoints for roundedness, and
transport across `<-trans`{.Agda} for closure.

<!--
```agda
    lo-inhab : ∥ Σ Ratio (λ q → □ (Lo q)) ∥
    lo-inhab = do
      (a , la) ← cut.lower-inhab x
      (b , ub) ← cut.upper-inhab x
      (c , lc) ← cut.lower-inhab y
      (d , ud) ← cut.upper-inhab y
      pure ( min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) +ℚ (-ℚ 1)
           , inc (a , b , c , d , la , ub , lc , ud , sub-pos-< _ 1 0<1'))

    up-inhab : ∥ Σ Ratio (λ q → □ (Up q)) ∥
    up-inhab = do
      (a , la) ← cut.lower-inhab x
      (b , ub) ← cut.upper-inhab x
      (c , lc) ← cut.lower-inhab y
      (d , ud) ← cut.upper-inhab y
      pure ( max₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d) +ℚ 1
           , inc (a , b , c , d , la , ub , lc , ud , add-pos-< _ 1 0<1'))

    lo-round : ∀ q → □ (Lo q) → ∥ Σ Ratio (λ r → (q < r) × □ (Lo r)) ∥
    lo-round q = □-rec squash λ (a , b , c , d , la , ub , lc , ud , q<m) →
      inc ( midpoint q _ , mid-<l q<m
          , inc (a , b , c , d , la , ub , lc , ud , mid-<r q<m))

    up-round : ∀ r → □ (Up r) → ∥ Σ Ratio (λ q → (q < r) × □ (Up q)) ∥
    up-round r = □-rec squash λ (a , b , c , d , la , ub , lc , ud , M<r) →
      inc ( midpoint _ r , mid-<r M<r
          , inc (a , b , c , d , la , ub , lc , ud , mid-<l M<r))

    lo-close : ∀ {q r} → q < r → □ (Lo r) → □ (Lo q)
    lo-close q<r = □-map λ (a , b , c , d , la , ub , lc , ud , r<m) →
      (a , b , c , d , la , ub , lc , ud , <-trans q<r r<m)

    up-close : ∀ {q r} → q < r → □ (Up q) → □ (Up r)
    up-close q<r = □-map λ (a , b , c , d , la , ub , lc , ud , M<q) →
      (a , b , c , d , la , ub , lc , ud , <-trans M<q q<r)
```
-->

Disjointness is a single call to the bracketing lemma evaluated at
the common rational point $(\max(a, a'), \max(c, c'))$: the strict
order between the factors' lower and upper witnesses, supplied by
`lower<upper`{.Agda}, feeds `disjoint-key`{.Agda}.

<!--
```agda
    disj : ∀ q → □ (Lo q) → □ (Up q) → ⊥
    disj q = □-rec (hlevel 1) λ (a , b , c , d , la , ub , lc , ud , q<m) →
             □-rec (hlevel 1) λ (a' , b' , c' , d' , la' , ub' , lc' , ud' , M'<q) →
      disjoint-key q a b c d a' b' c' d'
        (lower<upper x la ub) (lower<upper x la ub') (lower<upper x la' ub) (lower<upper x la' ub')
        (lower<upper y lc ud) (lower<upper y lc ud') (lower<upper y lc' ud) (lower<upper y lc' ud')
        q<m M'<q
```
-->

Locatedness is the analytic heart. We bracket each factor first to
within a unit — fixing bounds $B_1, B_2$ on the magnitudes of the
endpoints — and then to within $\delta = \frac{(r-q)/2}{B_1 + B_2}$,
intersecting the two brackets so the tighter one inherits the bounds.
The spread of the four products is then below half the gap $r - q$,
so `located-decide`{.Agda} must commit to one side.

<!--
```agda
    located : ∀ {q r} → q < r → ∥ □ (Lo q) ⊎ □ (Up r) ∥
    located {q} {r} q<r = do
      (a₀ , b₀ , la₀ , ub₀ , _) ← approx x 1 0<1'
      (c₀ , d₀ , lc₀ , ud₀ , _) ← approx y 1 0<1'
      let B₂ = maxℚ 1 (maxℚ b₀ (-ℚ a₀))
          B₁ = maxℚ 1 (maxℚ d₀ (-ℚ c₀))
          gap = r +ℚ (-ℚ q)
          0≤B₂ = bound-nn a₀ b₀
          0≤B₁ = bound-nn c₀ d₀
          B₁≤B₁+B₂ : B₁ ≤ (B₁ +ℚ B₂)
          B₁≤B₁+B₂ = ≤-resp (+ℚ-idr B₁) refl (+ℚ-preserves-≤ (≤-refl {B₁}) 0≤B₂)
          BBpos : 0 < (B₁ +ℚ B₂)
          BBpos = <-≤-trans (bound-pos c₀ d₀) B₁≤B₁+B₂
          BBp : Positive (B₁ +ℚ B₂)
          BBp = to-positive BBpos
      let δ = (half gap /ℚ (B₁ +ℚ B₂)) ⦃ inc (positive→nonzero BBp) ⦄
          δ-pos = div-pos (half gap) (B₁ +ℚ B₂) ⦃ inc (positive→nonzero BBp) ⦄
                    (half-pos (<→positive-diff q<r)) BBpos
      (a₁ , b₁ , la₁ , ub₁ , wx₁) ← approx x δ δ-pos
      (c₁ , d₁ , lc₁ , ud₁ , wy₁) ← approx y δ δ-pos
      let a = maxℚ a₀ a₁ ; b = minℚ b₀ b₁ ; c = maxℚ c₀ c₁ ; d = minℚ d₀ d₁
          la = maxℚ-lower-mem x la₀ la₁
          ub = minℚ-upper-mem x ub₀ ub₁
          lc = maxℚ-lower-mem y lc₀ lc₁
          ud = minℚ-upper-mem y ud₀ ud₁
          a≤b = <-weaken (lower<upper x la ub)
          c≤d = <-weaken (lower<upper y lc ud)
          -B₂≤a = ≤-trans (bound-lo a₀ b₀) (maxℚ-≤l {a₀} {a₁})
          b≤B₂  = ≤-trans (minℚ-≤l {b₀} {b₁}) (bound-hi a₀ b₀)
          -B₁≤c = ≤-trans (bound-lo c₀ d₀) (maxℚ-≤l {c₀} {c₁})
          d≤B₁  = ≤-trans (minℚ-≤l {d₀} {d₁}) (bound-hi c₀ d₀)
          wx≤δ : (b +ℚ (-ℚ a)) ≤ δ
          wx≤δ = ≤-trans (+ℚ-preserves-≤ (minℚ-≤r {b₀} {b₁}) (negℚ-anti-≤ (maxℚ-≤r {a₀} {a₁}))) (<-weaken wx₁)
          wy≤δ : (d +ℚ (-ℚ c)) ≤ δ
          wy≤δ = ≤-trans (+ℚ-preserves-≤ (minℚ-≤r {d₀} {d₁}) (negℚ-anti-≤ (maxℚ-≤r {c₀} {c₁}))) (<-weaken wy₁)
          S≤half = width-budget gap B₁ B₂ (b +ℚ (-ℚ a)) (d +ℚ (-ℚ c)) BBp 0≤B₁ 0≤B₂ wx≤δ wy≤δ
      pure ([ (λ q<m → inl (inc (a , b , c , d , la , ub , lc , ud , q<m)))
            , (λ M<r → inr (inc (a , b , c , d , la , ub , lc , ud , M<r))) ]
            (located-decide q r a b c d B₁ B₂ q<r a≤b c≤d -B₂≤a b≤B₂ 0≤B₂ -B₁≤c d≤B₁ 0≤B₁ S≤half))
```
-->

Assembling the eight fields gives the product.

```agda
  prod : ℝ
  prod .lower q = elΩ (Lo q)
  prod .upper q = elΩ (Up q)
  prod .has-is-cut = record
    { lower-inhab  = lo-inhab
    ; upper-inhab  = up-inhab
    ; lower-round  = lo-round
    ; lower-close  = lo-close
    ; upper-round  = up-round
    ; upper-close  = up-close
    ; cut-disjoint = disj
    ; cut-located  = located
    }

_*ᴿ_ : ℝ → ℝ → ℝ
x *ᴿ y = prod x y

infixl 8 _*ᴿ_
```
