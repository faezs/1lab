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

## Commutativity

Because the four corner products of a bracket are symmetric under
swapping the two factors — $\{ac, ad, bc, bd\}$ is $\{ca, cb, da,
db\}$ — the product is commutative. The four-fold minimum is a
greatest lower bound, so it is unchanged by the reindexing, and the
lower cut of $x \cdot y$ is contained in that of $y \cdot x$; the
[[antisymmetry|dedekind-real]] of the real order finishes the job
without ever mentioning the upper cuts.

<!--
```agda
private abstract
  min₄-comm-le
    : ∀ a b c d
    → min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
      ≤ min₄ (c *ℚ a) (c *ℚ b) (d *ℚ a) (d *ℚ b)
  min₄-comm-le a b c d = min₄-univ
    (≤-resp refl (*ℚ-commutative a c) (min₄-≤₁ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
    (≤-resp refl (*ℚ-commutative b c) (min₄-≤₃ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
    (≤-resp refl (*ℚ-commutative a d) (min₄-≤₂ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
    (≤-resp refl (*ℚ-commutative b d) (min₄-≤₄ {a *ℚ c} {a *ℚ d} {b *ℚ c} {b *ℚ d}))
```
-->

```agda
*ᴿ-comm : ∀ x y → x *ᴿ y ≡ y *ᴿ x
*ᴿ-comm x y = ≤ᴿ-antisym (to x y) (to y x)
  where
  to : ∀ x y → (x *ᴿ y) ≤ᴿ (y *ᴿ x)
  to x y q = □-map λ (a , b , c , d , la , ub , lc , ud , q<m) →
    (c , d , a , b , lc , ud , la , ub , <-≤-trans q<m (min₄-comm-le a b c d))
```

## The multiplicative unit

The real number $1$ is the rational $1$ as a cut. One direction of
the unit law is immediate — a bracket $c < 1 < d$ pins the four
products between $ac$ and $bd$, and the four-fold minimum is below
$a \cdot 1 = a$. The other direction is a budget argument, of the
same shape as locatedness: given a lower bound $a > q$ for $x$,
bracket $1$ so tightly (within $\delta = \tfrac{(a-q)/2}{B}$, where
$B$ bounds the magnitudes of the endpoints) that every corner
product stays above $q$.

```agda
1ᴿ : ℝ
1ᴿ = ratℝ 1
```

<!--
```agda
private abstract
  one-minus-sub : ∀ δ → (1 +ℚ (-ℚ (1 +ℚ (-ℚ δ)))) ≡ δ
  one-minus-sub δ = rational!
  one-minus-add : ∀ δ → (1 +ℚ (-ℚ (1 +ℚ δ))) ≡ (-ℚ δ)
  one-minus-add δ = rational!
  sub-diff : ∀ a q → (a +ℚ (-ℚ (a +ℚ (-ℚ q)))) ≡ q
  sub-diff a q = rational!

private
  idr-witness
    : ∀ x q a b → q < a → ∣ x .lower a ∣ → ∣ x .upper b ∣
    → ∣ (x *ᴿ 1ᴿ) .lower q ∣
  idr-witness x q a b q<a la ub =
    inc (a , b , c , d , la , ub , c<1 , 1<d , q<min)
    where
    gap : Ratio
    gap = a +ℚ (-ℚ q)
    gap-pos : 0 < gap
    gap-pos = <→positive-diff q<a
    B : Ratio
    B = maxℚ 1 (maxℚ b (-ℚ a))
    0<B : 0 < B
    0<B = bound-pos a b
    B-nz : Nonzero B
    B-nz = inc (positive→nonzero (to-positive 0<B))
    δ : Ratio
    δ = (half gap /ℚ B) ⦃ B-nz ⦄
    δ-pos : 0 < δ
    δ-pos = div-pos (half gap) B ⦃ B-nz ⦄ (half-pos gap-pos) 0<B
    c d : Ratio
    c = 1 +ℚ (-ℚ δ)
    d = 1 +ℚ δ
    c<1 : c < 1
    c<1 = sub-pos-< 1 δ δ-pos
    1<d : 1 < d
    1<d = add-pos-< 1 δ δ-pos
    Bδ≡ : B *ℚ δ ≡ half gap
    Bδ≡ = *ℚ-commutative B δ ∙ /ℚ-cancel (half gap) B ⦃ B-nz ⦄
    a≤b : a ≤ b
    a≤b = <-weaken (lower<upper x la ub)
    a≤B : a ≤ B
    a≤B = ≤-trans a≤b (bound-hi a b)
    -B≤a : (-ℚ B) ≤ a
    -B≤a = bound-lo a b
    b≤B : b ≤ B
    b≤B = bound-hi a b
    -B≤b : (-ℚ B) ≤ b
    -B≤b = ≤-trans (bound-lo a b) a≤b
    q<a-hg : q < (a +ℚ (-ℚ half gap))
    q<a-hg = <-resp aeq refl (+ℚ-preserves-<l a (negℚ-anti-< (half-lt gap-pos)))
      where
      aeq : a +ℚ (-ℚ gap) ≡ q
      aeq = sub-diff a q
    corner
      : ∀ p → (-ℚ B) ≤ p → p ≤ B → a ≤ p
      → ∀ e → (-ℚ δ) ≤ (1 +ℚ (-ℚ e)) → (1 +ℚ (-ℚ e)) ≤ δ
      → q < (p *ℚ e)
    corner p -B≤p p≤B a≤p e lo hi = <-≤-trans q<a-hg (≤-trans a-hg≤p-hg p-hg≤pe)
      where
      p1e≤hg : (p *ℚ (1 +ℚ (-ℚ e))) ≤ half gap
      p1e≤hg = ≤-resp refl Bδ≡ (abs-mul-bound p (1 +ℚ (-ℚ e)) B δ -B≤p p≤B lo hi (<-weaken 0<B))
      pe-eq : (p +ℚ (-ℚ (p *ℚ (1 +ℚ (-ℚ e))))) ≡ (p *ℚ e)
      pe-eq = rational!
      a-hg≤p-hg : (a +ℚ (-ℚ half gap)) ≤ (p +ℚ (-ℚ half gap))
      a-hg≤p-hg = +ℚ-preserves-≤ a≤p ≤-refl
      p-hg≤pe : (p +ℚ (-ℚ half gap)) ≤ (p *ℚ e)
      p-hg≤pe = ≤-resp refl pe-eq (+ℚ-preserves-≤ (≤-refl {p}) (negℚ-anti-≤ p1e≤hg))
    1mc : (1 +ℚ (-ℚ c)) ≡ δ
    1mc = one-minus-sub δ
    1md : (1 +ℚ (-ℚ d)) ≡ (-ℚ δ)
    1md = one-minus-add δ
    -δ≤δ : (-ℚ δ) ≤ δ
    -δ≤δ = ≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ (<-weaken δ-pos))) (<-weaken δ-pos)
    lo-c : (-ℚ δ) ≤ (1 +ℚ (-ℚ c))
    lo-c = ≤-resp refl (sym 1mc) -δ≤δ
    hi-c : (1 +ℚ (-ℚ c)) ≤ δ
    hi-c = ≤-resp (sym 1mc) refl ≤-refl
    lo-d : (-ℚ δ) ≤ (1 +ℚ (-ℚ d))
    lo-d = ≤-resp refl (sym 1md) ≤-refl
    hi-d : (1 +ℚ (-ℚ d)) ≤ δ
    hi-d = ≤-resp (sym 1md) refl -δ≤δ
    q<min : q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    q<min = min₄-univ-<
      (corner a -B≤a a≤B ≤-refl c lo-c hi-c)
      (corner a -B≤a a≤B ≤-refl d lo-d hi-d)
      (corner b -B≤b b≤B a≤b c lo-c hi-c)
      (corner b -B≤b b≤B a≤b d lo-d hi-d)
```
-->

```agda
*ᴿ-idr : ∀ x → x *ᴿ 1ᴿ ≡ x
*ᴿ-idr x = ≤ᴿ-antisym fwd bwd
  where
  fwd : (x *ᴿ 1ᴿ) ≤ᴿ x
  fwd q = □-rec ((x .lower q) .is-tr)
    λ (a , b , c , d , la , ub , c<1 , 1<d , q<m) →
      cut.lower-close x
        (<-≤-trans q<m (≤-resp refl (*ℚ-idr a)
          (≤-trans (minℚ-≤l {minℚ (a *ℚ c) (a *ℚ d)} {minℚ (b *ℚ c) (b *ℚ d)})
                   (bracket₁-lower a 1 c d (<-weaken c<1) (<-weaken 1<d)))))
        la

  bwd : x ≤ᴿ (x *ᴿ 1ᴿ)
  bwd q lq = ∥-∥-rec ((x *ᴿ 1ᴿ) .lower q .is-tr)
    (λ (a , q<a , la) → ∥-∥-rec ((x *ᴿ 1ᴿ) .lower q .is-tr)
      (λ (b , ub) → idr-witness x q a b q<a la ub)
      (cut.upper-inhab x))
    (cut.lower-round x q lq)

*ᴿ-idl : ∀ x → 1ᴿ *ᴿ x ≡ x
*ᴿ-idl x = *ᴿ-comm 1ᴿ x ∙ *ᴿ-idr x
```

## Zero absorption

Multiplying by $0$ annihilates: $x \cdot 0 = 0$. One direction is
immediate from the bracketing lemma — a bracket $c < 0 < d$ around
the zero factor pins the four products between $a \cdot 0 = 0$ and
$b \cdot 0 = 0$, so the four-fold minimum is at most $0$ and any $q$
below it is below $0$. The other direction is the same budget
argument as the unit law, with baseline $0$ instead of $1$: given
$q < 0$, bracket $0$ so tightly (within
$\delta = \tfrac{(-q)/2}{B}$, $B$ bounding the magnitudes of an
$x$-bracket) that every corner product $p \cdot e$, with
$|p| \le B$ and $|e| \le \delta$, satisfies
$p \cdot e \ge -B\delta = -\tfrac{-q}{2} > q$.

<!--
```agda
private abstract
  zero-sub-diff : ∀ q → (0 +ℚ (-ℚ (0 +ℚ (-ℚ q)))) ≡ q
  zero-sub-diff q = rational!

private
  zeroʳ-witness
    : ∀ x q a b → q < 0 → ∣ x .lower a ∣ → ∣ x .upper b ∣
    → ∣ (x *ᴿ 0ᴿ) .lower q ∣
  zeroʳ-witness x q a b q<0 la ub =
    inc (a , b , c , d , la , ub , c<0 , 0<d , q<min)
    where
    gap : Ratio
    gap = 0 +ℚ (-ℚ q)
    gap-pos : 0 < gap
    gap-pos = <→positive-diff q<0
    B : Ratio
    B = maxℚ 1 (maxℚ b (-ℚ a))
    0<B : 0 < B
    0<B = bound-pos a b
    B-nz : Nonzero B
    B-nz = inc (positive→nonzero (to-positive 0<B))
    δ : Ratio
    δ = (half gap /ℚ B) ⦃ B-nz ⦄
    δ-pos : 0 < δ
    δ-pos = div-pos (half gap) B ⦃ B-nz ⦄ (half-pos gap-pos) 0<B
    c d : Ratio
    c = 0 +ℚ (-ℚ δ)
    d = 0 +ℚ δ
    c<0 : c < 0
    c<0 = sub-pos-< 0 δ δ-pos
    0<d : 0 < d
    0<d = add-pos-< 0 δ δ-pos
    Bδ≡ : B *ℚ δ ≡ half gap
    Bδ≡ = *ℚ-commutative B δ ∙ /ℚ-cancel (half gap) B ⦃ B-nz ⦄
    a≤b : a ≤ b
    a≤b = <-weaken (lower<upper x la ub)
    b≤B : b ≤ B
    b≤B = bound-hi a b
    -B≤a : (-ℚ B) ≤ a
    -B≤a = bound-lo a b
    -B≤b : (-ℚ B) ≤ b
    -B≤b = ≤-trans (bound-lo a b) a≤b
    a≤B : a ≤ B
    a≤B = ≤-trans a≤b b≤B
    q<-hg : q < (0 +ℚ (-ℚ half gap))
    q<-hg = <-resp zeq refl (+ℚ-preserves-<l 0 (negℚ-anti-< (half-lt gap-pos)))
      where
      zeq : 0 +ℚ (-ℚ gap) ≡ q
      zeq = zero-sub-diff q
    -δ≤c : (-ℚ δ) ≤ c
    -δ≤c = ≤-resp refl (sym (+ℚ-idl (-ℚ δ))) ≤-refl
    c≤δ : c ≤ δ
    c≤δ = ≤-resp (sym (+ℚ-idl (-ℚ δ))) refl (≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ (<-weaken δ-pos))) (<-weaken δ-pos))
    -δ≤d : (-ℚ δ) ≤ d
    -δ≤d = ≤-resp refl (sym (+ℚ-idl δ)) (≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ (<-weaken δ-pos))) (<-weaken δ-pos))
    d≤δ : d ≤ δ
    d≤δ = ≤-resp (sym (+ℚ-idl δ)) refl ≤-refl
    corner
      : ∀ p → (-ℚ B) ≤ p → p ≤ B
      → ∀ e → (-ℚ δ) ≤ e → e ≤ δ
      → q < (p *ℚ e)
    corner p -B≤p p≤B e -δ≤e e≤δ = <-≤-trans q<-hg -hg≤pe
      where
      -Bδ≤pe : (-ℚ (B *ℚ δ)) ≤ (p *ℚ e)
      -Bδ≤pe = abs-mul-lower p e B δ -B≤p p≤B -δ≤e e≤δ (<-weaken 0<B)
      -hg≤pe : (0 +ℚ (-ℚ half gap)) ≤ (p *ℚ e)
      -hg≤pe = ≤-resp (ap (-ℚ_) Bδ≡ ∙ sym (+ℚ-idl (-ℚ half gap))) refl -Bδ≤pe
    q<min : q < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    q<min = min₄-univ-<
      (corner a -B≤a a≤B c -δ≤c c≤δ)
      (corner a -B≤a a≤B d -δ≤d d≤δ)
      (corner b -B≤b b≤B c -δ≤c c≤δ)
      (corner b -B≤b b≤B d -δ≤d d≤δ)
```
-->

```agda
*ᴿ-zeroʳ : ∀ x → x *ᴿ 0ᴿ ≡ 0ᴿ
*ᴿ-zeroʳ x = ≤ᴿ-antisym fwd bwd
  where
  fwd : (x *ᴿ 0ᴿ) ≤ᴿ 0ᴿ
  fwd q = □-rec ((0ᴿ .lower q) .is-tr)
    λ (a , b , c , d , la , ub , c<0 , 0<d , q<m) →
      <-≤-trans q<m
        (≤-resp refl (*ℚ-zeror a)
          (≤-trans (minℚ-≤l {minℚ (a *ℚ c) (a *ℚ d)} {minℚ (b *ℚ c) (b *ℚ d)})
                   (bracket₁-lower a 0 c d (<-weaken c<0) (<-weaken 0<d))))

  bwd : 0ᴿ ≤ᴿ (x *ᴿ 0ᴿ)
  bwd q q<0 = ∥-∥-rec ((x *ᴿ 0ᴿ) .lower q .is-tr)
    (λ (a , la) → ∥-∥-rec ((x *ᴿ 0ᴿ) .lower q .is-tr)
      (λ (b , ub) → zeroʳ-witness x q a b q<0 la ub)
      (cut.upper-inhab x))
    (cut.lower-inhab x)

*ᴿ-zeroˡ : ∀ x → 0ᴿ *ᴿ x ≡ 0ᴿ
*ᴿ-zeroˡ x = *ᴿ-comm 0ᴿ x ∙ *ᴿ-zeroʳ x
```

## Distributivity over addition

Multiplication distributes over addition: $x \cdot (y + z) = x \cdot
y + x \cdot z$. The interval product is only *sub*distributive over
the Minkowski sum of brackets — for a fixed $x$-bracket $[A, B]$,

$$
[A,B]\cdot([c,d]+[c',d']) \;\supseteq\; [A,B]\cdot[c,d] + [A,B]\cdot[c',d'],
$$

because the four-fold minimum is only *super*additive,
$\min_4(\cdots) + \min_4(\cdots) \le \min_4(\cdots + \cdots)$ (the
two summands may attain their minima at different corners). This
inclusion is exactly the "$\supseteq$" containment of intervals,
which on lower cuts reads as the inequality
$(x \cdot y) + (x \cdot z) \le x \cdot (y + z)$ — one of the two
directions of the distributive law, and the one that goes through
without any $\varepsilon$-budget. The two rational facts it rests on
are the superadditivity of the four-fold minimum and the fact that a
tighter bracket has a larger four-fold minimum; both are immediate
from the greatest-lower-bound property.

<!--
```agda
private abstract
  min₄-superadd
    : ∀ A B c d c' d'
    → ((min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d)) +ℚ
       (min₄ (A *ℚ c') (A *ℚ d') (B *ℚ c') (B *ℚ d')))
      ≤ min₄ (A *ℚ (c +ℚ c')) (A *ℚ (d +ℚ d')) (B *ℚ (c +ℚ c')) (B *ℚ (d +ℚ d'))
  min₄-superadd A B c d c' d' = min₄-univ
    (≤-resp refl (sym (*ℚ-distribl A c c'))
      (+ℚ-preserves-≤ (min₄-≤₁ {A *ℚ c} {A *ℚ d} {B *ℚ c} {B *ℚ d})
                      (min₄-≤₁ {A *ℚ c'} {A *ℚ d'} {B *ℚ c'} {B *ℚ d'})))
    (≤-resp refl (sym (*ℚ-distribl A d d'))
      (+ℚ-preserves-≤ (min₄-≤₂ {A *ℚ c} {A *ℚ d} {B *ℚ c} {B *ℚ d})
                      (min₄-≤₂ {A *ℚ c'} {A *ℚ d'} {B *ℚ c'} {B *ℚ d'})))
    (≤-resp refl (sym (*ℚ-distribl B c c'))
      (+ℚ-preserves-≤ (min₄-≤₃ {A *ℚ c} {A *ℚ d} {B *ℚ c} {B *ℚ d})
                      (min₄-≤₃ {A *ℚ c'} {A *ℚ d'} {B *ℚ c'} {B *ℚ d'})))
    (≤-resp refl (sym (*ℚ-distribl B d d'))
      (+ℚ-preserves-≤ (min₄-≤₄ {A *ℚ c} {A *ℚ d} {B *ℚ c} {B *ℚ d})
                      (min₄-≤₄ {A *ℚ c'} {A *ℚ d'} {B *ℚ c'} {B *ℚ d'})))

  min₄-tighten
    : ∀ A B a b c d → a ≤ A → A ≤ B → B ≤ b → c ≤ d
    → min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
      ≤ min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d)
  min₄-tighten A B a b c d a≤A A≤B B≤b c≤d = min₄-univ
    (bracket-lower A c a b c d a≤A A≤b ≤-refl c≤d)
    (bracket-lower A d a b c d a≤A A≤b c≤d ≤-refl)
    (bracket-lower B c a b c d a≤B B≤b ≤-refl c≤d)
    (bracket-lower B d a b c d a≤B B≤b c≤d ≤-refl)
    where
    A≤b : A ≤ b
    A≤b = ≤-trans A≤B B≤b
    a≤B : a ≤ B
    a≤B = ≤-trans a≤A A≤B

  min₄-tighten₂
    : ∀ A B C D c d → C ≤ c → c ≤ d → d ≤ D
    → min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D)
      ≤ min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d)
  min₄-tighten₂ A B C D c d C≤c c≤d d≤D = min₄-univ
    (≤-trans mtl (bracket₁-lower A c C D C≤c c≤D))
    (≤-trans mtl (bracket₁-lower A d C D C≤d d≤D))
    (≤-trans mtr (bracket₁-lower B c C D C≤c c≤D))
    (≤-trans mtr (bracket₁-lower B d C D C≤d d≤D))
    where
    C≤d : C ≤ d
    C≤d = ≤-trans C≤c c≤d
    c≤D : c ≤ D
    c≤D = ≤-trans c≤d d≤D
    mtl : min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D) ≤ minℚ (A *ℚ C) (A *ℚ D)
    mtl = minℚ-≤l {minℚ (A *ℚ C) (A *ℚ D)} {minℚ (B *ℚ C) (B *ℚ D)}
    mtr : min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D) ≤ minℚ (B *ℚ C) (B *ℚ D)
    mtr = minℚ-≤r {minℚ (A *ℚ C) (A *ℚ D)} {minℚ (B *ℚ C) (B *ℚ D)}

  sub-move : ∀ {a b} s → a ≤ (b +ℚ s) → (a +ℚ (-ℚ s)) ≤ b
  sub-move {a} {b} s a≤bs = ≤-resp refl b+s-s≡b (+ℚ-preserves-≤ a≤bs (≤-refl { -ℚ s}))
    where
    b+s-s≡b : (b +ℚ s) +ℚ (-ℚ s) ≡ b
    b+s-s≡b = rational!

  lt-move : ∀ {a b} s → s < (b +ℚ (-ℚ a)) → a < (b +ℚ (-ℚ s))
  lt-move {a} {b} s s<b-a = <-resp a+s-s≡a refl (+ℚ-preserves-<r (-ℚ s) a+s<b)
    where
    a+[b-a]≡b : a +ℚ (b +ℚ (-ℚ a)) ≡ b
    a+[b-a]≡b = rational!
    a+s<b : (a +ℚ s) < b
    a+s<b = <-resp refl a+[b-a]≡b (+ℚ-preserves-<l a s<b-a)
    a+s-s≡a : (a +ℚ s) +ℚ (-ℚ s) ≡ a
    a+s-s≡a = rational!

  ps-ring : ∀ a b h → ((a +ℚ (-ℚ h)) +ℚ (b +ℚ (-ℚ h))) ≡ ((a +ℚ b) +ℚ (-ℚ (h +ℚ h)))
  ps-ring a b h = rational!

  sum4-ring : ∀ a p b r → ((a +ℚ p) +ℚ (b +ℚ r)) ≡ ((a +ℚ b) +ℚ (p +ℚ r))
  sum4-ring a p b r = rational!

  sum-pos : ∀ {a b} → 0 < a → 0 ≤ b → 0 < (a +ℚ b)
  sum-pos {a} {b} 0<a 0≤b = <-≤-trans 0<a
    (≤-resp (+ℚ-idr a) refl (+ℚ-preserves-≤ (≤-refl {a}) 0≤b))
```
-->

The lower-cut containment now follows by unpacking the two product
witnesses, intersecting their $x$-brackets into a common
$[A, B] = [\max(a, a'), \min(b, b')]$ (a lower and an upper witness
for $x$ by the same max-of-lowers, min-of-uppers argument as
locatedness), summing the two $(y + z)$-brackets, and chaining the
two rational lemmas above with the strict slacks of the summands.

```agda
private abstract
  <-sum : ∀ {p q r s} → p < q → r < s → (p +ℚ r) < (q +ℚ s)
  <-sum {p} {q} {r} {s} p<q r<s =
    <-trans (+ℚ-preserves-<r r p<q) (+ℚ-preserves-<l q r<s)

*ᴿ-distribˡ-≤
  : ∀ x y z → ((x *ᴿ y) +ᴿ (x *ᴿ z)) ≤ᴿ (x *ᴿ (y +ᴿ z))
*ᴿ-distribˡ-≤ x y z q = □-rec ((x *ᴿ (y +ᴿ z)) .lower q .is-tr)
  λ (P , S , lxyP , lxzS , q<PS) →
    □-rec ((x *ᴿ (y +ᴿ z)) .lower q .is-tr)
      (λ (a , b , c , d , la , ub , lc , ud , P<m) →
        □-rec ((x *ᴿ (y +ᴿ z)) .lower q .is-tr)
          (λ (a' , b' , c' , d' , la' , ub' , lc' , ud' , S<m') →
            assemble a b c d la ub lc ud P<m a' b' c' d' la' ub' lc' ud' S<m' q<PS)
          lxzS)
      lxyP
  where
  assemble
    : ∀ a b c d
    → ∣ x .lower a ∣ → ∣ x .upper b ∣ → ∣ y .lower c ∣ → ∣ y .upper d ∣
    → ∀ {P} → P < min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
    → ∀ a' b' c' d'
    → ∣ x .lower a' ∣ → ∣ x .upper b' ∣ → ∣ z .lower c' ∣ → ∣ z .upper d' ∣
    → ∀ {S} → S < min₄ (a' *ℚ c') (a' *ℚ d') (b' *ℚ c') (b' *ℚ d')
    → {q : Ratio} → q < P +ℚ S
    → ∣ (x *ᴿ (y +ᴿ z)) .lower q ∣
  assemble a b c d la ub lc ud {P} P<m a' b' c' d' la' ub' lc' ud' {S} S<m' {q} q<PS =
    inc (A , B , (c +ℚ c') , (d +ℚ d') , lA , uB , lyz , uyz , q<final)
    where
    A B : Ratio
    A = maxℚ a a'
    B = minℚ b b'
    lA : ∣ x .lower A ∣
    lA = maxℚ-lower-mem x la la'
    uB : ∣ x .upper B ∣
    uB = minℚ-upper-mem x ub ub'
    lyz : ∣ (y +ᴿ z) .lower (c +ℚ c') ∣
    lyz = □-rec ((y +ᴿ z) .lower (c +ℚ c') .is-tr)
      (λ (γ , c<γ , lγ) → □-rec ((y +ᴿ z) .lower (c +ℚ c') .is-tr)
        (λ (γ' , c'<γ' , lγ') →
          inc (γ , γ' , lγ , lγ' , <-sum c<γ c'<γ'))
        (tr-□ (cut.lower-round z c' lc')))
      (tr-□ (cut.lower-round y c lc))
    uyz : ∣ (y +ᴿ z) .upper (d +ℚ d') ∣
    uyz = □-rec ((y +ᴿ z) .upper (d +ℚ d') .is-tr)
      (λ (δ , δ<d , uδ) → □-rec ((y +ᴿ z) .upper (d +ℚ d') .is-tr)
        (λ (δ' , δ'<d' , uδ') →
          inc (δ , δ' , uδ , uδ' , <-sum δ<d δ'<d'))
        (tr-□ (cut.upper-round z d' ud')))
      (tr-□ (cut.upper-round y d ud))
    a≤A : a ≤ A
    a≤A = maxℚ-≤l {a} {a'}
    a'≤A : a' ≤ A
    a'≤A = maxℚ-≤r {a} {a'}
    B≤b : B ≤ b
    B≤b = minℚ-≤l {b} {b'}
    B≤b' : B ≤ b'
    B≤b' = minℚ-≤r {b} {b'}
    A≤B : A ≤ B
    A≤B = <-weaken (lower<upper x lA uB)
    c≤d : c ≤ d
    c≤d = <-weaken (lower<upper y lc ud)
    c'≤d' : c' ≤ d'
    c'≤d' = <-weaken (lower<upper z lc' ud')
    -- tighten each product bracket to the common [A,B]
    tight-y : min₄ (a *ℚ c) (a *ℚ d) (b *ℚ c) (b *ℚ d)
              ≤ min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d)
    tight-y = min₄-tighten A B a b c d a≤A A≤B B≤b c≤d
    tight-z : min₄ (a' *ℚ c') (a' *ℚ d') (b' *ℚ c') (b' *ℚ d')
              ≤ min₄ (A *ℚ c') (A *ℚ d') (B *ℚ c') (B *ℚ d')
    tight-z = min₄-tighten A B a' b' c' d' a'≤A A≤B B≤b' c'≤d'
    P<tight : P < min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d)
    P<tight = <-≤-trans P<m tight-y
    S<tight : S < min₄ (A *ℚ c') (A *ℚ d') (B *ℚ c') (B *ℚ d')
    S<tight = <-≤-trans S<m' tight-z
    q<sum : q < (min₄ (A *ℚ c) (A *ℚ d) (B *ℚ c) (B *ℚ d) +ℚ
                 min₄ (A *ℚ c') (A *ℚ d') (B *ℚ c') (B *ℚ d'))
    q<sum = <-trans q<PS (<-sum P<tight S<tight)
    q<final : q < min₄ (A *ℚ (c +ℚ c')) (A *ℚ (d +ℚ d')) (B *ℚ (c +ℚ c')) (B *ℚ (d +ℚ d'))
    q<final = <-≤-trans q<sum (min₄-superadd A B c d c' d')
```

The right-handed subdistributive law is the same statement read
through [[commutativity|real-multiplication]]: rewriting each factor
$y \cdot x = x \cdot y$ and $(y + z) \cdot x = x \cdot (y + z)$
transports the containment along the two equalities.

```agda
*ᴿ-distribʳ-≤
  : ∀ x y z → ((y *ᴿ x) +ᴿ (z *ᴿ x)) ≤ᴿ ((y +ᴿ z) *ᴿ x)
*ᴿ-distribʳ-≤ x y z =
  subst₂ _≤ᴿ_
    (sym (ap₂ _+ᴿ_ (*ᴿ-comm y x) (*ᴿ-comm z x)))
    (*ᴿ-comm x (y +ᴿ z))
    (*ᴿ-distribˡ-≤ x y z)
```

<!--
```agda
private
  distrib-witness
    : ∀ x y z q A B C D c c' d d'
    → ∣ x .lower A ∣ → ∣ x .upper B ∣
    → ∣ y .lower c ∣ → ∣ z .lower c' ∣ → (C < c +ℚ c')
    → ∣ y .upper d ∣ → ∣ z .upper d' ∣ → (d +ℚ d' < D)
    → (q < min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D))
    → ∀ ε B₂ B₁ B₁'
    → ((-ℚ B₂) ≤ A) → (B ≤ B₂) → (0 ≤ B₂)
    → ((-ℚ B₁) ≤ c) → (d ≤ B₁) → (0 ≤ B₁)
    → ((-ℚ B₁') ≤ c') → (d' ≤ B₁') → (0 ≤ B₁')
    → ((((B₂ +ℚ B₁) +ℚ (B₂ +ℚ B₁')) *ℚ ε)
       ≤ half (min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D) +ℚ (-ℚ q)))
    → ∀ ax bx → ∣ x .lower ax ∣ → ∣ x .upper bx ∣ → ((bx +ℚ (-ℚ ax)) < ε)
    → ∀ ay by → ∣ y .lower ay ∣ → ∣ y .upper by ∣ → ((by +ℚ (-ℚ ay)) < ε)
    → ∀ az bz → ∣ z .lower az ∣ → ∣ z .upper bz ∣ → ((bz +ℚ (-ℚ az)) < ε)
    → ∣ ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q ∣
  distrib-witness x y z q A B C D c c' d d' lA uB lyc lzc' C<cc' uyd uzd' dd'<D q<M₀
    ε B₂ B₁ B₁' -B₂≤A B≤B₂ 0≤B₂ -B₁≤c d≤B₁ 0≤B₁ -B₁'≤c' d'≤B₁' 0≤B₁' budget
    ax bx lax ubx wx ay by lay uby wy az bz laz ubz wz =
    inc (P , S , xy-wit , xz-wit , q<PS)
    where
    M₀ : Ratio
    M₀ = min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D)
    slack : Ratio
    slack = M₀ +ℚ (-ℚ q)
    0<slack : 0 < slack
    0<slack = <→positive-diff q<M₀
    A' B' c₂ d₂ c₂' d₂' : Ratio
    A' = maxℚ A ax
    B' = minℚ B bx
    c₂ = maxℚ c ay
    d₂ = minℚ d by
    c₂' = maxℚ c' az
    d₂' = minℚ d' bz
    lA' : ∣ x .lower A' ∣
    lA' = maxℚ-lower-mem x lA lax
    uB' : ∣ x .upper B' ∣
    uB' = minℚ-upper-mem x uB ubx
    ly₂ : ∣ y .lower c₂ ∣
    ly₂ = maxℚ-lower-mem y lyc lay
    uy₂ : ∣ y .upper d₂ ∣
    uy₂ = minℚ-upper-mem y uyd uby
    lz₂ : ∣ z .lower c₂' ∣
    lz₂ = maxℚ-lower-mem z lzc' laz
    uz₂ : ∣ z .upper d₂' ∣
    uz₂ = minℚ-upper-mem z uzd' ubz
    A≤A' : A ≤ A'
    A≤A' = maxℚ-≤l {A} {ax}
    B'≤B : B' ≤ B
    B'≤B = minℚ-≤l {B} {bx}
    c≤c₂ : c ≤ c₂
    c≤c₂ = maxℚ-≤l {c} {ay}
    d₂≤d : d₂ ≤ d
    d₂≤d = minℚ-≤l {d} {by}
    c'≤c₂' : c' ≤ c₂'
    c'≤c₂' = maxℚ-≤l {c'} {az}
    d₂'≤d' : d₂' ≤ d'
    d₂'≤d' = minℚ-≤l {d'} {bz}
    A'≤B' : A' ≤ B'
    A'≤B' = <-weaken (lower<upper x lA' uB')
    c₂≤d₂ : c₂ ≤ d₂
    c₂≤d₂ = <-weaken (lower<upper y ly₂ uy₂)
    c₂'≤d₂' : c₂' ≤ d₂'
    c₂'≤d₂' = <-weaken (lower<upper z lz₂ uz₂)
    -B₂≤A' : (-ℚ B₂) ≤ A'
    -B₂≤A' = ≤-trans -B₂≤A A≤A'
    B'≤B₂ : B' ≤ B₂
    B'≤B₂ = ≤-trans B'≤B B≤B₂
    -B₁≤c₂ : (-ℚ B₁) ≤ c₂
    -B₁≤c₂ = ≤-trans -B₁≤c c≤c₂
    d₂≤B₁ : d₂ ≤ B₁
    d₂≤B₁ = ≤-trans d₂≤d d≤B₁
    -B₁'≤c₂' : (-ℚ B₁') ≤ c₂'
    -B₁'≤c₂' = ≤-trans -B₁'≤c' c'≤c₂'
    d₂'≤B₁' : d₂' ≤ B₁'
    d₂'≤B₁' = ≤-trans d₂'≤d' d'≤B₁'
    wx' : (B' +ℚ (-ℚ A')) ≤ ε
    wx' = ≤-trans (+ℚ-preserves-≤ B'≤bx (negℚ-anti-≤ ax≤A')) (<-weaken wx)
      where
      B'≤bx : B' ≤ bx
      B'≤bx = minℚ-≤r {B} {bx}
      ax≤A' : ax ≤ A'
      ax≤A' = maxℚ-≤r {A} {ax}
    wy' : (d₂ +ℚ (-ℚ c₂)) ≤ ε
    wy' = ≤-trans (+ℚ-preserves-≤ d₂≤by (negℚ-anti-≤ ay≤c₂)) (<-weaken wy)
      where
      d₂≤by : d₂ ≤ by
      d₂≤by = minℚ-≤r {d} {by}
      ay≤c₂ : ay ≤ c₂
      ay≤c₂ = maxℚ-≤r {c} {ay}
    wz' : (d₂' +ℚ (-ℚ c₂')) ≤ ε
    wz' = ≤-trans (+ℚ-preserves-≤ d₂'≤bz (negℚ-anti-≤ az≤c₂')) (<-weaken wz)
      where
      d₂'≤bz : d₂' ≤ bz
      d₂'≤bz = minℚ-≤r {d'} {bz}
      az≤c₂' : az ≤ c₂'
      az≤c₂' = maxℚ-≤r {c'} {az}
    c<d : c < d
    c<d = lower<upper y lyc uyd
    c'<d' : c' < d'
    c'<d' = lower<upper z lzc' uzd'
    C≤cc₂ : C ≤ (c₂ +ℚ c₂')
    C≤cc₂ = ≤-trans (<-weaken C<cc') (+ℚ-preserves-≤ c≤c₂ c'≤c₂')
    dd₂≤D : (d₂ +ℚ d₂') ≤ D
    dd₂≤D = ≤-trans (+ℚ-preserves-≤ d₂≤d d₂'≤d') (<-weaken dd'<D)
    cc₂≤dd₂ : (c₂ +ℚ c₂') ≤ (d₂ +ℚ d₂')
    cc₂≤dd₂ = +ℚ-preserves-≤ c₂≤d₂ c₂'≤d₂'
    C≤D : C ≤ D
    C≤D = ≤-trans (<-weaken C<cc') (≤-trans (+ℚ-preserves-≤ (<-weaken c<d) (<-weaken c'<d')) (<-weaken dd'<D))
    M₁' M₂' Msum : Ratio
    M₁' = min₄ (A' *ℚ c₂) (A' *ℚ d₂) (B' *ℚ c₂) (B' *ℚ d₂)
    M₂' = min₄ (A' *ℚ c₂') (A' *ℚ d₂') (B' *ℚ c₂') (B' *ℚ d₂')
    Msum = min₄ (A' *ℚ (c₂ +ℚ c₂')) (A' *ℚ (d₂ +ℚ d₂')) (B' *ℚ (c₂ +ℚ c₂')) (B' *ℚ (d₂ +ℚ d₂'))
    q<Msum : q < Msum
    q<Msum = <-≤-trans
      (<-≤-trans q<M₀ (min₄-tighten A' B' A B C D A≤A' A'≤B' B'≤B C≤D))
      (min₄-tighten₂ A' B' C D (c₂ +ℚ c₂') (d₂ +ℚ d₂') C≤cc₂ cc₂≤dd₂ dd₂≤D)
    sp₁ sp₂ : Ratio
    sp₁ = (B₂ *ℚ (d₂ +ℚ (-ℚ c₂))) +ℚ (B₁ *ℚ (B' +ℚ (-ℚ A')))
    sp₂ = (B₂ *ℚ (d₂' +ℚ (-ℚ c₂'))) +ℚ (B₁' *ℚ (B' +ℚ (-ℚ A')))
    Msum≤ : Msum ≤ ((M₁' +ℚ M₂') +ℚ (sp₁ +ℚ sp₂))
    Msum≤ = ≤-resp refl rearr (≤-trans msum≤sum (+ℚ-preserves-≤ ac₂≤ ac₂'≤))
      where
      msum≤sum : Msum ≤ ((A' *ℚ c₂) +ℚ (A' *ℚ c₂'))
      msum≤sum = ≤-resp refl (*ℚ-distribl A' c₂ c₂')
        (min₄-≤₁ {A' *ℚ (c₂ +ℚ c₂')} {A' *ℚ (d₂ +ℚ d₂')} {B' *ℚ (c₂ +ℚ c₂')} {B' *ℚ (d₂ +ℚ d₂')})
      ac₂≤ : (A' *ℚ c₂) ≤ (M₁' +ℚ sp₁)
      ac₂≤ = ≤-trans (max₄-≥₁ {A' *ℚ c₂} {A' *ℚ d₂} {B' *ℚ c₂} {B' *ℚ d₂})
        (spread-bound A' B' c₂ d₂ B₁ B₂ A'≤B' c₂≤d₂ -B₂≤A' B'≤B₂ 0≤B₂ -B₁≤c₂ d₂≤B₁ 0≤B₁)
      ac₂'≤ : (A' *ℚ c₂') ≤ (M₂' +ℚ sp₂)
      ac₂'≤ = ≤-trans (max₄-≥₁ {A' *ℚ c₂'} {A' *ℚ d₂'} {B' *ℚ c₂'} {B' *ℚ d₂'})
        (spread-bound A' B' c₂' d₂' B₁' B₂ A'≤B' c₂'≤d₂' -B₂≤A' B'≤B₂ 0≤B₂ -B₁'≤c₂' d₂'≤B₁' 0≤B₁')
      rearr : ((M₁' +ℚ sp₁) +ℚ (M₂' +ℚ sp₂)) ≡ ((M₁' +ℚ M₂') +ℚ (sp₁ +ℚ sp₂))
      rearr = sum4-ring M₁' sp₁ M₂' sp₂
    spread<slack : (sp₁ +ℚ sp₂) < slack
    spread<slack = ≤-<-trans (≤-trans sp≤Denomε budget2) (half-lt 0<slack)
      where
      sp≤Denomε : (sp₁ +ℚ sp₂) ≤ (((B₂ +ℚ B₁) +ℚ (B₂ +ℚ B₁')) *ℚ ε)
      sp≤Denomε = ≤-resp refl distrib-Denom
        (+ℚ-preserves-≤
          (+ℚ-preserves-≤ (*ℚ-preserves-≤l B₂ 0≤B₂ wy') (*ℚ-preserves-≤l B₁ 0≤B₁ wx'))
          (+ℚ-preserves-≤ (*ℚ-preserves-≤l B₂ 0≤B₂ wz') (*ℚ-preserves-≤l B₁' 0≤B₁' wx')))
        where
        distrib-Denom
          : (((B₂ *ℚ ε) +ℚ (B₁ *ℚ ε)) +ℚ ((B₂ *ℚ ε) +ℚ (B₁' *ℚ ε)))
            ≡ (((B₂ +ℚ B₁) +ℚ (B₂ +ℚ B₁')) *ℚ ε)
        distrib-Denom = rational!
      budget2 : (((B₂ +ℚ B₁) +ℚ (B₂ +ℚ B₁')) *ℚ ε) ≤ half slack
      budget2 = budget
    μ : Ratio
    μ = M₁' +ℚ M₂'
    q<μ : q < μ
    q<μ = <-≤-trans (lt-move (sp₁ +ℚ sp₂) sp<Msum-q) (sub-move (sp₁ +ℚ sp₂) Msum≤)
      where
      sp<Msum-q : (sp₁ +ℚ sp₂) < (Msum +ℚ (-ℚ q))
      sp<Msum-q = <-≤-trans spread<slack (+ℚ-preserves-≤ M₀≤Msum (≤-refl { -ℚ q}))
        where
        M₀≤Msum : M₀ ≤ Msum
        M₀≤Msum = ≤-trans (min₄-tighten A' B' A B C D A≤A' A'≤B' B'≤B C≤D)
                          (min₄-tighten₂ A' B' C D (c₂ +ℚ c₂') (d₂ +ℚ d₂') C≤cc₂ cc₂≤dd₂ dd₂≤D)
    gap' : Ratio
    gap' = μ +ℚ (-ℚ q)
    0<gap' : 0 < gap'
    0<gap' = <→positive-diff q<μ
    hh : Ratio
    hh = half (half gap')
    0<hh : 0 < hh
    0<hh = half-pos (half-pos 0<gap')
    P S : Ratio
    P = M₁' +ℚ (-ℚ hh)
    S = M₂' +ℚ (-ℚ hh)
    P<M₁' : P < M₁'
    P<M₁' = sub-pos-< M₁' hh 0<hh
    S<M₂' : S < M₂'
    S<M₂' = sub-pos-< M₂' hh 0<hh
    PS≡ : (P +ℚ S) ≡ (μ +ℚ (-ℚ half gap'))
    PS≡ = ring-ps ∙ ap (λ w → μ +ℚ (-ℚ w)) (half-sum (half gap'))
      where
      ring-ps : ((M₁' +ℚ (-ℚ hh)) +ℚ (M₂' +ℚ (-ℚ hh))) ≡ ((M₁' +ℚ M₂') +ℚ (-ℚ (hh +ℚ hh)))
      ring-ps = ps-ring M₁' M₂' hh
    q<PS : q < (P +ℚ S)
    q<PS = subst (λ w → q < w) (sym PS≡) base
      where
      base : q < (μ +ℚ (-ℚ half gap'))
      base = lt-move {q} {μ} (half gap') (half-lt 0<gap')
    xy-wit : ∣ (x *ᴿ y) .lower P ∣
    xy-wit = inc (A' , B' , c₂ , d₂ , lA' , uB' , ly₂ , uy₂ , P<M₁')
    xz-wit : ∣ (x *ᴿ z) .lower S ∣
    xz-wit = inc (A' , B' , c₂' , d₂' , lA' , uB' , lz₂ , uz₂ , S<M₂')
```
-->

<!--
```agda
private
  distrib-core
    : ∀ x y z q A B C D c c' d d'
    → ∣ x .lower A ∣ → ∣ x .upper B ∣
    → ∣ y .lower c ∣ → ∣ z .lower c' ∣ → (C < c +ℚ c')
    → ∣ y .upper d ∣ → ∣ z .upper d' ∣ → (d +ℚ d' < D)
    → (q < min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D))
    → ∣ ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q ∣
  distrib-core x y z q A B C D c c' d d' lA uB lyc lzc' C<cc' uyd uzd' dd'<D q<M₀ =
    ∥-∥-rec prop
      (λ (ax , bx , lax , ubx , wx) → ∥-∥-rec prop
        (λ (ay , by , lay , uby , wy) → ∥-∥-rec prop
          (λ (az , bz , laz , ubz , wz) →
            distrib-witness x y z q A B C D c c' d d'
              lA uB lyc lzc' C<cc' uyd uzd' dd'<D q<M₀
              ε B₂ B₁ B₁'
              (bound-lo A B) (bound-hi A B) (bound-nn A B)
              (bound-lo c d) (bound-hi c d) (bound-nn c d)
              (bound-lo c' d') (bound-hi c' d') (bound-nn c' d')
              budget
              ax bx lax ubx wx ay by lay uby wy az bz laz ubz wz)
          (approx z ε 0<ε))
        (approx y ε 0<ε))
      (approx x ε 0<ε)
    where
    prop : is-prop ∣ ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q ∣
    prop = ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q .is-tr
    M₀ : Ratio
    M₀ = min₄ (A *ℚ C) (A *ℚ D) (B *ℚ C) (B *ℚ D)
    slack : Ratio
    slack = M₀ +ℚ (-ℚ q)
    0<slack : 0 < slack
    0<slack = <→positive-diff q<M₀
    B₂ B₁ B₁' Denom : Ratio
    B₂ = maxℚ 1 (maxℚ B (-ℚ A))
    B₁ = maxℚ 1 (maxℚ d (-ℚ c))
    B₁' = maxℚ 1 (maxℚ d' (-ℚ c'))
    Denom = (B₂ +ℚ B₁) +ℚ (B₂ +ℚ B₁')
    0<Denom : 0 < Denom
    0<Denom = sum-pos (sum-pos (bound-pos A B) (bound-nn c d))
                      (<-weaken (sum-pos (bound-pos A B) (bound-nn c' d')))
    Denom-nz : Nonzero Denom
    Denom-nz = inc (positive→nonzero (to-positive 0<Denom))
    ε : Ratio
    ε = (half slack /ℚ Denom) ⦃ Denom-nz ⦄
    0<ε : 0 < ε
    0<ε = div-pos (half slack) Denom ⦃ Denom-nz ⦄ (half-pos 0<slack) 0<Denom
    budget : (Denom *ℚ ε) ≤ half slack
    budget = ≤-resp (sym Denomε≡) refl (≤-refl {half slack})
      where
      Denomε≡ : Denom *ℚ ε ≡ half slack
      Denomε≡ = *ℚ-commutative Denom ε ∙ /ℚ-cancel (half slack) Denom ⦃ Denom-nz ⦄
```
-->

Putting the pieces together, the reverse containment holds: given a
witness that $q$ is below $x \cdot (y + z)$, we intersect its
$x$-, $y$- and $z$-brackets with fresh approximations tight enough
that the super-additive defect of the four-fold minimum falls below
the fixed slack $M_0 - q$, and the summed witness for $x \cdot y + x
\cdot z$ then clears $q$.

```agda
*ᴿ-distribˡ-≥ : ∀ x y z → (x *ᴿ (y +ᴿ z)) ≤ᴿ ((x *ᴿ y) +ᴿ (x *ᴿ z))
*ᴿ-distribˡ-≥ x y z q = □-rec prop
  (λ (A , B , C , D , lA , uB , lyzC , uyzD , q<M₀) →
    □-rec prop (λ (c , c' , lyc , lzc' , C<cc') →
      □-rec prop (λ (d , d' , uyd , uzd' , dd'<D) →
        distrib-core x y z q A B C D c c' d d'
          lA uB lyc lzc' C<cc' uyd uzd' dd'<D q<M₀)
        uyzD)
      lyzC)
  where
  prop : is-prop ∣ ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q ∣
  prop = ((x *ᴿ y) +ᴿ (x *ᴿ z)) .lower q .is-tr
```

Combining both containments gives the **distributive law**, and its
right-handed form by commutativity — completing the ordered-ring
structure of the reals.

```agda
*ᴿ-distribˡ : ∀ x y z → x *ᴿ (y +ᴿ z) ≡ (x *ᴿ y) +ᴿ (x *ᴿ z)
*ᴿ-distribˡ x y z = ≤ᴿ-antisym (*ᴿ-distribˡ-≥ x y z) (*ᴿ-distribˡ-≤ x y z)

*ᴿ-distribʳ : ∀ x y z → (y +ᴿ z) *ᴿ x ≡ (y *ᴿ x) +ᴿ (z *ᴿ x)
*ᴿ-distribʳ x y z =
  *ᴿ-comm (y +ᴿ z) x
  ∙ *ᴿ-distribˡ x y z
  ∙ ap₂ _+ᴿ_ (*ᴿ-comm x y) (*ᴿ-comm x z)
```


