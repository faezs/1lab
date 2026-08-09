<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Complete
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Exp
open import Data.Real.Smooth.Integral using (pow2)
open import Data.Real.Smooth.Convergence
  using (ceilℚ ; ceilℚ-bound ; two-pow-inv ; pow2-mod ; mod-spec ; 0<nℚ-pow2)
open import Data.Nat.Base using (Nat ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-associative ; +-commutative)
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Real.Exp.Modulus where
```

# Discharging the exponential's modulus {defines="exp-modulus"}

`Data.Real.Exp`{.Agda} builds $\exp(x)$ on the box $\abs x \le N$ from a
`Modulus`{.Agda}: a function taking a positive slack $\varepsilon$ to a
truncation index that is both *past the geometric threshold* ($2N \le
\nQ(\suc(i + k))$ for every $i$) and *small* ($T_k \le \varepsilon$,
where $T_k = N^k/k!$). That module took the modulus as input because it
had no rational ceiling to hand: the naive route to "some $k$ works" is
the [[archimedean property|archimedean]], which lives under a
[[propositional truncation|propositional-truncation]], and turning it
into a section would need countable choice.

`Data.Real.Smooth.Convergence`{.Agda} since produced exactly the missing
piece — the *concrete* ceiling `ceilℚ`{.Agda}, read off the chosen
fraction representative of a rational, together with the power-of-two
modulus `pow2-mod`{.Agda} satisfying $C\cdot 2^{-\mathrm{pow2mod}(C,
\varepsilon)} \le \varepsilon$. This module spends those two facts to
build the modulus outright, so the exponential becomes a function of
$x$, $N$ and a bound alone.

The recipe has two halves. The **threshold** half is immediate: take
$$
m_0 \;=\; \lceil 2N \rceil,
$$
so that $2N \le \nQ m_0 \le \nQ(\suc(i+m_0))$ for every $i$; any index
of the shape $j + m_0$ inherits this. The **decay** half is the point
of the threshold: past $m_0$ the ratio lemma of `Data.Real.Exp`{.Agda}
gives $2\,T_{\suc m} \le T_m$, so an induction on $j$ shows
$$
T_{j+m_0}\cdot 2^{j} \;\le\; T_{m_0},
$$
and `pow2-mod`{.Agda} chooses the $j$ that pushes the right-hand side
below $\varepsilon$. Multiplying the two halves together, the index
$$
\mathrm{at}(\varepsilon) \;=\; \mathrm{pow2mod}(T_{m_0}, \varepsilon) + m_0
$$
satisfies both fields at once.

## Rational bookkeeping

Everything below is arithmetic on $\bQ$. The successor law for $\nQ$ and
its consequences (nonnegativity, additivity, monotonicity along an
addend) are private in the modules that own them, so we re-derive them
here rather than editing those files.

<!--
```agda
private abstract
  nℚ-suc' : ∀ n → nℚ (suc n) ≡ 1 +ℚ nℚ n
  nℚ-suc' n =
    ℤ.pos (suc n) / 1        ≡˘⟨ ap (_/ 1) one+pos ⟩
    (1 ℤ.+ℤ ℤ.pos n) / 1     ≡˘⟨ +ℚ-common-denom 1 1 (ℤ.pos n) ⟩
    (1 / 1) +ℚ (ℤ.pos n / 1) ∎
    where
    one+pos : (1 ℤ.+ℤ ℤ.pos n) ≡ ℤ.pos (suc n)
    one+pos = refl

  nℚ-nonneg' : ∀ n → 0 ≤ nℚ n
  nℚ-nonneg' zero = ≤-refl
  nℚ-nonneg' (suc n) = subst (0 ≤_) (sym (nℚ-suc' n))
    (≤-resp (+ℚ-idl 0) refl
      (+ℚ-preserves-≤ (<-weaken 0<1') (nℚ-nonneg' n)))

  nℚ-one' : nℚ 1 ≡ 1
  nℚ-one' = nℚ-suc' 0 ∙ +ℚ-idr 1

  nℚ-add' : ∀ m n → nℚ (m + n) ≡ nℚ m +ℚ nℚ n
  nℚ-add' zero    n = sym (+ℚ-idl (nℚ n))
  nℚ-add' (suc m) n =
      nℚ-suc' (m + n)
    ∙ ap (1 +ℚ_) (nℚ-add' m n)
    ∙ +ℚ-associative 1 (nℚ m) (nℚ n)
    ∙ ap (_+ℚ nℚ n) (sym (nℚ-suc' m))

  nℚ-le-plus' : ∀ m k → nℚ m ≤ nℚ (m + k)
  nℚ-le-plus' m k = subst (nℚ m ≤_) (sym (nℚ-add' m k))
    (≤-resp (+ℚ-idr (nℚ m)) refl
      (+ℚ-preserves-≤ (≤-refl {nℚ m}) (nℚ-nonneg' k)))
```
-->

The reciprocal of $2^{j}$ cancels $\nQ(2^{j})$ and is nonnegative; the
doubling law $\nQ(2^{\suc j}) = \nQ(2^{j})\cdot 2$ is what turns the
ratio lemma into a factor of two.

<!--
```agda
private
  nzp : ∀ n → Nonzero (nℚ (pow2 n))
  nzp n = inc (positive→nonzero (to-positive (0<nℚ-pow2 n)))

  0≤nℚp : ∀ n → 0 ≤ nℚ (pow2 n)
  0≤nℚp n = <-weaken (0<nℚ-pow2 n)

  0≤tpi : ∀ n → 0 ≤ two-pow-inv n
  0≤tpi n = <-weaken (invℚ-pos {nℚ (pow2 n)} ⦃ nzp n ⦄ (0<nℚ-pow2 n))

  tpi-cancel : ∀ n → (nℚ (pow2 n) *ℚ two-pow-inv n) ≡ 1
  tpi-cancel n = *ℚ-invr {nℚ (pow2 n)} {nzp n}

  nℚ-double' : ∀ n → nℚ (pow2 (suc n)) ≡ (nℚ (pow2 n) *ℚ 2)
  nℚ-double' n = nℚ-add' (pow2 n) (pow2 n) ∙ x+x≡x*2 (nℚ (pow2 n))

  dbl-id : ∀ (t q : Ratio) → (t *ℚ (q *ℚ 2)) ≡ ((t +ℚ t) *ℚ q)
  dbl-id t q = rational!
```
-->

The term bound $T_k = (1/k!)N^k$ is nonnegative whenever $N$ is —
`Data.Real.Exp`{.Agda} keeps this private, so again we re-derive it.

<!--
```agda
private
  powℚ-nn : ∀ N → 0 ≤ N → ∀ k → 0 ≤ powℚ N k
  powℚ-nn N 0≤N zero    = <-weaken 0<1'
  powℚ-nn N 0≤N (suc k) = *ℚ-nonnegative 0≤N (powℚ-nn N 0≤N k)

  Tℚ-nn : ∀ N → 0 ≤ N → ∀ k → 0 ≤ Tℚ N k
  Tℚ-nn N 0≤N k = *ℚ-nonnegative (<-weaken (0<recip-fact k)) (powℚ-nn N 0≤N k)
```
-->

## The construction

Fix a nonnegative radius $N$. The threshold index is the concrete
ceiling of $2N$, and `thr₀`{.Agda} says every index at or past it clears
the geometric hurdle.

```agda
private
  module Build (N : Ratio) (0≤N : 0 ≤ N) where
    m₀ : Nat
    m₀ = ceilℚ (2 *ℚ N)

    C : Ratio
    C = Tℚ N m₀

    0≤C : 0 ≤ C
    0≤C = Tℚ-nn N 0≤N m₀

    thr₀ : ∀ i → (2 *ℚ N) ≤ nℚ (suc (i + m₀))
    thr₀ i = ≤-trans (ceilℚ-bound (2 *ℚ N))
      (subst (nℚ m₀ ≤_) (ap nℚ (+-commutative m₀ (suc i)))
        (nℚ-le-plus' m₀ (suc i)))
```

Now the geometric decay, in its multiplicative form $T_{j+m_0}\cdot
\nQ(2^{j}) \le T_{m_0}$ — stated this way the induction needs no
division at all. The successor step rewrites $\nQ(2^{\suc j})$ as
$\nQ(2^{j})\cdot 2$, pulls the two across the product to double the
term, and applies `ratio-lemma`{.Agda} at the threshold `thr₀ j`.

```agda
    decay : ∀ j → (Tℚ N (j + m₀) *ℚ nℚ (pow2 j)) ≤ C
    decay zero = ≤-resp (sym (ap (C *ℚ_) nℚ-one' ∙ *ℚ-idr C)) refl (≤-refl {C})
    decay (suc j) = ≤-resp (sym e₁) refl (≤-trans step (decay j))
      where
      T' : Ratio
      T' = Tℚ N (suc (j + m₀))

      Q : Ratio
      Q = nℚ (pow2 j)

      e₁ : (T' *ℚ nℚ (pow2 (suc j))) ≡ ((T' +ℚ T') *ℚ Q)
      e₁ = ap (T' *ℚ_) (nℚ-double' j) ∙ dbl-id T' Q

      step : ((T' +ℚ T') *ℚ Q) ≤ (Tℚ N (j + m₀) *ℚ Q)
      step = *ℚ-preserves-≤r Q (ratio-lemma N 0≤N (j + m₀) (thr₀ j)) (0≤nℚp j)
```

Dividing through by $\nQ(2^{j})$ — that is, multiplying by
`two-pow-inv j`{.Agda} and cancelling — puts the estimate in the shape
`mod-spec`{.Agda} consumes.

```agda
    decay' : ∀ j → Tℚ N (j + m₀) ≤ (C *ℚ two-pow-inv j)
    decay' j = ≤-resp cancel refl
      (*ℚ-preserves-≤r (two-pow-inv j) (decay j) (0≤tpi j))
      where
      T : Ratio
      T = Tℚ N (j + m₀)

      cancel : ((T *ℚ nℚ (pow2 j)) *ℚ two-pow-inv j) ≡ T
      cancel = sym (*ℚ-associative T (nℚ (pow2 j)) (two-pow-inv j))
             ∙ ap (T *ℚ_) (tpi-cancel j)
             ∙ *ℚ-idr T
```

Both fields are now one line each. Note that the record `Modulus x N` is
indexed by $x$ but *constrains* only $N$, so the same data serves every
point of the box.

```agda
    modulus-for : (x : ℝ) → Modulus x N
    modulus-for x .Modulus.N≥0 = 0≤N
    modulus-for x .Modulus.at ε p = pow2-mod C ε p + m₀
    modulus-for x .Modulus.small ε p =
      ≤-trans (decay' (pow2-mod C ε p)) (mod-spec C ε p 0≤C)
    modulus-for x .Modulus.past ε p i =
      subst (λ z → (2 *ℚ N) ≤ nℚ (suc z))
        (sym (+-associative i (pow2-mod C ε p) m₀))
        (thr₀ (i + pow2-mod C ε p))
```

## The modulus, and a self-contained exponential

```agda
mk-modulus : (x : ℝ) (N : Ratio) → 0 ≤ N → Modulus x N
mk-modulus x N 0≤N = Build.modulus-for N 0≤N x
```

With the modulus discharged, `exp`{.Agda} loses its one *analytic*
input. What remains are the two bookkeeping arguments naming the box:
the bound $\abs x \le \ratℝ N$ itself, and $N \ge 0$ — the latter not
an extra assumption, since it already follows from the former, but
kept explicit to avoid threading `abs-nonneg`{.Agda} through the
rational layer. No convergence datum is supplied by the caller any
more.

```agda
exp! : (x : ℝ) (N : Ratio) → 0 ≤ N → absᴿ x ≤ᴿ ratℝ N → ℝ
exp! x N 0≤N b = exp x N b (mk-modulus x N 0≤N)

exp!-0 : ∀ (N : Ratio) (0≤N : 0 ≤ N) (b : absᴿ 0ᴿ ≤ᴿ ratℝ N)
  → exp! 0ᴿ N 0≤N b ≡ 1ᴿ
exp!-0 N 0≤N b = exp-0 N b (mk-modulus 0ᴿ N 0≤N)
```

Nothing here is an input any more: `mk-modulus`{.Agda} is total on
nonnegative radii, with no truncation, no choice and no postulate. What
remains deferred in `Data.Real.Exp`{.Agda} — the derivative identity
$\exp' = \exp$, the functional equation, and the sine/cosine system — is
untouched by this pass; only the *convergence datum* has been closed.
