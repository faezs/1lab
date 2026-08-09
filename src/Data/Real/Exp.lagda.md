<!--
```agda
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
open import Data.Real.Complete
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Nat.Base using (Nat ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-sucr ; +-commutative)
open import Data.Sum
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Real.Exp where
```

# The exponential via power series {defines="real-exponential exp"}

The [[completeness|real-completeness]] primitive `lim`{.Agda} lets us
finally sum a convergent series of [[reals|dedekind-real]]. This module
builds the **exponential** of a real number of bounded magnitude,
$$
\exp(x) \;=\; \sum_{k=0}^{\infty} \frac{x^k}{k!},
$$
as the limit of its Taylor partial sums. Convergence is *pure rational
bookkeeping*: on the box $\abs x \le N$ every term is dominated by the
rational $T_k = N^k/k!$, whose ratio $T_{k+1}/T_k = N/(k+1)$ drops below
$\tfrac12$ once $k+1 \ge 2N$, so from there the tail is beaten by a
geometric series and the partial sums are Cauchy.

The one thing this construction cannot do *constructively* is choose the
truncation point. Turning "some $n$ makes $T_n \le \varepsilon$" into a
function $\varepsilon \mapsto n$ is the [[Archimedean
property|archimedean]], which lives under a [[propositional
truncation|propositional-truncation]] here (there is no canonical
integer ceiling on the [[rationals|rational]], which are a
set-quotient). Producing such a modulus as a *section* would need
countable choice, which we do not assume. We therefore package the
modulus as an explicit datum `Modulus`{.Agda}: it is honest data —
every part of it is true — but it must be *supplied*, not conjured. Once
supplied, everything below is discharged with **zero postulates**.

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
```
-->

## Factorials and powers as rationals

The embedding $\nQ$ of the naturals is positive on successors and
monotone by one step; both facts fall out of `nℚ-suc`{.Agda}, the
observation that $\nQ(\suc n) = 1 + \nQ n$.

<!--
```agda
private abstract
  nℚ-suc' : ∀ n → nℚ (suc n) ≡ 1 +ℚ nℚ n
  nℚ-suc' n =
    ℤ.pos (suc n) / 1        ≡˘⟨ ap (_/ 1) refl ⟩
    (1 ℤ.+ℤ ℤ.pos n) / 1     ≡˘⟨ +ℚ-common-denom 1 1 (ℤ.pos n) ⟩
    (1 / 1) +ℚ (ℤ.pos n / 1) ∎

  nℚ-nonneg' : ∀ n → 0 ≤ nℚ n
  nℚ-nonneg' zero = ≤-refl
  nℚ-nonneg' (suc n) = subst (0 ≤_) (sym (nℚ-suc' n))
    (≤-trans (<-weaken 0<1') (≤-resp (+ℚ-idl 1) refl (+ℚ-preserves-≤ (≤-refl {1}) (nℚ-nonneg' n))))
```
-->

```agda
0<nℚsuc : ∀ n → 0 < nℚ (suc n)
```

<!--
```agda
0<nℚsuc n = <-≤-trans 0<1'
  (subst (1 ≤_) (sym (nℚ-suc' n))
    (≤-resp (+ℚ-idr 1) refl (+ℚ-preserves-≤ (≤-refl {1}) (nℚ-nonneg' n))))
```
-->

The reciprocal factorial $1/n!$ is defined by the recursion $1/(\suc
n)! = (1/n!)\cdot(1/\suc n)$, which makes it manifestly positive and
gives the key identity $1/(\suc n)! \cdot \nQ(\suc n) = 1/n!$ for free —
sidestepping any need to reason about factorials of products.

```agda
recip-fact : Nat → Ratio
recip-fact zero = 1
recip-fact (suc n) = recip-fact n *ℚ invℚ (nℚ (suc n)) ⦃ nz ⦄
  where nz : Nonzero (nℚ (suc n))
        nz = inc (positive→nonzero (to-positive (0<nℚsuc n)))

0<recip-fact : ∀ n → 0 < recip-fact n
0<recip-fact zero = 0<1'
0<recip-fact (suc n) = from-positive
  (*ℚ-positive (to-positive (0<recip-fact n)) (invℚ-positive (to-positive (0<nℚsuc n))))

recip-fact-rec : ∀ n → recip-fact (suc n) *ℚ nℚ (suc n) ≡ recip-fact n
recip-fact-rec n =
  (recip-fact n *ℚ invℚ (nℚ (suc n)) ⦃ nz ⦄) *ℚ nℚ (suc n)
    ≡⟨ sym (*ℚ-associative (recip-fact n) _ _) ⟩
  recip-fact n *ℚ (invℚ (nℚ (suc n)) ⦃ nz ⦄ *ℚ nℚ (suc n))
    ≡⟨ ap (recip-fact n *ℚ_) (*ℚ-invl ⦃ nz ⦄) ⟩
  recip-fact n *ℚ 1
    ≡⟨ *ℚ-idr (recip-fact n) ⟩
  recip-fact n ∎
  where nz : Nonzero (nℚ (suc n))
        nz = inc (positive→nonzero (to-positive (0<nℚsuc n)))
```

Powers of a rational, and the **term bound** $T_k = (1/k!)\,N^k$ that
will dominate the $k$-th summand.

```agda
powℚ : Ratio → Nat → Ratio
powℚ p zero = 1
powℚ p (suc n) = p *ℚ powℚ p n

Tℚ : Ratio → Nat → Ratio
Tℚ N k = recip-fact k *ℚ powℚ N k
```

<!--
```agda
private abstract
  powℚ-nonneg : ∀ N → 0 ≤ N → ∀ k → 0 ≤ powℚ N k
  powℚ-nonneg N 0≤N zero = <-weaken 0<1'
  powℚ-nonneg N 0≤N (suc k) = *ℚ-nonnegative 0≤N (powℚ-nonneg N 0≤N k)

  Tℚ-nonneg : ∀ N → 0 ≤ N → ∀ k → 0 ≤ Tℚ N k
  Tℚ-nonneg N 0≤N k = *ℚ-nonnegative (<-weaken (0<recip-fact k)) (powℚ-nonneg N 0≤N k)
```
-->

## Multiplying point cuts

To bound a real product by a rational product we need only the *upper*
half of the fact that $\ratℝ$ is multiplicative: a rational below the
[[interval product|interval-product]] of two point cuts is below their
rational product, since it is below the four-fold minimum of a bracket,
which the [[bracketing lemma|real-multiplication]] pins below $p \cdot
q$.

```agda
ratℝ-*-≤ : ∀ p q → (ratℝ p *ᴿ ratℝ q) ≤ᴿ ratℝ (p *ℚ q)
ratℝ-*-≤ p q t = □-rec (hlevel 1) λ (a , b , c , d , la , ub , lc , ud , t<m) →
  <-≤-trans t<m (bracket-lower p q a b c d (<-weaken la) (<-weaken ub) (<-weaken lc) (<-weaken ud))
```

## Real powers and the power bound

```agda
_^ᴿ_ : ℝ → Nat → ℝ
x ^ᴿ zero = 1ᴿ
x ^ᴿ suc n = x *ᴿ (x ^ᴿ n)

infixr 8 _^ᴿ_
```

A nonnegative rational bounds its own absolute value, and — inducting
on the exponent through `abs-prod`{.Agda} and `ratℝ-*-≤`{.Agda} — a
bound $\abs x \le N$ propagates to $\abs{x^k} \le N^k$.

```agda
absᴿ-ratℝ-nn : ∀ p → 0 ≤ p → absᴿ (ratℝ p) ≤ᴿ ratℝ p
absᴿ-ratℝ-nn p 0≤p = abs-≤ {ratℝ p} {ratℝ p} (≤ᴿ-refl {ratℝ p})
  (subst (_≤ᴿ ratℝ p) (sym (ratℝ-neg p)) (ratℝ-mono { -ℚ p} {p} -p≤p))
  where
  -p≤p : (-ℚ p) ≤ p
  -p≤p = ≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ 0≤p)) 0≤p

pow-bound : ∀ x N → absᴿ x ≤ᴿ ratℝ N → ∀ k → absᴿ (x ^ᴿ k) ≤ᴿ ratℝ (powℚ N k)
pow-bound x N b zero = absᴿ-ratℝ-nn 1 (<-weaken 0<1')
pow-bound x N b (suc k) =
  ≤ᴿ-trans {absᴿ (x *ᴿ (x ^ᴿ k))} {ratℝ N *ᴿ ratℝ (powℚ N k)} {ratℝ (N *ℚ powℚ N k)}
    (abs-prod {x} {x ^ᴿ k} {ratℝ N} {ratℝ (powℚ N k)} b (pow-bound x N b k))
    (ratℝ-*-≤ N (powℚ N k))
```

## The terms and the partial sums

The $k$-th Taylor term and its bound $\abs{\text{term}_k} \le T_k$, then
the partial sums $\sum_{k \le n}$ by the obvious recursion.

```agda
exp-term : ℝ → Nat → ℝ
exp-term x k = ratℝ (recip-fact k) *ᴿ (x ^ᴿ k)

term-bound : ∀ x N → absᴿ x ≤ᴿ ratℝ N → ∀ k → absᴿ (exp-term x k) ≤ᴿ ratℝ (Tℚ N k)
term-bound x N b k =
  ≤ᴿ-trans {absᴿ (ratℝ (recip-fact k) *ᴿ (x ^ᴿ k))}
           {ratℝ (recip-fact k) *ᴿ ratℝ (powℚ N k)}
           {ratℝ (recip-fact k *ℚ powℚ N k)}
    (abs-prod {ratℝ (recip-fact k)} {x ^ᴿ k} {ratℝ (recip-fact k)} {ratℝ (powℚ N k)}
      (absᴿ-ratℝ-nn (recip-fact k) (<-weaken (0<recip-fact k)))
      (pow-bound x N b k))
    (ratℝ-*-≤ (recip-fact k) (powℚ N k))

exp-partial : ℝ → Nat → ℝ
exp-partial x zero = exp-term x zero
exp-partial x (suc n) = exp-partial x n +ᴿ exp-term x (suc n)
```

## Telescoping the tail

The rational **tail budget** $\Ttail_n^j = \sum_{i=1}^{j} T_{n+i}$
bounds the distance between two partial sums: telescoping across the
new terms and summing their bounds with `abs-sum`{.Agda},
$$
\abs{P_{j+n} - P_n} \;\le\; \ratℝ\!\left(\Ttail_n^j\right).
$$
The index is written $j + n$ so that `suc j + n` reduces definitionally
to `suc (j + n)`, keeping the induction on $j$ clean.

```agda
Ttail : Ratio → Nat → Nat → Ratio
Ttail N n zero = 0
Ttail N n (suc j) = Ttail N n j +ℚ Tℚ N (suc (j + n))
```

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)
  tele-id : ∀ A t B → (A R.+ t) R.+ (R.- B) ≡ (A R.+ (R.- B)) R.+ t
  tele-id A t B = cring! S
  neg-sub : ∀ A B → R.- (A R.+ (R.- B)) ≡ B R.+ (R.- A)
  neg-sub A B = cring! S
private module RI = Identities ℝ-comm

private
  abs0 : absᴿ 0ᴿ ≡ 0ᴿ
  abs0 =
    maxᴿ 0ᴿ (-ᴿ 0ᴿ)        ≡⟨ ap (maxᴿ 0ᴿ) (ratℝ-neg 0) ⟩
    maxᴿ 0ᴿ (ratℝ (-ℚ 0))  ≡⟨ ap (λ z → maxᴿ 0ᴿ (ratℝ z)) neg-zero ⟩
    maxᴿ 0ᴿ 0ᴿ             ≡⟨ maxᴿ-idem 0ᴿ ⟩
    0ᴿ                     ∎
```
-->

```agda
tail-bound : ∀ x N → absᴿ x ≤ᴿ ratℝ N → ∀ n j
  → absᴿ (exp-partial x (j + n) +ᴿ (-ᴿ exp-partial x n)) ≤ᴿ ratℝ (Ttail N n j)
tail-bound x N b n zero = subst (_≤ᴿ ratℝ 0) (sym az) (≤ᴿ-refl {ratℝ 0})
  where az : absᴿ (exp-partial x n +ᴿ (-ᴿ exp-partial x n)) ≡ ratℝ 0
        az = ap absᴿ (+ᴿ-invr (exp-partial x n)) ∙ abs0
tail-bound x N b n (suc j) =
  subst (λ z → absᴿ z ≤ᴿ ratℝ (Ttail N n (suc j))) (sym (RI.tele-id A t B))
    (subst (absᴿ ((A +ᴿ (-ᴿ B)) +ᴿ t) ≤ᴿ_) rateq
      (abs-sum {A +ᴿ (-ᴿ B)} {t} {ratℝ (Ttail N n j)} {ratℝ (Tℚ N (suc (j + n)))}
        (tail-bound x N b n j) (term-bound x N b (suc (j + n)))))
  where
  A = exp-partial x (j + n)
  t = exp-term x (suc (j + n))
  B = exp-partial x n
  rateq : (ratℝ (Ttail N n j) +ᴿ ratℝ (Tℚ N (suc (j + n)))) ≡ ratℝ (Ttail N n (suc j))
  rateq = sym (ratℝ-+ (Ttail N n j) (Tℚ N (suc (j + n))))
```

## The geometric estimate

Past the threshold $2N \le \nQ(\suc n)$ the ratio drops below a half:
$2\,T_{\suc n} \le T_n$. This is the whole convergence story, and it is
proved by factoring out $c = (1/(\suc n)!)\,N^n \ge 0$ and comparing the
scalars $2N \le \nQ(\suc n)$.

<!--
```agda
private
  lhs-lem : ∀ (r n p : Ratio) → (r *ℚ (n *ℚ p)) +ℚ (r *ℚ (n *ℚ p)) ≡ (r *ℚ p) *ℚ (2 *ℚ n)
  lhs-lem r n p = rational!

  swap-mul : ∀ (r s t : Ratio) → (r *ℚ s) *ℚ t ≡ (r *ℚ t) *ℚ s
  swap-mul r s t = rational!
```
-->

```agda
ratio-lemma : ∀ (N : Ratio) → 0 ≤ N → ∀ (m : Nat) → (2 *ℚ N) ≤ nℚ (suc m)
  → (Tℚ N (suc m) +ℚ Tℚ N (suc m)) ≤ Tℚ N m
ratio-lemma N 0≤N m thr =
  ≤-resp (sym lhs) (sym rhs) (*ℚ-preserves-≤l c 0≤c thr)
  where
  c : Ratio
  c = recip-fact (suc m) *ℚ powℚ N m
  0≤c : 0 ≤ c
  0≤c = *ℚ-nonnegative (<-weaken (0<recip-fact (suc m))) (powℚ-nonneg N 0≤N m)
  lhs : Tℚ N (suc m) +ℚ Tℚ N (suc m) ≡ c *ℚ (2 *ℚ N)
  lhs = lhs-lem (recip-fact (suc m)) N (powℚ N m)
  rhs : Tℚ N m ≡ c *ℚ nℚ (suc m)
  rhs = ap (_*ℚ powℚ N m) (sym (recip-fact-rec m))
      ∙ swap-mul (recip-fact (suc m)) (nℚ (suc m)) (powℚ N m)
```

Peeling the *first* term instead of the last turns the tail budget into
a recursion on the starting index, from which a single induction shows
the whole tail is dominated by its head: $\Ttail_n^j \le T_n$ whenever
$n$ is past the threshold. (At the closing step $2\,T_{\suc n} \le T_n$
absorbs the doubled head.)

<!--
```agda
private abstract
  Ttail-peel : ∀ N n j → Ttail N n (suc j) ≡ (Tℚ N (suc n) +ℚ Ttail N (suc n) j)
  Ttail-peel N n zero = +ℚ-idl (Tℚ N (suc n)) ∙ sym (+ℚ-idr (Tℚ N (suc n)))
  Ttail-peel N n (suc j) =
    ap (_+ℚ Tℚ N (suc (suc j + n))) (Ttail-peel N n j)
    ∙ sym (+ℚ-associative (Tℚ N (suc n)) (Ttail N (suc n) j) (Tℚ N (suc (suc j + n))))
    ∙ ap (λ z → Tℚ N (suc n) +ℚ (Ttail N (suc n) j +ℚ Tℚ N (suc z))) (sym (+-sucr j n))
```
-->

```agda
tail-le-head : ∀ N → 0 ≤ N → ∀ n
  → (thr : ∀ i → (2 *ℚ N) ≤ nℚ (suc (i + n)))
  → ∀ j → Ttail N n j ≤ Tℚ N n
tail-le-head N 0≤N n thr zero = Tℚ-nonneg N 0≤N n
tail-le-head N 0≤N n thr (suc j) =
  ≤-resp (sym (Ttail-peel N n j)) refl step
  where
  thr' : ∀ i → (2 *ℚ N) ≤ nℚ (suc (i + suc n))
  thr' i = subst (λ z → (2 *ℚ N) ≤ nℚ (suc z)) (sym (+-sucr i n)) (thr (suc i))
  ih : Ttail N (suc n) j ≤ Tℚ N (suc n)
  ih = tail-le-head N 0≤N (suc n) thr' j
  step : (Tℚ N (suc n) +ℚ Ttail N (suc n) j) ≤ Tℚ N n
  step = ≤-trans (+ℚ-preserves-≤ (≤-refl {Tℚ N (suc n)}) ih)
    (ratio-lemma N 0≤N n (thr 0))
```

## The convergence modulus

A **modulus** for $\exp$ on the box $\abs x \le N$ chooses, for each
positive slack $\varepsilon$, a truncation index `at ε` at which the
head term is already below $\varepsilon$ (`small`) and which lies past
the geometric threshold (`past`). As explained above, such a choice is
true but not constructible without countable choice, so it is taken as
input. A later producer holding a concrete rational ceiling (buildable
from `Data.Int.DivMod`) could discharge it.

```agda
record Modulus (x : ℝ) (N : Ratio) : Type where
  no-eta-equality
  field
    N≥0   : 0 ≤ N
    at    : (ε : Ratio) → 0 < ε → Nat
    small : ∀ ε (p : 0 < ε) → Tℚ N (at ε p) ≤ ε
    past  : ∀ ε (p : 0 < ε) (i : Nat) → (2 *ℚ N) ≤ nℚ (suc (i + at ε p))
```

<!--
```agda
private
  split-nat : (a b : Nat) → (Σ Nat λ j → a + j ≡ b) ⊎ (Σ Nat λ j → b + j ≡ a)
  split-nat zero b = inl (b , refl)
  split-nat (suc a) zero = inr (suc a , refl)
  split-nat (suc a) (suc b) with split-nat a b
  ... | inl (j , e) = inl (j , ap suc e)
  ... | inr (j , e) = inr (j , ap suc e)

  absᴿ-sub-sym : ∀ u v → absᴿ (u +ᴿ (-ᴿ v)) ≡ absᴿ (v +ᴿ (-ᴿ u))
  absᴿ-sub-sym u v = ap absᴿ (sym (RI.neg-sub v u)) ∙ absᴿ-neg (v +ᴿ (-ᴿ u))

module _ (x : ℝ) (N : Ratio) (b : absᴿ x ≤ᴿ ratℝ N) (M : Modulus x N) where
  private
    open Modulus M
    P : Nat → ℝ
    P = exp-partial x

    -- |P(j + at ε) − P(at ε)| ≤ ε, uniformly in j.
    seg-bd : ∀ ε (p : 0 < ε) (j : Nat)
      → absᴿ (P (j + at ε p) +ᴿ (-ᴿ P (at ε p))) ≤ᴿ ratℝ ε
    seg-bd ε p j = ≤ᴿ-trans {absᴿ (P (j + at ε p) +ᴿ (-ᴿ P (at ε p)))}
                            {ratℝ (Ttail N (at ε p) j)} {ratℝ ε}
      (tail-bound x N b (at ε p) j)
      (ratℝ-mono {Ttail N (at ε p) j} {ε}
        (≤-trans (tail-le-head N N≥0 (at ε p) (past ε p) j) (small ε p)))

    fbound : ∀ ε δ (p : 0 < ε) (r : 0 < δ)
      → absᴿ (P (at ε p) +ᴿ (-ᴿ P (at δ r))) ≤ᴿ ratℝ (ε +ℚ δ)
    fbound ε δ p r with split-nat (at ε p) (at δ r)
    ... | inl (j , e) = subst (λ z → absᴿ (P (at ε p) +ᴿ (-ᴿ P z)) ≤ᴿ ratℝ (ε +ℚ δ)) e proof-inl
      where
      a = at ε p
      flp : absᴿ (P a +ᴿ (-ᴿ P (a + j))) ≡ absᴿ (P (j + a) +ᴿ (-ᴿ P a))
      flp = absᴿ-sub-sym (P a) (P (a + j))
          ∙ ap (λ z → absᴿ (P z +ᴿ (-ᴿ P a))) (+-commutative a j)
      proof-inl : absᴿ (P a +ᴿ (-ᴿ P (a + j))) ≤ᴿ ratℝ (ε +ℚ δ)
      proof-inl = subst (_≤ᴿ ratℝ (ε +ℚ δ)) (sym flp)
        (≤ᴿ-trans {absᴿ (P (j + a) +ᴿ (-ᴿ P a))} {ratℝ ε} {ratℝ (ε +ℚ δ)}
          (seg-bd ε p j)
          (ratℝ-mono {ε} {ε +ℚ δ}
            (≤-resp (+ℚ-idr ε) refl (+ℚ-preserves-≤ (≤-refl {ε}) (<-weaken r)))))
    ... | inr (j , e) = subst (λ z → absᴿ (P z +ᴿ (-ᴿ P (at δ r))) ≤ᴿ ratℝ (ε +ℚ δ)) e proof-inr
      where
      bb = at δ r
      proof-inr : absᴿ (P (bb + j) +ᴿ (-ᴿ P bb)) ≤ᴿ ratℝ (ε +ℚ δ)
      proof-inr = subst (λ z → absᴿ (P z +ᴿ (-ᴿ P bb)) ≤ᴿ ratℝ (ε +ℚ δ))
        (sym (+-commutative bb j))
        (≤ᴿ-trans {absᴿ (P (j + bb) +ᴿ (-ᴿ P bb))} {ratℝ δ} {ratℝ (ε +ℚ δ)}
          (seg-bd δ r j)
          (ratℝ-mono {δ} {ε +ℚ δ}
            (≤-resp (+ℚ-idl δ) refl (+ℚ-preserves-≤ (<-weaken p) (≤-refl {δ})))))

  exp-approx-build : CauchyApprox
  exp-approx-build .fst ε p = exp-partial x (Modulus.at M ε p)
  exp-approx-build .snd ε δ p r = fbound ε δ p r
```
-->

Assembling the partial sums into a `CauchyApprox`{.Agda} and taking its
limit gives the exponential.

```agda
exp-approx : (x : ℝ) (N : Ratio) → absᴿ x ≤ᴿ ratℝ N → Modulus x N → CauchyApprox
exp-approx x N b M = exp-approx-build x N b M

exp : (x : ℝ) (N : Ratio) → absᴿ x ≤ᴿ ratℝ N → Modulus x N → ℝ
exp x N b M = lim (exp-approx x N b M)
```

## The value at zero

At $x = 0$ every term past the constant vanishes — $0^{\suc k} = 0$
absorbs the whole product — so every partial sum is exactly $1$, and
the limit of the constant approximation is $1$.

```agda
exp-partial-0 : ∀ n → exp-partial 0ᴿ n ≡ 1ᴿ
```

<!--
```agda
private
  0^suc : ∀ k → (0ᴿ ^ᴿ suc k) ≡ 0ᴿ
  0^suc k = *ᴿ-zeroˡ (0ᴿ ^ᴿ k)

  exp-term-0-suc : ∀ k → exp-term 0ᴿ (suc k) ≡ 0ᴿ
  exp-term-0-suc k =
    ap (ratℝ (recip-fact (suc k)) *ᴿ_) (0^suc k) ∙ *ᴿ-zeroʳ (ratℝ (recip-fact (suc k)))

exp-partial-0 zero = *ᴿ-idl 1ᴿ
exp-partial-0 (suc n) =
  ap₂ _+ᴿ_ (exp-partial-0 n) (exp-term-0-suc n) ∙ +ᴿ-idr 1ᴿ
```
-->

```agda
exp-0 : ∀ (N : Ratio) (b : absᴿ 0ᴿ ≤ᴿ ratℝ N) (M : Modulus 0ᴿ N)
  → exp 0ᴿ N b M ≡ 1ᴿ
exp-0 N b M = limit-unique A (lim A) 1ᴿ (lim-is-limit A) 1ᴿ-is-limit
  where
  A = exp-approx 0ᴿ N b M
  1ᴿ-is-limit : is-limit A 1ᴿ
  1ᴿ-is-limit ε p =
    subst (λ z → absᴿ (1ᴿ +ᴿ (-ᴿ z)) ≤ᴿ ratℝ (2 *ℚ ε))
      (sym (exp-partial-0 (Modulus.at M ε p)))
      (subst (_≤ᴿ ratℝ (2 *ℚ ε)) (sym az) 0≤2ε)
    where
    az : absᴿ (1ᴿ +ᴿ (-ᴿ 1ᴿ)) ≡ ratℝ 0
    az = ap absᴿ (+ᴿ-invr 1ᴿ) ∙ abs0
    ε<2ε : ε < (2 *ℚ ε)
    ε<2ε = <-resp refl (x+x≡x*2 ε ∙ *ℚ-commutative ε 2) (add-pos-< ε ε p)
    0≤2ε : ratℝ 0 ≤ᴿ ratℝ (2 *ℚ ε)
    0≤2ε = ratℝ-mono {0} {2 *ℚ ε} (<-weaken (<-trans p ε<2ε))
```

## What is deferred

The **derivative identity** $\exp' = \exp$ is not proved here: obtaining
it by termwise differentiation of these partial sums would require a
second completeness layer at the level of Hadamard towers; it is cheaper
via a future integral/Picard pass over the fundamental theorem. The
**functional equation** $\exp(x+y) = \exp(x)\exp(y)$ (a Cauchy-product
rearrangement of these series) and the coupled **sine/cosine** system
are likewise left for later. What is delivered is the honest,
zero-postulate *value* $\exp(x)$ on any compact box, given a
convergence modulus.
