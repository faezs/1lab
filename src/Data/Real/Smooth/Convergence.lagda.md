<!--
```agda
{-# OPTIONS --lossy-unification #-}
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
open import Data.Real.Complete
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative using (ratℝ-*-≤ ; abs-nonneg ; diff-zero→≡)
open import Data.Real.Smooth.Integral

open import Data.Fin using (Fin ; fzero ; fsuc ; fin-view ; Discrete-Fin ; Fin-absurd ; Fin-cases)
open import Data.Dec
open import Data.Sum

open import Data.Nat.Base using (Nat ; zero ; suc ; _+_)
import Data.Nat as Nat
import Data.Int.Base as ℤ
import Data.Int.Order as ℤ
import Data.Int.Properties as ℤ
```
-->

```agda
module Data.Real.Smooth.Convergence where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  neg-sum : ∀ a b → R.- (a R.+ b) ≡ (R.- a) R.+ (R.- b)
  neg-sum a b = cring! S

  tele3 : ∀ a b c → a R.+ (R.- c) ≡ (a R.+ (R.- b)) R.+ (b R.+ (R.- c))
  tele3 a b c = cring! S

  reassoc-r : ∀ a b c → (a R.+ b) R.+ c ≡ a R.+ (b R.+ c)
  reassoc-r a b c = cring! S

  mul-sub : ∀ c x y → c R.* (y R.+ (R.- x)) ≡ (c R.* y) R.+ (R.- (c R.* x))
  mul-sub c x y = cring! S

  even-cancel
    : ∀ a b → (a R.+ a) R.+ (R.- (a R.+ b)) ≡ a R.+ (R.- b)
  even-cancel a b = cring! S

  neg-sub : ∀ A B → R.- (A R.+ (R.- B)) ≡ B R.+ (R.- A)
  neg-sub A B = cring! S

private module RI = Identities ℝ-comm
```
-->

# Discharging the convergence of the dyadic Riemann sums {defines="riemann-convergence"}

The [[Riemann integral|riemann-integral]] of `Data.Real.Smooth.Integral`{.Agda}
is defined *relative to* an assumed convergence of the dyadic Riemann
sums (its module parameter `∫-converges`{.Agda}). This module closes
that gap **constructively**, for every integrand carrying a rational
Lipschitz witness on an oriented box $a \le b$: the sums are shown
Cauchy by a single geometric estimate, and their `lim`{.Agda} — the
value `∫L`{.Agda} — is the Riemann limit `∫L-converges`{.Agda}. The
one place countable choice would otherwise intrude — turning "some
index makes the tail small" into an actual $\varepsilon \mapsto N$ — is
dispatched by a concrete rational ceiling built from [[integer
division|integer-division]].

## A concrete Archimedean ceiling

The [[rationals|rational-numbers]] are a set-quotient, with no canonical
integer numerator; but every rational has a *chosen* fraction
representative through the splitting `splitℚ`{.Agda}, and one more than
the absolute value of its numerator is a natural number that dominates
it.

```agda
ceilℚ : Ratio → Nat
ceilℚ r = suc (ℤ.abs (splitℚ r .fst .↑))
```

<!--
```agda
private
  x≤abs : ∀ x → x ℤ.≤ ℤ.pos (ℤ.abs x)
  x≤abs (ℤ.pos m)    = ℤ.≤-refl
  x≤abs (ℤ.negsuc m) = ℤ.<-weaken ℤ.neg<pos

  abs<suc : ∀ x → ℤ.pos (ℤ.abs x) ℤ.< ℤ.pos (suc (ℤ.abs x))
  abs<suc x = ℤ.pos<pos Nat.≤-refl

  s≥1 : ∀ {s} → ℤ.Positive s → 1 ℤ.≤ s
  s≥1 (ℤ.pos m) = ℤ.pos≤pos (Nat.s≤s Nat.0≤x)

  suc-abs≤
    : ∀ x {s} → ℤ.Positive s
    → ℤ.pos (suc (ℤ.abs x)) ℤ.≤ (ℤ.pos (suc (ℤ.abs x)) ℤ.*ℤ s)
  suc-abs≤ x {s} p = ℤ.≤-trans
    (ℤ.≤-refl' (sym (ℤ.*ℤ-oner (ℤ.pos (suc (ℤ.abs x))))))
    (ℤ.≤-trans
      (ℤ.≤-refl' (ℤ.*ℤ-commutative (ℤ.pos (suc (ℤ.abs x))) 1))
      (ℤ.≤-trans
        (ℤ.*ℤ-preserves-≤r {1} {s} (ℤ.pos (suc (ℤ.abs x))) (s≥1 p))
        (ℤ.≤-refl' (ℤ.*ℤ-commutative s (ℤ.pos (suc (ℤ.abs x)))))))

  int-≤ : ∀ x {s} (p : ℤ.Positive s)
        → (x ℤ.*ℤ 1) ℤ.≤ (ℤ.pos (suc (ℤ.abs x)) ℤ.*ℤ s)
  int-≤ x {s} p = ℤ.≤-trans (ℤ.≤-refl' (ℤ.*ℤ-oner x))
    (ℤ.≤-trans (x≤abs x)
      (ℤ.≤-trans (ℤ.<-weaken (abs<suc x)) (suc-abs≤ x p)))

  frac-bound : (f : Fraction) → toℚ f ≤ nℚ (suc (ℤ.abs (f .↑)))
  frac-bound (x / s [ p ]) = toℚ≤ (int-≤ x p)
```
-->

```agda
ceilℚ-bound : ∀ r → r ≤ nℚ (ceilℚ r)
ceilℚ-bound r =
  subst (_≤ nℚ (ceilℚ r)) (splitℚ r .snd) (frac-bound (splitℚ r .fst))
```

## Powers of two

Every `pow2 n`{.Agda} is at least one and dominates $n$; its rational
embedding is therefore positive and has a reciprocal, the geometric
decay factor of the convergence estimate.

```agda
1≤pow2 : ∀ n → 1 Nat.≤ pow2 n
n≤pow2 : ∀ n → n Nat.≤ pow2 n
```

<!--
```agda
private
  le-plusl : ∀ x y → x Nat.≤ x + y
  le-plusl zero    y = Nat.0≤x
  le-plusl (suc x) y = Nat.s≤s (le-plusl x y)

1≤pow2 zero    = Nat.≤-refl
1≤pow2 (suc n) = Nat.≤-trans (1≤pow2 n) (le-plusl (pow2 n) (pow2 n))

n≤pow2 zero    = Nat.0≤x
n≤pow2 (suc n) = Nat.+-preserves-≤ 1 (pow2 n) n (pow2 n) (1≤pow2 n) (n≤pow2 n)
```
-->

## The rational embedding of the naturals

The successor, additivity, nonnegativity and monotonicity of $\nQ$;
all follow from $\nQ(\suc n) = 1 + \nQ n$.

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
    (≤-resp (+ℚ-idl 0) refl
      (+ℚ-preserves-≤ (<-weaken 0<1') (nℚ-nonneg' n)))

  nℚ-one : nℚ 1 ≡ 1
  nℚ-one = nℚ-suc' 0 ∙ +ℚ-idr 1

  nℚ-add : ∀ m n → nℚ (m + n) ≡ nℚ m +ℚ nℚ n
  nℚ-add zero    n = sym (+ℚ-idl (nℚ n))
  nℚ-add (suc m) n =
      nℚ-suc' (m + n)
    ∙ ap (1 +ℚ_) (nℚ-add m n)
    ∙ +ℚ-associative 1 (nℚ m) (nℚ n)
    ∙ ap (_+ℚ nℚ n) (sym (nℚ-suc' m))

  ≤→+ : ∀ {m n} → m Nat.≤ n → Σ Nat (λ k → m + k ≡ n)
  ≤→+ {zero}  {n}     _  = n , refl
  ≤→+ {suc m} {zero}  le = absurd (Nat.¬suc≤0 le)
  ≤→+ {suc m} {suc n} le = let (k , e) = ≤→+ {m} {n} (Nat.≤-peel le) in k , ap suc e

  nℚ-le-plus : ∀ m k → nℚ m ≤ nℚ (m + k)
  nℚ-le-plus m k = subst (nℚ m ≤_) (sym (nℚ-add m k))
    (≤-resp (+ℚ-idr (nℚ m)) refl
      (+ℚ-preserves-≤ (≤-refl {nℚ m}) (nℚ-nonneg' k)))

  nℚ-mono : ∀ {m n} → m Nat.≤ n → nℚ m ≤ nℚ n
  nℚ-mono {m} {n} le =
    let (k , e) = ≤→+ le in subst (nℚ m ≤_) (ap nℚ e) (nℚ-le-plus m k)
```
-->

```agda
0<nℚ-pow2 : ∀ n → 0 < nℚ (pow2 n)
```

<!--
```agda
0<nℚ-pow2 n = <-≤-trans 0<1'
  (subst (_≤ nℚ (pow2 n)) nℚ-one (nℚ-mono (1≤pow2 n)))

private
  nz-pow2 : ∀ n → Nonzero (nℚ (pow2 n))
  nz-pow2 n = inc (positive→nonzero (to-positive (0<nℚ-pow2 n)))
```
-->

The reciprocal of $2^{m}$, and a small cancellation lemma for the
strict order that turns the geometric estimate around.

```agda
two-pow-inv : Nat → Ratio
two-pow-inv m = invℚ (nℚ (pow2 m)) ⦃ nz-pow2 m ⦄
```

<!--
```agda
private
  *ℚ-cancel-≤r : ∀ {a b} w → 0 < w → (a *ℚ w) ≤ (b *ℚ w) → a ≤ b
  *ℚ-cancel-≤r {a} {b} w 0<w h with holds? (a ≤ b)
  ... | yes p = p
  ... | no ¬p = absurd (<-irrefl refl (≤-<-trans h (*ℚ-preserves-<r w b<a 0<w)))
    where
    b<a : b < a
    b<a with ≤-strengthen (≤-is-weakly-total a b ¬p)
    ... | inl e   = absurd (¬p (≤-refl' (sym e)))
    ... | inr b<a = b<a
```
-->

## The Archimedean modulus

Given a rational budget $C$ and a slack $\varepsilon$, the index
`pow2-mod C ε` is the power-of-two ceiling of $C/\varepsilon$: at it,
$C\cdot (1/2)^{N} \le \varepsilon$. This is the single use of the
concrete ceiling; it is reusable — in particular it unblocks the
`Modulus`{.Agda} of `Data.Real.Exp`{.Agda}.

```agda
pow2-mod : (C ε : Ratio) → 0 < ε → Nat
pow2-mod C ε p = ceilℚ ((C /ℚ ε) ⦃ inc (positive→nonzero (to-positive p)) ⦄)

mod-spec
  : ∀ C ε (p : 0 < ε) → 0 ≤ C
  → (C *ℚ two-pow-inv (pow2-mod C ε p)) ≤ ε
```

<!--
```agda
mod-spec C ε p 0≤C = ≤-resp refl cancelε stepC
  where
  instance nzε : Nonzero ε
  nzε = inc (positive→nonzero (to-positive p))

  N : Nat
  N = pow2-mod C ε p

  P : Ratio
  P = nℚ (pow2 N)

  0<P : 0 < P
  0<P = 0<nℚ-pow2 N

  0≤iP : 0 ≤ two-pow-inv N
  0≤iP = <-weaken (invℚ-pos {nℚ (pow2 N)} ⦃ nz-pow2 N ⦄ 0<P)

  stepA : (C /ℚ ε) ≤ P
  stepA = ≤-trans (ceilℚ-bound ((C /ℚ ε) ⦃ nzε ⦄)) (nℚ-mono (n≤pow2 N))

  stepB : C ≤ (ε *ℚ P)
  stepB = ≤-resp (/ℚ-cancel C ε) (*ℚ-commutative P ε)
    (*ℚ-preserves-≤r ε stepA (<-weaken p))

  stepC : (C *ℚ two-pow-inv N) ≤ ((ε *ℚ P) *ℚ two-pow-inv N)
  stepC = *ℚ-preserves-≤r (two-pow-inv N) stepB 0≤iP

  cancelε : ((ε *ℚ P) *ℚ two-pow-inv N) ≡ ε
  cancelε =
      sym (*ℚ-associative ε P (two-pow-inv N))
    ∙ ap (ε *ℚ_) (*ℚ-invr {nℚ (pow2 N)} {nz-pow2 N})
    ∙ *ℚ-idr ε
```
-->

## Regrouping finite sums of reals

The even/odd regrouping of a dyadic sum — the one lemma with no
existing template — together with the negation, difference, and bounded
domination of finite sums. These feed the per-step estimate below.

<!--
```agda
private
  neg0 : (-ᴿ 0ᴿ) ≡ 0ᴿ
  neg0 = ratℝ-neg 0 ∙ ap ratℝ neg-zero

  abs0 : absᴿ 0ᴿ ≡ 0ᴿ
  abs0 = ap (maxᴿ 0ᴿ) neg0 ∙ maxᴿ-idem 0ᴿ

  dbl-suc : ∀ K → (suc K + suc K) ≡ suc (suc (K + K))
  dbl-suc K = ap suc (Nat.+-sucr K K)

  nsuc-mul : ∀ K c → ((nℚ K *ℚ c) +ℚ c) ≡ (nℚ (suc K) *ℚ c)
  nsuc-mul K c =
      +ℚ-commutative (nℚ K *ℚ c) c
    ∙ ap (_+ℚ (nℚ K *ℚ c)) (sym (*ℚ-idl c))
    ∙ sym (*ℚ-distribr c 1 (nℚ K))
    ∙ ap (_*ℚ c) (sym (nℚ-suc' K))
```
-->

```agda
sum-pair
  : ∀ K (t : Nat → ℝ)
  → sumᴿ (K + K) t ≡ sumᴿ K (λ i → t (i + i) +ᴿ t (suc (i + i)))
sum-pair zero    t = refl
sum-pair (suc K) t =
    ap (λ m → sumᴿ m t) (dbl-suc K)
  ∙ ap (λ z → (z +ᴿ t (K + K)) +ᴿ t (suc (K + K))) (sum-pair K t)
  ∙ RI.reassoc-r (sumᴿ K G) (t (K + K)) (t (suc (K + K)))
  where G = λ i → t (i + i) +ᴿ t (suc (i + i))

sumᴿ-neg : ∀ K (s : Nat → ℝ) → (-ᴿ sumᴿ K s) ≡ sumᴿ K (λ i → -ᴿ s i)
sumᴿ-neg zero    s = neg0
sumᴿ-neg (suc K) s =
    RI.neg-sum (sumᴿ K s) (s K)
  ∙ ap (_+ᴿ (-ᴿ s K)) (sumᴿ-neg K s)

sumᴿ-sub
  : ∀ K (s u : Nat → ℝ)
  → (sumᴿ K s +ᴿ (-ᴿ sumᴿ K u)) ≡ sumᴿ K (λ i → s i +ᴿ (-ᴿ u i))
sumᴿ-sub K s u =
    ap (sumᴿ K s +ᴿ_) (sumᴿ-neg K u)
  ∙ sym (sumᴿ-add K s (λ i → -ᴿ u i))

sumᴿ-bounded
  : ∀ K c (s : Nat → ℝ)
  → (∀ i → i Nat.< K → absᴿ (s i) ≤ᴿ ratℝ c)
  → absᴿ (sumᴿ K s) ≤ᴿ ratℝ (nℚ K *ℚ c)
sumᴿ-bounded zero    c s hyp =
  subst (λ z → absᴿ (sumᴿ 0 s) ≤ᴿ ratℝ z) (sym (*ℚ-zerol c))
    (subst (_≤ᴿ ratℝ 0) (sym abs0) (≤ᴿ-refl {ratℝ 0}))
sumᴿ-bounded (suc K) c s hyp =
  ≤ᴿ-trans {absᴿ (sumᴿ K s +ᴿ s K)}
    {absᴿ (sumᴿ K s) +ᴿ absᴿ (s K)} {ratℝ (nℚ (suc K) *ℚ c)}
    (abs-sum {sumᴿ K s} {s K} {absᴿ (sumᴿ K s)} {absᴿ (s K)}
      (≤ᴿ-refl {absᴿ (sumᴿ K s)}) (≤ᴿ-refl {absᴿ (s K)}))
    (≤ᴿ-trans {absᴿ (sumᴿ K s) +ᴿ absᴿ (s K)}
      {ratℝ (nℚ K *ℚ c) +ᴿ ratℝ c} {ratℝ (nℚ (suc K) *ℚ c)}
      (+ᴿ-mono {absᴿ (sumᴿ K s)} {ratℝ (nℚ K *ℚ c)} {absᴿ (s K)} {ratℝ c}
        (sumᴿ-bounded K c s (λ i i<K → hyp i (Nat.≤-sucr i<K)))
        (hyp K Nat.≤-refl))
      (subst ((ratℝ (nℚ K *ℚ c) +ᴿ ratℝ c) ≤ᴿ_) ratℝ-eq
        (≤ᴿ-refl {ratℝ (nℚ K *ℚ c) +ᴿ ratℝ c})))
  where
  ratℝ-eq : (ratℝ (nℚ K *ℚ c) +ᴿ ratℝ c) ≡ ratℝ (nℚ (suc K) *ℚ c)
  ratℝ-eq = sym (ratℝ-+ (nℚ K *ℚ c) c) ∙ ap ratℝ (nsuc-mul K c)
```

## The dyadic refinement

Bisecting the $2^{n}$-partition makes the $(n+1)$-partition an *exact*
refinement: the even node $2i$ of level $n+1$ is the node $i$ of level
$n$, and the odd node $2i+1$ is that node shifted by the finer mesh.
The heart is the additivity of $\nQ$ across doubling, which halves the
mesh factor.

<!--
```agda
private
  node-inner
    : ∀ a b n i → (nℚ (i + i) *ℚ msh a b (suc n)) ≡ (nℚ i *ℚ msh a b n)
  node-inner a b n i =
      ap (_*ℚ msh a b (suc n)) (nℚ-add i i)
    ∙ *ℚ-distribr (msh a b (suc n)) (nℚ i) (nℚ i)
    ∙ sym (*ℚ-distribl (nℚ i) (msh a b (suc n)) (msh a b (suc n)))
    ∙ ap (nℚ i *ℚ_) (half-sum (msh a b n))
```
-->

```agda
node-even : ∀ a b n i → dyadic a b (suc n) (i + i) ≡ dyadic a b n i
node-even a b n i = ap (a +ℚ_) (node-inner a b n i)

node-odd
  : ∀ a b n i
  → dyadic a b (suc n) (suc (i + i)) ≡ (dyadic a b n i +ℚ msh a b (suc n))
node-odd a b n i =
    ap (λ z → a +ℚ (z *ℚ msh a b (suc n))) (nℚ-suc' (i + i))
  ∙ ap (a +ℚ_) (*ℚ-distribr (msh a b (suc n)) 1 (nℚ (i + i)))
  ∙ ap (λ z → a +ℚ (z +ℚ (nℚ (i + i) *ℚ msh a b (suc n))))
      (*ℚ-idl (msh a b (suc n)))
  ∙ ap (λ z → a +ℚ (msh a b (suc n) +ℚ z)) (node-inner a b n i)
  ∙ reassoc a (msh a b (suc n)) (nℚ i *ℚ msh a b n)
  where
  reassoc : ∀ A H M → (A +ℚ (H +ℚ M)) ≡ ((A +ℚ M) +ℚ H)
  reassoc A H M = rational!
```

The total mesh telescopes exactly: $2^{n}$ pieces of width $h_{n}$ span
$b - a$.

```agda
pow-msh : ∀ a b n → (nℚ (pow2 n) *ℚ msh a b n) ≡ (b +ℚ (-ℚ a))
pow-msh a b zero    = ap (_*ℚ msh a b zero) nℚ-one ∙ *ℚ-idl (msh a b zero)
pow-msh a b (suc n) =
    ap (_*ℚ msh a b (suc n)) (nℚ-add (pow2 n) (pow2 n))
  ∙ *ℚ-distribr (msh a b (suc n)) (nℚ (pow2 n)) (nℚ (pow2 n))
  ∙ sym (*ℚ-distribl (nℚ (pow2 n)) (msh a b (suc n)) (msh a b (suc n)))
  ∙ ap (nℚ (pow2 n) *ℚ_) (half-sum (msh a b n))
  ∙ pow-msh a b n
```

## Absolute values of rational embeddings

A two-sided rational bracket on a rational lifts to a bound on the
absolute value of its real embedding — the only interface through
which the estimate below touches `absᴿ`{.Agda} of a rational.

```agda
private
  abs-ratℝ-≤ : ∀ {r s} → (-ℚ s) ≤ r → r ≤ s → absᴿ (ratℝ r) ≤ᴿ ratℝ s
  abs-ratℝ-≤ {r} {s} -s≤r r≤s = abs-≤ {ratℝ r} {ratℝ s}
    (ratℝ-mono r≤s)
    (subst (_≤ᴿ ratℝ r) (sym (ratℝ-neg s)) (ratℝ-mono -s≤r))

  neg≤self : ∀ {x} → 0 ≤ x → (-ℚ x) ≤ x
  neg≤self {x} 0≤x = ≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ 0≤x)) 0≤x
```

## Reciprocals of powers of two

The reciprocal geometry the telescope runs on: cancellation of a
nonzero factor, the doubling of $\nQ(2^{n})$, the halving law
$(1/2)^{n} = (1/2)^{n+1} + (1/2)^{n+1}$, antitonicity, and the two
`invℚ`{.Agda}-cancellations that convert a mesh and a squared mesh
into powers of one half.

```agda
private
  mul-cancelr : ∀ {a b} w ⦃ nz : Nonzero w ⦄ → (a *ℚ w) ≡ (b *ℚ w) → a ≡ b
  mul-cancelr {a} {b} w ⦃ nz ⦄ e =
      sym (*ℚ-idr a)
    ∙ ap (a *ℚ_) (sym (*ℚ-invr {w} {nz}))
    ∙ *ℚ-associative a w (invℚ w ⦃ nz ⦄)
    ∙ ap (_*ℚ invℚ w ⦃ nz ⦄) e
    ∙ sym (*ℚ-associative b w (invℚ w ⦃ nz ⦄))
    ∙ ap (b *ℚ_) (*ℚ-invr {w} {nz})
    ∙ *ℚ-idr b

  nℚ-double : ∀ n → nℚ (pow2 (suc n)) ≡ nℚ (pow2 n) *ℚ 2
  nℚ-double n = nℚ-add (pow2 n) (pow2 n) ∙ x+x≡x*2 (nℚ (pow2 n))

  0≤tpi : ∀ k → 0 ≤ two-pow-inv k
  0≤tpi k = <-weaken (invℚ-pos {nℚ (pow2 k)} ⦃ nz-pow2 k ⦄ (0<nℚ-pow2 k))

  oneone : (1 +ℚ 1) ≡ 2
  oneone = x+x≡x*2 1 ∙ *ℚ-idl 2

  geom : ∀ n → two-pow-inv n ≡ (two-pow-inv (suc n) +ℚ two-pow-inv (suc n))
  geom n = mul-cancelr (nℚ (pow2 (suc n))) ⦃ nz-pow2 (suc n) ⦄ (lhs ∙ sym rhs)
    where
    lhs : two-pow-inv n *ℚ nℚ (pow2 (suc n)) ≡ 2
    lhs =
        ap (two-pow-inv n *ℚ_) (nℚ-double n)
      ∙ *ℚ-associative (two-pow-inv n) (nℚ (pow2 n)) 2
      ∙ ap (_*ℚ 2) (*ℚ-invl {nℚ (pow2 n)} ⦃ nz-pow2 n ⦄)
      ∙ *ℚ-idl 2

    rhs : (two-pow-inv (suc n) +ℚ two-pow-inv (suc n)) *ℚ nℚ (pow2 (suc n)) ≡ 2
    rhs =
        *ℚ-distribr (nℚ (pow2 (suc n))) (two-pow-inv (suc n)) (two-pow-inv (suc n))
      ∙ ap₂ _+ℚ_
          (*ℚ-invl {nℚ (pow2 (suc n))} ⦃ nz-pow2 (suc n) ⦄)
          (*ℚ-invl {nℚ (pow2 (suc n))} ⦃ nz-pow2 (suc n) ⦄)
      ∙ oneone

  tpi-anti : ∀ n → two-pow-inv (suc n) ≤ two-pow-inv n
  tpi-anti n = <-weaken (invℚ-anti-< {nℚ (pow2 n)} {nℚ (pow2 (suc n))}
    ⦃ nz-pow2 n ⦄ ⦃ nz-pow2 (suc n) ⦄ (0<nℚ-pow2 n) pow2<)
    where
    pow2< : nℚ (pow2 n) < nℚ (pow2 (suc n))
    pow2< = <-resp refl (sym (nℚ-add (pow2 n) (pow2 n)))
      (add-pos-< (nℚ (pow2 n)) (nℚ (pow2 n)) (0<nℚ-pow2 n))

  msh-tpi : ∀ a b n → msh a b n ≡ ((b +ℚ (-ℚ a)) *ℚ two-pow-inv n)
  msh-tpi a b n =
      sym (*ℚ-idl (msh a b n))
    ∙ ap (_*ℚ msh a b n) (sym (*ℚ-invl {nℚ (pow2 n)} ⦃ nz-pow2 n ⦄))
    ∙ sym (*ℚ-associative (two-pow-inv n) (nℚ (pow2 n)) (msh a b n))
    ∙ ap (two-pow-inv n *ℚ_) (pow-msh a b n)
    ∙ *ℚ-commutative (two-pow-inv n) (b +ℚ (-ℚ a))

  collect1
    : ∀ a s P → (a *ℚ (s *ℚ s)) *ℚ (P *ℚ 2) ≡ (s *ℚ P) *ℚ (a *ℚ (s *ℚ 2))
  collect1 a s P = rational!

  collect2 : ∀ a s → a *ℚ (s *ℚ 2) ≡ s *ℚ (a *ℚ 2)
  collect2 a s = rational!

  pow-tpi
    : ∀ n
    → nℚ (pow2 n) *ℚ (two-pow-inv (suc n) *ℚ two-pow-inv (suc n))
    ≡ two-pow-inv (suc (suc n))
  pow-tpi n = mul-cancelr (nℚ (pow2 (suc (suc n)))) ⦃ nz-pow2 (suc (suc n)) ⦄
    (lhsw ∙ sym rhsw)
    where
    s = two-pow-inv (suc n)
    lhsw
      : (nℚ (pow2 n) *ℚ (s *ℚ s)) *ℚ nℚ (pow2 (suc (suc n))) ≡ 1
    lhsw =
        ap ((nℚ (pow2 n) *ℚ (s *ℚ s)) *ℚ_) (nℚ-double (suc n))
      ∙ collect1 (nℚ (pow2 n)) s (nℚ (pow2 (suc n)))
      ∙ ap (_*ℚ (nℚ (pow2 n) *ℚ (s *ℚ 2)))
          (*ℚ-invl {nℚ (pow2 (suc n))} ⦃ nz-pow2 (suc n) ⦄)
      ∙ *ℚ-idl (nℚ (pow2 n) *ℚ (s *ℚ 2))
      ∙ collect2 (nℚ (pow2 n)) s
      ∙ ap (s *ℚ_) (sym (nℚ-double n))
      ∙ *ℚ-invl {nℚ (pow2 (suc n))} ⦃ nz-pow2 (suc n) ⦄

    rhsw : two-pow-inv (suc (suc n)) *ℚ nℚ (pow2 (suc (suc n))) ≡ 1
    rhsw = *ℚ-invl {nℚ (pow2 (suc (suc n)))} ⦃ nz-pow2 (suc (suc n)) ⦄
```

## The Lipschitz interface

The single analytic hypothesis the estimate consumes, packaged as
**data**: a rational Lipschitz modulus $M$ on the box $[-R, R]$ with
$R = \max(b, -a)$, valid for the finitely-many rational tags that the
dyadic partition visits. A two-sided rational bracket on $p - q$
witnesses the argument separation, so no `absℚ`{.Agda} is ever needed.

```agda
boxR : Ratio → Ratio → Ratio
boxR a b = maxℚ b (-ℚ a)

record LipBound (f : Fun 1) (a b : Ratio) : Type where
  no-eta-equality
  field
    M   : Ratio
    0≤M : 0 ≤ M
    lip : (p q d : Ratio)
        → (p +ℚ (-ℚ q)) ≤ d → (-ℚ d) ≤ (p +ℚ (-ℚ q))
        → absᴿ (ratℝ p) ≤ᴿ ratℝ (boxR a b)
        → absᴿ (ratℝ q) ≤ᴿ ratℝ (boxR a b)
        → absᴿ (f (pt p) +ᴿ (-ᴿ f (pt q))) ≤ᴿ ratℝ (M *ℚ d)
```

Every bounded-smooth function *merely* carries such a witness: its
depth-one Hadamard quotient `A .fst 1 fzero .fst`{.Agda} is a function
of two variables, bounded on the box by `Bd`{.Agda}, and the quotient
equation turns the difference $f(p) - f(q)$ into $(p - q)$ times that
quotient evaluated on a point of the box.

```agda
private
  set-pt
    : ∀ (p q : Ratio)
    → set (pt p) fzero (ratℝ q) ≡ pt q
  set-pt p q = funext go where
    go : (j : Fin 1) → set (pt p) fzero (ratℝ q) j ≡ pt q j
    go j with Discrete-Fin .decide fzero j
    ... | yes _  = refl
    ... | no ¬e  = absurd (¬e (Fin-cases {P = λ k → fzero ≡ k}
      refl (λ i → absurd (Fin-absurd i)) j))

Smooth⁺→LipBound
  : (f : Fun 1) (a b : Ratio) → Smooth⁺ 1 f → ∥ LipBound f a b ∥
Smooth⁺→LipBound f a b A = ∥-∥-map mk-lip (Bd2 R)
  where
  g : Fun 2
  g = A .fst 1 fzero .fst

  qeq : Quot 1 f fzero g
  qeq = A .fst 1 fzero .snd .fst

  Bd2 : Bd 2 g
  Bd2 = A .snd .snd 1 fzero .fst

  R : Ratio
  R = boxR a b

  mk-lip
    : Σ Ratio (λ M' → (y : Fin 2 → ℝ) → InBox 2 R y → absᴿ (g y) ≤ᴿ ratℝ M')
    → LipBound f a b
  mk-lip (M' , gbd) = record { M = maxℚ M' 0 ; 0≤M = maxℚ-≤r {M'} {0} ; lip = liplemma }
    where
    liplemma
      : (p q d : Ratio)
      → (p +ℚ (-ℚ q)) ≤ d → (-ℚ d) ≤ (p +ℚ (-ℚ q))
      → absᴿ (ratℝ p) ≤ᴿ ratℝ R → absᴿ (ratℝ q) ≤ᴿ ratℝ R
      → absᴿ (f (pt p) +ᴿ (-ᴿ f (pt q))) ≤ᴿ ratℝ (maxℚ M' 0 *ℚ d)
    liplemma p q d pq≤d -d≤pq |p|≤R |q|≤R =
      subst (λ z → absᴿ z ≤ᴿ ratℝ (maxℚ M' 0 *ℚ d)) (sym qeq-inst)
        (≤ᴿ-trans {absᴿ (X *ᴿ Y)} {ratℝ d *ᴿ ratℝ (maxℚ M' 0)}
          {ratℝ (maxℚ M' 0 *ℚ d)}
          (abs-prod {X} {Y} {ratℝ d} {ratℝ (maxℚ M' 0)} Xbound Ybound)
          (subst (λ w → (ratℝ d *ᴿ ratℝ (maxℚ M' 0)) ≤ᴿ w)
            (ap ratℝ (*ℚ-commutative d (maxℚ M' 0)))
            (ratℝ-*-≤ d (maxℚ M' 0))))
      where
      X : ℝ
      X = ratℝ p +ᴿ (-ᴿ ratℝ q)

      Y : ℝ
      Y = g (cons (ratℝ q) (pt p))

      qeq-inst
        : f (pt p) +ᴿ (-ᴿ f (pt q)) ≡ X *ᴿ Y
      qeq-inst =
          sym (ap (λ w → f (pt p) +ᴿ (-ᴿ f w)) (set-pt p q))
        ∙ qeq (pt p) (ratℝ q)

      pq-path : X ≡ ratℝ (p +ℚ (-ℚ q))
      pq-path = ap (ratℝ p +ᴿ_) (ratℝ-neg q) ∙ sym (ratℝ-+ p (-ℚ q))

      Xbound : absᴿ X ≤ᴿ ratℝ d
      Xbound = subst (λ z → absᴿ z ≤ᴿ ratℝ d) (sym pq-path)
        (abs-ratℝ-≤ {p +ℚ (-ℚ q)} {d} -d≤pq pq≤d)

      inbox : InBox 2 R (cons (ratℝ q) (pt p))
      inbox = Fin-cases |q|≤R (λ _ → |p|≤R)

      Ybound : absᴿ Y ≤ᴿ ratℝ (maxℚ M' 0)
      Ybound = ≤ᴿ-trans {absᴿ Y} {ratℝ M'} {ratℝ (maxℚ M' 0)}
        (gbd (cons (ratℝ q) (pt p)) inbox)
        (ratℝ-mono (maxℚ-≤l {M'} {0}))
```

## A triangle estimate over a rational budget

The one packaging the telescope repeats: two consecutive differences,
each within a rational bound, compose to a difference within the sum
of the bounds.

```agda
private
  sub-self : ∀ x h → (x +ℚ (-ℚ (x +ℚ h))) ≡ (-ℚ h)
  sub-self x h = rational!

  merge3
    : ∀ {I S T : ℝ} {β γ : Ratio}
    → absᴿ (I +ᴿ (-ᴿ S)) ≤ᴿ ratℝ β
    → absᴿ (S +ᴿ (-ᴿ T)) ≤ᴿ ratℝ γ
    → absᴿ (I +ᴿ (-ᴿ T)) ≤ᴿ ratℝ (β +ℚ γ)
  merge3 {I} {S} {T} {β} {γ} hIS hST =
    subst (λ z → absᴿ z ≤ᴿ ratℝ (β +ℚ γ)) (sym (RI.tele3 I S T))
      (subst (λ w → absᴿ ((I +ᴿ (-ᴿ S)) +ᴿ (S +ᴿ (-ᴿ T))) ≤ᴿ w) (sym (ratℝ-+ β γ))
        (abs-sum {I +ᴿ (-ᴿ S)} {S +ᴿ (-ᴿ T)} {ratℝ β} {ratℝ γ} hIS hST))
```

# The dyadic Cauchy estimate {defines="riemann-cauchy"}

Fix a Lipschitz-witnessed integrand on $[a, b]$ with $a \le b$. The
per-step estimate, its telescope, and the resulting `lim`{.Agda} are
assembled in one parametrised module. Write $M$ for the Lipschitz
modulus, $\Delta = b - a$ for the interval width, $R = \max(b, -a)$ for
the box radius, and $D = M\,\Delta^{2}$ for the geometric constant.

```agda
module _ (f : Fun 1) (a b : Ratio) (L : LipBound f a b) (a≤b : a ≤ b) where
  open LipBound L

  private
    Δ : Ratio
    Δ = b +ℚ (-ℚ a)

    R : Ratio
    R = boxR a b

    D : Ratio
    D = M *ℚ (Δ *ℚ Δ)

    0≤half : ∀ {x} → 0 ≤ x → 0 ≤ half x
    0≤half {x} 0≤x = ≤-resp (*ℚ-zerol (invℚ 2)) refl
      (*ℚ-preserves-≤r (invℚ 2) 0≤x (<-weaken (invℚ-pos {2} 0<2)))
      where
      0<2 : 0 < 2
      0<2 = decide!

    msh-nn : ∀ n → 0 ≤ msh a b n
    msh-nn zero    = ≤-resp (+ℚ-invr a) refl (+ℚ-preserves-≤ a≤b (≤-refl { -ℚ a}))
    msh-nn (suc n) = 0≤half (msh-nn n)

    0≤Δ : 0 ≤ Δ
    0≤Δ = msh-nn zero

    0≤D : 0 ≤ D
    0≤D = *ℚ-nonnegative 0≤M (*ℚ-nonnegative 0≤Δ 0≤Δ)
```

## Nodes stay in the box

Every dyadic node lies in $[a, b]$, hence in $[-R, R]$; the odd node of
level $n+1$ is the node $i$ of level $n$ shifted by the finer mesh, so
it too lies in the box (via its level-$(n+1)$ index $2i+1 < 2^{n+1}$).

```agda
  private
    node-hi : ∀ n i → i Nat.< pow2 n → dyadic a b n i ≤ R
    node-hi n i i<pn = ≤-trans dyadic≤b (maxℚ-≤l {b} { -ℚ a})
      where
      prod≤ : (nℚ i *ℚ msh a b n) ≤ Δ
      prod≤ = ≤-resp refl (pow-msh a b n)
        (*ℚ-preserves-≤r (msh a b n) (nℚ-mono (Nat.<-weaken i<pn)) (msh-nn n))

      dyadic≤b : dyadic a b n i ≤ b
      dyadic≤b = ≤-resp refl adia (+ℚ-preserves-≤ (≤-refl {a}) prod≤)
        where
        adia : a +ℚ Δ ≡ b
        adia = rational!

    node-lo : ∀ n i → i Nat.< pow2 n → (-ℚ R) ≤ dyadic a b n i
    node-lo n i i<pn = ≤-trans -R≤a a≤dyadic
      where
      -R≤a : (-ℚ R) ≤ a
      -R≤a = ≤-resp refl (negℚ-invol a) (negℚ-anti-≤ (maxℚ-≤r {b} { -ℚ a}))

      a≤dyadic : a ≤ dyadic a b n i
      a≤dyadic = ≤-resp (+ℚ-idr a) refl
        (+ℚ-preserves-≤ (≤-refl {a}) (*ℚ-nonnegative (nℚ-nonneg' i) (msh-nn n)))

    odd< : ∀ n i → i Nat.< pow2 n → suc (i + i) Nat.< pow2 (suc n)
    odd< n i i<pn = subst (Nat._≤ (pow2 n + pow2 n)) (dbl-suc i)
      (Nat.+-preserves-≤ (suc i) (pow2 n) (suc i) (pow2 n) i<pn i<pn)
```

## The per-step estimate

Refining the partition changes each Riemann sum by a controlled
amount. Regrouping the finer sum even/odd, the even half cancels the
coarse term and the odd half becomes the Lipschitz-bounded difference
across one fine mesh; summing $2^{n}$ such blocks gives the raw
per-step bound.

```agda
  private
    step-bound
      : ∀ n
      → absᴿ (Riemann f a b n +ᴿ (-ᴿ Riemann f a b (suc n)))
        ≤ᴿ ratℝ (nℚ (pow2 n) *ℚ (M *ℚ (msh a b (suc n) *ℚ msh a b (suc n))))
    step-bound n =
      subst (λ z → absᴿ z ≤ᴿ ratℝ (nℚ (pow2 n) *ℚ (M *ℚ (h1 *ℚ h1))))
        (sym Riemann-eq)
        (sumᴿ-bounded (pow2 n) (M *ℚ (h1 *ℚ h1)) block blockbd)
      where
      h1 : Ratio
      h1 = msh a b (suc n)

      Sn : Nat → ℝ
      Sn i = ratℝ (msh a b n) *ᴿ f (pt (dyadic a b n i))

      Tn : Nat → ℝ
      Tn j = ratℝ h1 *ᴿ f (pt (dyadic a b (suc n) j))

      U : Nat → ℝ
      U i = Tn (i + i) +ᴿ Tn (suc (i + i))

      block : Nat → ℝ
      block i =
        ratℝ h1 *ᴿ (f (pt (dyadic a b n i)) +ᴿ (-ᴿ f (pt (dyadic a b n i +ℚ h1))))

      msh-ratℝ : ratℝ (msh a b n) ≡ (ratℝ h1 +ᴿ ratℝ h1)
      msh-ratℝ = ap ratℝ (sym (half-sum (msh a b n))) ∙ ratℝ-+ h1 h1

      blockeq : ∀ i → Sn i +ᴿ (-ᴿ U i) ≡ block i
      blockeq i =
          ap₂ (λ s u → s +ᴿ (-ᴿ u)) Sdist (ap₂ _+ᴿ_ Teven Todd)
        ∙ RI.even-cancel (ratℝ h1 *ᴿ fXi) (ratℝ h1 *ᴿ fXih)
        ∙ sym (RI.mul-sub (ratℝ h1) fXih fXi)
        where
        fXi : ℝ
        fXi = f (pt (dyadic a b n i))
        fXih : ℝ
        fXih = f (pt (dyadic a b n i +ℚ h1))
        Sdist : Sn i ≡ (ratℝ h1 *ᴿ fXi) +ᴿ (ratℝ h1 *ᴿ fXi)
        Sdist = ap (_*ᴿ fXi) msh-ratℝ ∙ *ᴿ-distribʳ fXi (ratℝ h1) (ratℝ h1)
        Teven : Tn (i + i) ≡ ratℝ h1 *ᴿ fXi
        Teven = ap (λ z → ratℝ h1 *ᴿ f (pt z)) (node-even a b n i)
        Todd : Tn (suc (i + i)) ≡ ratℝ h1 *ᴿ fXih
        Todd = ap (λ z → ratℝ h1 *ᴿ f (pt z)) (node-odd a b n i)

      Riemann-eq
        : Riemann f a b n +ᴿ (-ᴿ Riemann f a b (suc n)) ≡ sumᴿ (pow2 n) block
      Riemann-eq =
          ap (λ z → Riemann f a b n +ᴿ (-ᴿ z)) (sum-pair (pow2 n) Tn)
        ∙ sumᴿ-sub (pow2 n) Sn U
        ∙ ap (sumᴿ (pow2 n)) (funext blockeq)

      blockbd
        : ∀ i → i Nat.< pow2 n → absᴿ (block i) ≤ᴿ ratℝ (M *ℚ (h1 *ℚ h1))
      blockbd i i<pn =
        ≤ᴿ-trans {absᴿ (block i)} {ratℝ h1 *ᴿ ratℝ (M *ℚ h1)}
          {ratℝ (M *ℚ (h1 *ℚ h1))}
          (abs-prod {ratℝ h1} {fXi +ᴿ (-ᴿ fXih)} {ratℝ h1} {ratℝ (M *ℚ h1)}
            h1-bound lip-bound)
          (subst (λ w → (ratℝ h1 *ᴿ ratℝ (M *ℚ h1)) ≤ᴿ w)
            (ap ratℝ h1-comm) (ratℝ-*-≤ h1 (M *ℚ h1)))
        where
        fXi : ℝ
        fXi = f (pt (dyadic a b n i))
        fXih : ℝ
        fXih = f (pt (dyadic a b n i +ℚ h1))

        0≤h1 : 0 ≤ h1
        0≤h1 = msh-nn (suc n)

        h1-bound : absᴿ (ratℝ h1) ≤ᴿ ratℝ h1
        h1-bound = abs-ratℝ-≤ {h1} {h1} (neg≤self 0≤h1) (≤-refl {h1})

        pq-id : (dyadic a b n i +ℚ (-ℚ (dyadic a b n i +ℚ h1))) ≡ (-ℚ h1)
        pq-id = sub-self (dyadic a b n i) h1

        |p|≤R : absᴿ (ratℝ (dyadic a b n i)) ≤ᴿ ratℝ R
        |p|≤R = abs-ratℝ-≤ {dyadic a b n i} {R} (node-lo n i i<pn) (node-hi n i i<pn)

        |q|≤R : absᴿ (ratℝ (dyadic a b n i +ℚ h1)) ≤ᴿ ratℝ R
        |q|≤R = abs-ratℝ-≤ {dyadic a b n i +ℚ h1} {R} q-lo q-hi
          where
          q-lo : (-ℚ R) ≤ (dyadic a b n i +ℚ h1)
          q-lo = subst ((-ℚ R) ≤_) (node-odd a b n i)
            (node-lo (suc n) (suc (i + i)) (odd< n i i<pn))
          q-hi : (dyadic a b n i +ℚ h1) ≤ R
          q-hi = subst (_≤ R) (node-odd a b n i)
            (node-hi (suc n) (suc (i + i)) (odd< n i i<pn))

        lip-bound : absᴿ (fXi +ᴿ (-ᴿ fXih)) ≤ᴿ ratℝ (M *ℚ h1)
        lip-bound = lip (dyadic a b n i) (dyadic a b n i +ℚ h1) h1
          (subst (_≤ h1) (sym pq-id) (neg≤self 0≤h1))
          (subst ((-ℚ h1) ≤_) (sym pq-id) (≤-refl { -ℚ h1}))
          |p|≤R |q|≤R

        h1-comm : h1 *ℚ (M *ℚ h1) ≡ M *ℚ (h1 *ℚ h1)
        h1-comm = rational!
```

## The clean geometric step

The raw per-step bound is exactly $D\,(1/2)^{n+2}$: rewriting the mesh
as $\Delta\,(1/2)^{n+1}$ and folding two reciprocals of $2^{n+1}$ into
one of $2^{n+2}$ turns it into a pure geometric term.

```agda
  private
    closed
      : ∀ n
      → nℚ (pow2 n) *ℚ (M *ℚ (msh a b (suc n) *ℚ msh a b (suc n)))
        ≡ D *ℚ two-pow-inv (suc (suc n))
    closed n =
        ap (λ z → nℚ (pow2 n) *ℚ (M *ℚ (z *ℚ z))) (msh-tpi a b (suc n))
      ∙ ap (nℚ (pow2 n) *ℚ_) (rearrM M Δ (two-pow-inv (suc n)))
      ∙ rearrN (nℚ (pow2 n)) D (two-pow-inv (suc n) *ℚ two-pow-inv (suc n))
      ∙ ap (D *ℚ_) (pow-tpi n)
      where
      rearrM
        : ∀ M' Δ' s → M' *ℚ ((Δ' *ℚ s) *ℚ (Δ' *ℚ s)) ≡ (M' *ℚ (Δ' *ℚ Δ')) *ℚ (s *ℚ s)
      rearrM M' Δ' s = rational!
      rearrN : ∀ X D' Y → X *ℚ (D' *ℚ Y) ≡ D' *ℚ (X *ℚ Y)
      rearrN X D' Y = rational!

    step-clean
      : ∀ n
      → absᴿ (Riemann f a b n +ᴿ (-ᴿ Riemann f a b (suc n)))
        ≤ᴿ ratℝ (D *ℚ two-pow-inv (suc (suc n)))
    step-clean n = subst
      (λ z → absᴿ (Riemann f a b n +ᴿ (-ᴿ Riemann f a b (suc n))) ≤ᴿ ratℝ z)
      (closed n) (step-bound n)
```

## Telescoping to a Cauchy sequence

Summing the geometric steps: with the invariant
$\lvert R_{m} - R_{n}\rvert \le D\,((1/2)^{m+1} - (1/2)^{n+1})$, each
added step closes exactly because $(1/2)^{n+1} = 2\cdot(1/2)^{n+2}$.
Dropping the nonnegative subtrahend and using $(1/2)^{m+1} \le
(1/2)^{m}$ gives the clean Cauchy bound $D\,(1/2)^{m}$.

```agda
  private
    cauchy-gap
      : ∀ k m
      → absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b (k + m)))
        ≤ᴿ ratℝ (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (k + m)))))
    cauchy-gap zero m = subst₂ _≤ᴿ_ (sym lhs0) (sym rhs0) (≤ᴿ-refl {0ᴿ})
      where
      lhs0 : absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b m)) ≡ 0ᴿ
      lhs0 = ap absᴿ (+ᴿ-invr (Riemann f a b m)) ∙ abs0
      rhs0 : ratℝ (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc m)))) ≡ 0ᴿ
      rhs0 = ap ratℝ (ap (D *ℚ_) (+ℚ-invr (two-pow-inv (suc m))) ∙ *ℚ-zeror D)
    cauchy-gap (suc k) m =
      subst
        (λ z → absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b (suc (k + m)))) ≤ᴿ ratℝ z)
        combine-eq
        (merge3 {Riemann f a b m} {Riemann f a b (k + m)} {Riemann f a b (suc (k + m))}
          {D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (k + m))))}
          {D *ℚ two-pow-inv (suc (suc (k + m)))}
          (cauchy-gap k m) (step-clean (k + m)))
      where
      combine-eq
        : (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (k + m)))))
          +ℚ (D *ℚ two-pow-inv (suc (suc (k + m))))
        ≡ D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (suc (k + m)))))
      combine-eq =
          ap (λ z →
                (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ z)))
                +ℚ (D *ℚ two-pow-inv (suc (suc (k + m)))))
            (geom (suc (k + m)))
        ∙ ringid D (two-pow-inv (suc m)) (two-pow-inv (suc (suc (k + m))))
        where
        ringid
          : ∀ D' A C → (D' *ℚ (A +ℚ (-ℚ (C +ℚ C)))) +ℚ (D' *ℚ C) ≡ D' *ℚ (A +ℚ (-ℚ C))
        ringid D' A C = rational!

    cauchy-bound
      : ∀ m n → m Nat.≤ n
      → absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b n))
        ≤ᴿ ratℝ (D *ℚ two-pow-inv m)
    cauchy-bound m n m≤n =
      subst
        (λ z → absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b z)) ≤ᴿ ratℝ (D *ℚ two-pow-inv m))
        e'
        (≤ᴿ-trans {absᴿ (Riemann f a b m +ᴿ (-ᴿ Riemann f a b (k + m)))}
          {ratℝ (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (k + m)))))}
          {ratℝ (D *ℚ two-pow-inv m)}
          (cauchy-gap k m) (ratℝ-mono shrink))
      where
      k : Nat
      k = (≤→+ m≤n) .fst

      e' : k + m ≡ n
      e' = sym (Nat.+-commutative m k) ∙ (≤→+ m≤n) .snd

      sub-nonneg : ∀ x y → 0 ≤ y → (x +ℚ (-ℚ y)) ≤ x
      sub-nonneg x y 0≤y = ≤-resp refl (+ℚ-idr x)
        (+ℚ-preserves-≤ (≤-refl {x}) (≤-resp refl neg-zero (negℚ-anti-≤ 0≤y)))

      shrink
        : (D *ℚ (two-pow-inv (suc m) +ℚ (-ℚ two-pow-inv (suc (k + m)))))
          ≤ (D *ℚ two-pow-inv m)
      shrink = *ℚ-preserves-≤l D 0≤D
        (≤-trans
          (sub-nonneg (two-pow-inv (suc m)) (two-pow-inv (suc (k + m)))
            (0≤tpi (suc (k + m))))
          (tpi-anti m))
```

## The limit

Sampling $\mathrm{Riemann}\,f\,a\,b$ at the Archimedean index
`pow2-mod D`{.Agda} packages it as a `CauchyApprox`{.Agda}; its
`lim`{.Agda} is the integral, and combining the limit modulus with the
Cauchy bound shows it is the Riemann limit of $f$.

```agda
  capprox : CauchyApprox
  capprox .fst ε p = Riemann f a b (pow2-mod D ε p)
  capprox .snd ε δ p r with holds? (pow2-mod D ε p Nat.≤ pow2-mod D δ r)
  ... | yes le =
    ≤ᴿ-trans {absᴿ (Riemann f a b Nε +ᴿ (-ᴿ Riemann f a b Nδ))}
      {ratℝ (D *ℚ two-pow-inv Nε)} {ratℝ (ε +ℚ δ)}
      (cauchy-bound Nε Nδ le)
      (ratℝ-mono (≤-trans (mod-spec D ε p 0≤D) (<-weaken (add-pos-< ε δ r))))
    where
    Nε = pow2-mod D ε p
    Nδ = pow2-mod D δ r
  ... | no ¬le =
    subst (λ z → absᴿ z ≤ᴿ ratℝ (ε +ℚ δ))
      (RI.neg-sub (Riemann f a b Nδ) (Riemann f a b Nε))
      (abs-neg {Riemann f a b Nδ +ᴿ (-ᴿ Riemann f a b Nε)} {ratℝ (ε +ℚ δ)}
        (≤ᴿ-trans {absᴿ (Riemann f a b Nδ +ᴿ (-ᴿ Riemann f a b Nε))}
          {ratℝ (D *ℚ two-pow-inv Nδ)} {ratℝ (ε +ℚ δ)}
          (cauchy-bound Nδ Nε (Nat.≤-is-weakly-total Nε Nδ ¬le))
          (ratℝ-mono
            (≤-trans (mod-spec D δ r 0≤D)
              (<-weaken (<-resp refl (+ℚ-commutative δ ε) (add-pos-< δ ε p)))))))
    where
    Nε = pow2-mod D ε p
    Nδ = pow2-mod D δ r

  ∫L : ℝ
  ∫L = lim capprox

  ∫L-converges : is-Rlim f a b ∫L
  ∫L-converges ε 0<ε = inc (Nη , goal)
    where
    η : Ratio
    η = half (half ε)

    0<η : 0 < η
    0<η = half-pos (half-pos 0<ε)

    Nη : Nat
    Nη = pow2-mod D η 0<η

    three-η : (2 *ℚ η +ℚ η) ≤ ε
    three-η = ≤-resp (sym twoη) four-η
      (+ℚ-preserves-≤ (≤-refl {η +ℚ η}) η≤ηη)
      where
      twoη : (2 *ℚ η +ℚ η) ≡ ((η +ℚ η) +ℚ η)
      twoη = ap (_+ℚ η) (*ℚ-commutative 2 η ∙ sym (x+x≡x*2 η))
      four-η : ((η +ℚ η) +ℚ (η +ℚ η)) ≡ ε
      four-η = ap₂ _+ℚ_ (half-sum (half ε)) (half-sum (half ε)) ∙ half-sum ε
      η≤ηη : η ≤ (η +ℚ η)
      η≤ηη = ≤-resp (+ℚ-idr η) refl
        (+ℚ-preserves-≤ (≤-refl {η}) (<-weaken 0<η))

    goal : (n : Nat) → Nη Nat.≤ n → absᴿ (∫L +ᴿ (-ᴿ Riemann f a b n)) ≤ᴿ ratℝ ε
    goal n Nη≤n =
      ≤ᴿ-trans {absᴿ (∫L +ᴿ (-ᴿ Riemann f a b n))}
        {ratℝ (2 *ℚ η +ℚ η)} {ratℝ ε}
        (merge3 {∫L} {Riemann f a b Nη} {Riemann f a b n} {2 *ℚ η} {η}
          modulus-bound cauchy-part)
        (ratℝ-mono three-η)
      where
      modulus-bound : absᴿ (∫L +ᴿ (-ᴿ Riemann f a b Nη)) ≤ᴿ ratℝ (2 *ℚ η)
      modulus-bound = lim-modulus capprox η 0<η

      cauchy-part : absᴿ (Riemann f a b Nη +ᴿ (-ᴿ Riemann f a b n)) ≤ᴿ ratℝ η
      cauchy-part = ≤ᴿ-trans {absᴿ (Riemann f a b Nη +ᴿ (-ᴿ Riemann f a b n))}
        {ratℝ (D *ℚ two-pow-inv Nη)} {ratℝ η}
        (cauchy-bound Nη n Nη≤n)
        (ratℝ-mono (mod-spec D η 0<η 0≤D))
```

## What this discharges, and what stays parametric

For any concrete integrand `f`{.Agda} on an oriented box `a ≤ b`, a
`LipBound f a b`{.Agda} — a **rational** Lipschitz modulus on
$[-R, R]$ — yields `∫L f a b L a≤b`{.Agda}, a genuine real, together
with a proof `∫L-converges`{.Agda} that it *is* the Riemann limit of
`f`{.Agda}. This is the analytic input `Data.Real.Smooth.Integral`{.Agda}
posits as its module parameter, now a **theorem** for every
Lipschitz-witnessed integrand.

Every bounded-smooth function *merely* carries such a witness:
`Smooth⁺→LipBound`{.Agda} extracts one from the depth-one bound data.
The extraction is `∥-∥`-valued because the bound tower records a
rational bound per box only *propositionally*; turning that into a
uniform assignment `(f : Fun 1) → Smooth⁺ 1 f → LipBound f a b`{.Agda}
— which is what `Integration`{.Agda}'s parameter `∫₀`{.Agda} would need,
choice-free and for *every* `Smooth⁺`{.Agda} at once — is exactly a use
of [[countable choice|axiom-of-choice]], and is deliberately not made
here. Two integrands, or one integrand on two boxes, are handled
independently by two applications of `∫L`{.Agda}; only the
*simultaneous* choice of witnesses across the whole function space is
withheld. The estimate itself, and the limit it produces, are entirely
choice-free.

The orientation `a ≤ b` enters through the mesh nonnegativity and the
node-in-box bound; the reversed box $b < a$ (whose Riemann limit is the
negation) is not treated, in the same spirit as the $x \ge 1$
restriction of `sqrt`{.Agda}.
