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
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Complete where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  id1 : ∀ B C → (B R.+ C) R.+ (R.- B) ≡ C
  id1 B C = cring! S

  id2 : ∀ A B → A ≡ (A R.+ (R.- B)) R.+ B
  id2 A B = cring! S

  neg-sub : ∀ A B → R.- (A R.+ (R.- B)) ≡ B R.+ (R.- A)
  neg-sub A B = cring! S

  split : ∀ A B M → A R.+ (R.- B) ≡ (A R.+ (R.- M)) R.+ (M R.+ (R.- B))
  split A B M = cring! S

  rearr : ∀ a b c d
    → (a R.+ b) R.+ (R.- (c R.+ d)) ≡ (a R.+ (R.- c)) R.+ (b R.+ (R.- d))
  rearr a b c d = cring! S

private module RI = Identities ℝ-comm
```
-->

# Cauchy-completeness of the real numbers {defines="real-completeness real-limit"}

The [[Dedekind reals|dedekind-real]] are constructed to be a
[[located|dedekind-cut]] ordered field, but nothing so far asserts
that they are **complete**: that every Cauchy sequence of reals
converges to a real. This module supplies the missing analytic
primitive. A limit is built as a *fifth* two-sided cut — after
`ratℝ`{.Agda}, `_+ᴿ_`{.Agda}, `_*ᴿ_`{.Agda} and `sqrt`{.Agda} — whose
lower and upper parts are assembled directly from the approximating
reals, with the [[approximation|approx]] modulus doing the work of
locatedness.

## Cauchy approximations

A **Cauchy approximation** is a family of reals $f(\varepsilon)$
indexed by a positive rational slack, such that $f(\varepsilon)$ and
$f(\delta)$ agree to within $\varepsilon + \delta$. This is the
regular-family presentation of a Cauchy sequence, and it is exactly
what the [[approximation lemma|approx]] already produces.

```agda
CauchyApprox : Type
CauchyApprox =
  Σ[ f ∈ ((ε : Ratio) → 0 < ε → ℝ) ]
    (∀ ε δ (p : 0 < ε) (r : 0 < δ)
      → absᴿ (f ε p +ᴿ (-ᴿ f δ r)) ≤ᴿ ratℝ (ε +ℚ δ))
```

<!--
```agda
private abstract
  0<1ℚ : 0 < 1
  0<1ℚ = 0<1'
```
-->

## Some order helpers

Three small facts about the strict and non-strict orders that the
completeness proof needs but which are not in the base development:
a mixed transitivity, the strict inequality that an open membership
witnesses, and cancellation of a rational summand under the strict
order.

```agda
<ᴿ-≤ᴿ-trans : ∀ {x y z} → x <ᴿ y → y ≤ᴿ z → x <ᴿ z
<ᴿ-≤ᴿ-trans {x} {y} {z} p y≤z = ∥-∥-map
  (λ (q , ux , ly) → q , ux , y≤z q ly) p

lower-mem→<ᴿ : ∀ {x u} → ∣ x .lower u ∣ → ratℝ u <ᴿ x
lower-mem→<ᴿ {x} {u} lu = ∥-∥-map
  (λ (s , u<s , ls) → s , u<s , ls)
  (cut.lower-round x u lu)

+ℚ-cancel-<r : ∀ {a b} c → a +ℚ c < b +ℚ c → a < b
+ℚ-cancel-<r {a} {b} c h with holds? (a < b)
... | yes p = p
... | no ¬p = absurd
  (<-irrefl refl (≤-<-trans (+ℚ-preserves-≤ (¬<→≥ ¬p) (≤-refl {c})) h))
```

The embedding of the rationals is monotone and commutes with
negation. Monotonicity is immediate; the negation law is the
observation that $t < -q$ and $q < -t$ are the same condition.

```agda
ratℝ-mono : ∀ {p q} → p ≤ q → ratℝ p ≤ᴿ ratℝ q
ratℝ-mono {p} {q} p≤q s s<p = <-≤-trans s<p p≤q
```

<!--
```agda
private abstract
  flipL : ∀ {a b} → a < (-ℚ b) → b < (-ℚ a)
  flipL {a} {b} p = <-resp (negℚ-invol b) refl (negℚ-anti-< p)

  flipU : ∀ {a b} → (-ℚ a) < b → (-ℚ b) < a
  flipU {a} {b} p = <-resp refl (negℚ-invol a) (negℚ-anti-< p)
```
-->

```agda
ratℝ-neg : ∀ t → (-ᴿ ratℝ t) ≡ ratℝ (-ℚ t)
ratℝ-neg t = ℝ-path
  (funext λ q → Ω-ua (flipL {t} {q}) (flipL {q} {t}))
  (funext λ q → Ω-ua (flipU {q} {t}) (flipU {t} {q}))
```

<!--
```agda
private
  +ᴿ-idl : ∀ x → 0ᴿ +ᴿ x ≡ x
  +ᴿ-idl x = +ᴿ-comm 0ᴿ x ∙ +ᴿ-idr x
```
-->

## Shifting inequalities across a subtraction

Turning $A \le B + C$ into $A - B \le C$ and back is the additive
bookkeeping that the limit modulus runs on; both directions are the
monotonicity of addition composed with a ring identity.

```agda
le→sub : ∀ A B C → A ≤ᴿ (B +ᴿ C) → (A +ᴿ (-ᴿ B)) ≤ᴿ C
le→sub A B C h = subst ((A +ᴿ (-ᴿ B)) ≤ᴿ_) (RI.id1 B C)
  (+ᴿ-mono {A} {B +ᴿ C} { -ᴿ B} { -ᴿ B} h (≤ᴿ-refl { -ᴿ B}))

sub→le : ∀ A B C → (A +ᴿ (-ᴿ B)) ≤ᴿ C → A ≤ᴿ (B +ᴿ C)
sub→le A B C h = subst (_≤ᴿ (B +ᴿ C)) (sym (RI.id2 A B))
  (subst (((A +ᴿ (-ᴿ B)) +ᴿ B) ≤ᴿ_) (+ᴿ-comm C B)
    (+ᴿ-mono {A +ᴿ (-ᴿ B)} {C} {B} {B} h (≤ᴿ-refl {B})))
```

## The limit

A rational $q$ lies below the limit exactly when, for *some* positive
slack $\varepsilon$, the shifted value $q + \varepsilon$ lies below the
approximant $f(\varepsilon)$; dually $r$ lies above the limit when $r -
\varepsilon$ lies above $f(\varepsilon)$ for some slack.

```agda
lim-lower lim-upper : CauchyApprox → Ratio → Ω
lim-lower c q = elΩ (Σ[ ε ∈ Ratio ] Σ[ p ∈ 0 < ε ]
  ∣ (c .fst ε p) .lower (q +ℚ ε) ∣)
lim-upper c r = elΩ (Σ[ ε ∈ Ratio ] Σ[ p ∈ 0 < ε ]
  ∣ (c .fst ε p) .upper (r +ℚ (-ℚ ε)) ∣)
```

<!--
```agda
private
  module _ (c : CauchyApprox) where
    private
      f = c .fst
      cb = c .snd

    abstract
      idr1 : ∀ a → (a +ℚ (-ℚ 1)) +ℚ 1 ≡ a
      idr1 a = rational!

      idu1 : ∀ b → (b +ℚ 1) +ℚ (-ℚ 1) ≡ b
      idu1 b = rational!

      sub-ε-add : ∀ a ε → (a +ℚ (-ℚ ε)) +ℚ ε ≡ a
      sub-ε-add a ε = rational!

    lim-lower-inhab : ∥ Σ Ratio (λ q → ∣ lim-lower c q ∣) ∥
    lim-lower-inhab = ∥-∥-map
      (λ (a , la) → a +ℚ (-ℚ 1)
        , inc (1 , 0<1ℚ , subst (λ z → ∣ (f 1 0<1ℚ) .lower z ∣) (sym (idr1 a)) la))
      (cut.lower-inhab (f 1 0<1ℚ))

    lim-upper-inhab : ∥ Σ Ratio (λ r → ∣ lim-upper c r ∣) ∥
    lim-upper-inhab = ∥-∥-map
      (λ (b , ub) → b +ℚ 1
        , inc (1 , 0<1ℚ , subst (λ z → ∣ (f 1 0<1ℚ) .upper z ∣) (sym (idu1 b)) ub))
      (cut.upper-inhab (f 1 0<1ℚ))

    lim-lower-round
      : ∀ q → ∣ lim-lower c q ∣ → ∥ Σ Ratio (λ r → (q < r) × ∣ lim-lower c r ∣) ∥
    lim-lower-round q = □-elim (λ _ → squash) λ (ε , p , mem) →
      ∥-∥-map
        (λ (s , qε<s , ls) →
          let qs : q < s +ℚ (-ℚ ε)
              qs = +ℚ-cancel-<r ε (<-resp refl (sym (sub-ε-add s ε)) qε<s)
          in midpoint q (s +ℚ (-ℚ ε))
           , mid-<l qs
           , inc (ε , p , cut.lower-close (f ε p)
               (<-resp refl (sub-ε-add s ε) (+ℚ-preserves-<r ε (mid-<r qs))) ls))
        (cut.lower-round (f ε p) (q +ℚ ε) mem)

    lim-lower-close
      : ∀ {q r} → q < r → ∣ lim-lower c r ∣ → ∣ lim-lower c q ∣
    lim-lower-close {q} {r} q<r = □-map λ (ε , p , mem) →
      ε , p , cut.lower-close (f ε p) (+ℚ-preserves-<r ε q<r) mem

    lim-upper-round
      : ∀ r → ∣ lim-upper c r ∣ → ∥ Σ Ratio (λ q → (q < r) × ∣ lim-upper c q ∣) ∥
    lim-upper-round r = □-elim (λ _ → squash) λ (ε , p , mem) →
      ∥-∥-map
        (λ (s , s<rε , us) →
          let sε<r : s +ℚ ε < r
              sε<r = <-resp refl (sub-ε-add r ε) (+ℚ-preserves-<r ε s<rε)
              sqε : s < midpoint (s +ℚ ε) r +ℚ (-ℚ ε)
              sqε = +ℚ-cancel-<r ε (<-resp refl
                (sym (sub-ε-add (midpoint (s +ℚ ε) r) ε)) (mid-<l sε<r))
          in midpoint (s +ℚ ε) r
           , mid-<r sε<r
           , inc (ε , p , cut.upper-close (f ε p) sqε us))
        (cut.upper-round (f ε p) (r +ℚ (-ℚ ε)) mem)

    lim-upper-close
      : ∀ {q r} → q < r → ∣ lim-upper c q ∣ → ∣ lim-upper c r ∣
    lim-upper-close {q} {r} q<r = □-map λ (ε , p , mem) →
      ε , p , cut.upper-close (f ε p) (+ℚ-preserves-<r (-ℚ ε) q<r) mem

    abstract
      disj-eq : ∀ q ε δ → (q +ℚ (-ℚ δ)) +ℚ (ε +ℚ δ) ≡ q +ℚ ε
      disj-eq q ε δ = rational!

    lim-cut-disjoint : ∀ q → ∣ lim-lower c q ∣ → ∣ lim-upper c q ∣ → ⊥
    lim-cut-disjoint q lq uq = □-elim (λ _ → hlevel 1)
      (λ (ε , pε , lmem) → □-elim (λ _ → hlevel 1)
        (λ (δ , pδ , umem) → <ᴿ-irrefl {ratℝ (q +ℚ ε)} (contra ε pε lmem δ pδ umem))
        uq)
      lq
      where
      contra
        : ∀ ε (pε : 0 < ε) → ∣ (f ε pε) .lower (q +ℚ ε) ∣
        → ∀ δ (pδ : 0 < δ) → ∣ (f δ pδ) .upper (q +ℚ (-ℚ δ)) ∣
        → ratℝ (q +ℚ ε) <ᴿ ratℝ (q +ℚ ε)
      contra ε pε lmem δ pδ umem =
        <ᴿ-≤ᴿ-trans {ratℝ (q +ℚ ε)} {f ε pε} {ratℝ (q +ℚ ε)} s1 s-le
        where
        boundᴿ : (f ε pε +ᴿ (-ᴿ f δ pδ)) ≤ᴿ ratℝ (ε +ℚ δ)
        boundᴿ = abs-out-l {f ε pε +ᴿ (-ᴿ f δ pδ)} {ratℝ (ε +ℚ δ)} (cb ε δ pε pδ)

        fε≤ : f ε pε ≤ᴿ (f δ pδ +ᴿ ratℝ (ε +ℚ δ))
        fε≤ = sub→le (f ε pε) (f δ pδ) (ratℝ (ε +ℚ δ)) boundᴿ

        fδ≤ : f δ pδ ≤ᴿ ratℝ (q +ℚ (-ℚ δ))
        fδ≤ = upper→≤ratℝ {f δ pδ} {q +ℚ (-ℚ δ)} umem

        s3 : (f δ pδ +ᴿ ratℝ (ε +ℚ δ)) ≤ᴿ (ratℝ (q +ℚ (-ℚ δ)) +ᴿ ratℝ (ε +ℚ δ))
        s3 = +ᴿ-mono {f δ pδ} {ratℝ (q +ℚ (-ℚ δ))} {ratℝ (ε +ℚ δ)} {ratℝ (ε +ℚ δ)}
               fδ≤ (≤ᴿ-refl {ratℝ (ε +ℚ δ)})

        eqr : (ratℝ (q +ℚ (-ℚ δ)) +ᴿ ratℝ (ε +ℚ δ)) ≡ ratℝ (q +ℚ ε)
        eqr = sym (ratℝ-+ (q +ℚ (-ℚ δ)) (ε +ℚ δ)) ∙ ap ratℝ (disj-eq q ε δ)

        s1 : ratℝ (q +ℚ ε) <ᴿ f ε pε
        s1 = lower-mem→<ᴿ {f ε pε} {q +ℚ ε} lmem

        s-le : f ε pε ≤ᴿ ratℝ (q +ℚ ε)
        s-le = ≤ᴿ-trans {f ε pε} {f δ pδ +ᴿ ratℝ (ε +ℚ δ)} {ratℝ (q +ℚ ε)}
                 fε≤ (subst ((f δ pδ +ᴿ ratℝ (ε +ℚ δ)) ≤ᴿ_) eqr s3)

    lim-cut-located
      : ∀ {q r} → q < r → ∥ ∣ lim-lower c q ∣ ⊎ ∣ lim-upper c r ∣ ∥
    lim-cut-located {q} {r} q<r = ∥-∥-map cases
      (cut.cut-located (f ε 0<ε) locgap)
      where
      d : Ratio
      d = r +ℚ (-ℚ q)

      d-pos : 0 < d
      d-pos = <→positive-diff q<r

      ε : Ratio
      ε = half (half d)

      0<ε : 0 < ε
      0<ε = half-pos (half-pos d-pos)

      abstract
        e1 : (q +ℚ ε) +ℚ ε ≡ q +ℚ (ε +ℚ ε)
        e1 = rational!

        e2 : (r +ℚ (-ℚ ε)) +ℚ ε ≡ r
        e2 = rational!

        qpd : q +ℚ (r +ℚ (-ℚ q)) ≡ r
        qpd = rational!

      εε<d : ε +ℚ ε < d
      εε<d = <-resp (sym (half-sum (half d))) refl (half-lt d-pos)

      qεε<r : q +ℚ (ε +ℚ ε) < r
      qεε<r = <-resp refl qpd (+ℚ-preserves-<l q εε<d)

      locgap : q +ℚ ε < r +ℚ (-ℚ ε)
      locgap = +ℚ-cancel-<r ε (<-resp (sym e1) (sym e2) qεε<r)

      cases
        : ∣ (f ε 0<ε) .lower (q +ℚ ε) ∣ ⊎ ∣ (f ε 0<ε) .upper (r +ℚ (-ℚ ε)) ∣
        → ∣ lim-lower c q ∣ ⊎ ∣ lim-upper c r ∣
      cases (inl l) = inl (inc (ε , 0<ε , l))
      cases (inr u) = inr (inc (ε , 0<ε , u))

lim : CauchyApprox → ℝ
lim c .lower = lim-lower c
lim c .upper = lim-upper c
lim c .has-is-cut = record
  { lower-inhab  = lim-lower-inhab c
  ; upper-inhab  = lim-upper-inhab c
  ; lower-round  = lim-lower-round c
  ; lower-close  = lim-lower-close c
  ; upper-round  = lim-upper-round c
  ; upper-close  = lim-upper-close c
  ; cut-disjoint = lim-cut-disjoint c
  ; cut-located  = lim-cut-located c
  }
```
-->

## The convergence modulus

The limit is within $2\varepsilon$ of each approximant. This is the
sole quantitative output of the construction, and every downstream
consumer accesses the limit only through it.

<!--
```agda
private module _ (c : CauchyApprox) where
  private
    f = c .fst
    cb = c .snd

  L : ℝ
  L = lim c

  -- L is bounded above by fε + 2ε, at the level of the lower cuts.
  private
    lim-upper-bound : (ε : Ratio) (p : 0 < ε) → L ≤ᴿ (f ε p +ᴿ ratℝ (2 *ℚ ε))
    lim-upper-bound ε p q = □-elim (λ _ → hlevel 1) λ (δ , pδ , mem) →
      let
        fδ≤ : f δ pδ ≤ᴿ (f ε p +ᴿ ratℝ (δ +ℚ ε))
        fδ≤ = sub→le (f δ pδ) (f ε p) (ratℝ (δ +ℚ ε))
          (abs-out-l {f δ pδ +ᴿ (-ᴿ f ε p)} {ratℝ (δ +ℚ ε)} (cb δ ε pδ p))

        mem' : ∣ (f ε p +ᴿ ratℝ (δ +ℚ ε)) .lower (q +ℚ δ) ∣
        mem' = fδ≤ (q +ℚ δ) mem
      in □-map
        (λ (r , s , lr , s<δε , qδ<rs) →
          r , s +ℚ (-ℚ δ) , lr
          , <-trans (<-resp refl (δε-δ δ ε) (+ℚ-preserves-<r (-ℚ δ) s<δε))
              (ε<2ε ε p)
          , +ℚ-cancel-<r δ (<-resp refl (sym (rs-δ r s δ)) qδ<rs))
        mem'
      where
      abstract
        δε-δ : ∀ δ ε → (δ +ℚ ε) +ℚ (-ℚ δ) ≡ ε
        δε-δ δ ε = rational!

        rs-δ : ∀ r s δ → (r +ℚ (s +ℚ (-ℚ δ))) +ℚ δ ≡ r +ℚ s
        rs-δ r s δ = rational!

        eq-2ε : ∀ ε → ε +ℚ ε ≡ 2 *ℚ ε
        eq-2ε ε = x+x≡x*2 ε ∙ *ℚ-commutative ε 2

      ε<2ε : ∀ ε → 0 < ε → ε < 2 *ℚ ε
      ε<2ε ε p = <-resp refl (eq-2ε ε) (add-pos-< ε ε p)

  -- fε is bounded above by L + 2ε, at the level of the lower cuts.
  private
    lim-lower-bound : (ε : Ratio) (p : 0 < ε) → f ε p ≤ᴿ (L +ᴿ ratℝ (2 *ℚ ε))
    lim-lower-bound ε p q lq =
      inc (q +ℚ (-ℚ ε) , midpoint ε (2 *ℚ ε)
        , inc (ε , p , subst (λ z → ∣ (f ε p) .lower z ∣) (sym (qε-ε q ε)) lq)
        , mid-<r (ε<2ε ε p)
        , <-resp (qε-ε′ q ε) refl (+ℚ-preserves-<l (q +ℚ (-ℚ ε)) (mid-<l (ε<2ε ε p))))
      where
      abstract
        qε-ε : ∀ q ε → (q +ℚ (-ℚ ε)) +ℚ ε ≡ q
        qε-ε q ε = rational!

        qε-ε′ : ∀ q ε → (q +ℚ (-ℚ ε)) +ℚ ε ≡ q
        qε-ε′ q ε = rational!

        eq-2ε : ∀ ε → ε +ℚ ε ≡ 2 *ℚ ε
        eq-2ε ε = x+x≡x*2 ε ∙ *ℚ-commutative ε 2

      ε<2ε : ∀ ε → 0 < ε → ε < 2 *ℚ ε
      ε<2ε ε p = <-resp refl (eq-2ε ε) (add-pos-< ε ε p)

  lim-modulus′
    : (ε : Ratio) (p : 0 < ε)
    → absᴿ (L +ᴿ (-ᴿ f ε p)) ≤ᴿ ratℝ (2 *ℚ ε)
  lim-modulus′ ε p = abs-≤ {L +ᴿ (-ᴿ f ε p)} {ratℝ (2 *ℚ ε)} first second
    where
    b1 : L ≤ᴿ (f ε p +ᴿ ratℝ (2 *ℚ ε))
    b1 = lim-upper-bound ε p

    b2 : f ε p ≤ᴿ (L +ᴿ ratℝ (2 *ℚ ε))
    b2 = lim-lower-bound ε p

    first : (L +ᴿ (-ᴿ f ε p)) ≤ᴿ ratℝ (2 *ℚ ε)
    first = le→sub L (f ε p) (ratℝ (2 *ℚ ε)) b1

    subeq : (f ε p +ᴿ (-ᴿ L)) ≤ᴿ ratℝ (2 *ℚ ε)
    subeq = le→sub (f ε p) L (ratℝ (2 *ℚ ε)) b2

    second : (-ᴿ ratℝ (2 *ℚ ε)) ≤ᴿ (L +ᴿ (-ᴿ f ε p))
    second = subst ((-ᴿ ratℝ (2 *ℚ ε)) ≤ᴿ_) (RI.neg-sub (f ε p) L)
      (negᴿ-anti {f ε p +ᴿ (-ᴿ L)} {ratℝ (2 *ℚ ε)} subeq)
```
-->

```agda
lim-modulus
  : (c : CauchyApprox) (ε : Ratio) (p : 0 < ε)
  → absᴿ (lim c +ᴿ (-ᴿ c .fst ε p)) ≤ᴿ ratℝ (2 *ℚ ε)
lim-modulus c = lim-modulus′ c
```

## The limit predicate, and uniqueness

Being a limit is a proposition: it is the modulus bound holding at
every slack. The limit we built satisfies it, and any two reals
satisfying it coincide — proved by feeding the difference to the
[[Archimedean squeeze|real-lattice]].

```agda
is-limit : CauchyApprox → ℝ → Type
is-limit c L =
  ∀ (ε : Ratio) (p : 0 < ε) → absᴿ (L +ᴿ (-ᴿ c .fst ε p)) ≤ᴿ ratℝ (2 *ℚ ε)

is-limit-is-prop : (c : CauchyApprox) (L : ℝ) → is-prop (is-limit c L)
is-limit-is-prop c L = Π-is-hlevel 1 λ ε → Π-is-hlevel 1 λ p →
  Π-is-hlevel 1 λ s → fun-is-hlevel 1 ((ratℝ (2 *ℚ ε) .lower s) .is-tr)

lim-is-limit : (c : CauchyApprox) → is-limit c (lim c)
lim-is-limit c = lim-modulus c
```

<!--
```agda
private module _ (c : CauchyApprox) where
  private
    f = c .fst

  -- the difference of two limits is bounded by every 2·(ε/4) = ε/2,
  -- hence squeezed to zero.
  private
    abstract
      quarter-sum : ∀ ε → (2 *ℚ half (half ε)) +ℚ (2 *ℚ half (half ε)) ≡ ε
      quarter-sum ε =
        ap₂ _+ℚ_ (two-half ε) (two-half ε) ∙ half-sum ε
        where
        two-half : ∀ ε → 2 *ℚ half (half ε) ≡ half ε
        two-half ε =
            *ℚ-commutative 2 (half (half ε))
          ∙ sym (x+x≡x*2 (half (half ε)))
          ∙ half-sum (half ε)

  limit-diff-bound
    : (L L' : ℝ) → is-limit c L → is-limit c L'
    → (ε : Ratio) → 0 < ε
    → absᴿ (L +ᴿ (-ᴿ L')) ≤ᴿ ratℝ ε
  limit-diff-bound L L' hL hL' ε 0<ε =
    subst (absᴿ (L +ᴿ (-ᴿ L')) ≤ᴿ_) rat-eq bound
    where
    η : Ratio
    η = half (half ε)

    0<η : 0 < η
    0<η = half-pos (half-pos 0<ε)

    fη : ℝ
    fη = f η 0<η

    bx : absᴿ (L +ᴿ (-ᴿ fη)) ≤ᴿ ratℝ (2 *ℚ η)
    bx = hL η 0<η

    by : absᴿ (fη +ᴿ (-ᴿ L')) ≤ᴿ ratℝ (2 *ℚ η)
    by = subst (λ z → absᴿ z ≤ᴿ ratℝ (2 *ℚ η)) (RI.neg-sub L' fη)
      (abs-neg {L' +ᴿ (-ᴿ fη)} {ratℝ (2 *ℚ η)} (hL' η 0<η))

    bound : absᴿ (L +ᴿ (-ᴿ L')) ≤ᴿ (ratℝ (2 *ℚ η) +ᴿ ratℝ (2 *ℚ η))
    bound = subst (λ z → absᴿ z ≤ᴿ (ratℝ (2 *ℚ η) +ᴿ ratℝ (2 *ℚ η)))
      (sym (RI.split L L' fη))
      (abs-sum {L +ᴿ (-ᴿ fη)} {fη +ᴿ (-ᴿ L')} {ratℝ (2 *ℚ η)} {ratℝ (2 *ℚ η)} bx by)

    rat-eq : (ratℝ (2 *ℚ η) +ᴿ ratℝ (2 *ℚ η)) ≡ ratℝ ε
    rat-eq = sym (ratℝ-+ (2 *ℚ η) (2 *ℚ η)) ∙ ap ratℝ (quarter-sum ε)
```
-->

```agda
limit-unique
  : (c : CauchyApprox) (L L' : ℝ)
  → is-limit c L → is-limit c L' → L ≡ L'
limit-unique c L L' hL hL' =
  L                        ≡⟨ RI.id2 L L' ⟩
  (L +ᴿ (-ᴿ L')) +ᴿ L'     ≡⟨ ap (_+ᴿ L') diff≡0 ⟩
  0ᴿ +ᴿ L'                 ≡⟨ +ᴿ-idl L' ⟩
  L'                       ∎
  where
  sq : ∀ (ε : Ratio) → 0 < ε
     → ((L +ᴿ (-ᴿ L')) ≤ᴿ ratℝ ε) × (ratℝ (-ℚ ε) ≤ᴿ (L +ᴿ (-ᴿ L')))
  sq ε 0<ε =
      abs-out-l {L +ᴿ (-ᴿ L')} {ratℝ ε} (limit-diff-bound c L L' hL hL' ε 0<ε)
    , subst (_≤ᴿ (L +ᴿ (-ᴿ L'))) (ratℝ-neg ε)
        (abs-out-r {L +ᴿ (-ᴿ L')} {ratℝ ε} (limit-diff-bound c L L' hL hL' ε 0<ε))

  diff≡0 : (L +ᴿ (-ᴿ L')) ≡ 0ᴿ
  diff≡0 = squeeze (L +ᴿ (-ᴿ L')) sq
```

## Linearity and monotonicity

The pointwise sum of two Cauchy approximations, reindexed by halving
so its modulus still closes, is again a Cauchy approximation; its
limit is the sum of the limits. Monotone approximations have monotone
limits, and the constant approximation converges to its value.

<!--
```agda
private abstract
  half-half-sum : ∀ ε δ → (half ε +ℚ half δ) +ℚ (half ε +ℚ half δ) ≡ ε +ℚ δ
  half-half-sum ε δ =
      swap ∙ ap₂ _+ℚ_ (half-sum ε) (half-sum δ)
    where
    swap : (half ε +ℚ half δ) +ℚ (half ε +ℚ half δ)
         ≡ (half ε +ℚ half ε) +ℚ (half δ +ℚ half δ)
    swap = rational!
```
-->

```agda
_+ᶜ_ : CauchyApprox → CauchyApprox → CauchyApprox
(c +ᶜ c') .fst ε p = c .fst (half ε) (half-pos p) +ᴿ c' .fst (half ε) (half-pos p)
(c +ᶜ c') .snd ε δ p r =
  subst (λ z → absᴿ z ≤ᴿ ratℝ (ε +ℚ δ)) (sym (RI.rearr aε bε aδ bδ))
    (subst (absᴿ ((aε +ᴿ (-ᴿ aδ)) +ᴿ (bε +ᴿ (-ᴿ bδ))) ≤ᴿ_) rat-eq
      (abs-sum {aε +ᴿ (-ᴿ aδ)} {bε +ᴿ (-ᴿ bδ)}
        {ratℝ (half ε +ℚ half δ)} {ratℝ (half ε +ℚ half δ)}
        (c .snd (half ε) (half δ) (half-pos p) (half-pos r))
        (c' .snd (half ε) (half δ) (half-pos p) (half-pos r))))
  where
  aε = c .fst (half ε) (half-pos p)
  aδ = c .fst (half δ) (half-pos r)
  bε = c' .fst (half ε) (half-pos p)
  bδ = c' .fst (half δ) (half-pos r)

  rat-eq
    : (ratℝ (half ε +ℚ half δ) +ᴿ ratℝ (half ε +ℚ half δ)) ≡ ratℝ (ε +ℚ δ)
  rat-eq = sym (ratℝ-+ (half ε +ℚ half δ) (half ε +ℚ half δ))
    ∙ ap ratℝ (half-half-sum ε δ)

const-approx : ℝ → CauchyApprox
const-approx x .fst _ _ = x
const-approx x .snd ε δ p r =
  subst (_≤ᴿ ratℝ (ε +ℚ δ)) (sym az) 0≤εδ
  where
  abs0 : absᴿ 0ᴿ ≡ 0ᴿ
  abs0 =
    maxᴿ 0ᴿ (-ᴿ 0ᴿ)  ≡⟨ ap (maxᴿ 0ᴿ) (ratℝ-neg 0) ⟩
    maxᴿ 0ᴿ (ratℝ (-ℚ 0)) ≡⟨ ap (λ z → maxᴿ 0ᴿ (ratℝ z)) neg-zero ⟩
    maxᴿ 0ᴿ 0ᴿ       ≡⟨ maxᴿ-idem 0ᴿ ⟩
    0ᴿ               ∎

  az : absᴿ (x +ᴿ (-ᴿ x)) ≡ 0ᴿ
  az = ap absᴿ (+ᴿ-invr x) ∙ abs0

  0≤εδ : 0ᴿ ≤ᴿ ratℝ (ε +ℚ δ)
  0≤εδ = ratℝ-mono {0} {ε +ℚ δ} (<-weaken (<-+ ε δ p r))
    where
    <-+ : ∀ ε δ → 0 < ε → 0 < δ → 0 < ε +ℚ δ
    <-+ ε δ p r = <-trans p (add-pos-< ε δ r)
```

<!--
```agda
private module _ (c c' : CauchyApprox) where
  private
    f = c .fst
    f' = c' .fst

  -- lim c + lim c' is a limit of c +ᶜ c'.
  sum-is-limit : is-limit (c +ᶜ c') (lim c +ᴿ lim c')
  sum-is-limit ε p =
      subst (λ z → absᴿ z ≤ᴿ ratℝ (2 *ℚ ε))
        (sym (RI.rearr (lim c) (lim c') aη bη))
        (subst (absᴿ ((lim c +ᴿ (-ᴿ aη)) +ᴿ (lim c' +ᴿ (-ᴿ bη))) ≤ᴿ_) rat-eq
          (abs-sum {lim c +ᴿ (-ᴿ aη)} {lim c' +ᴿ (-ᴿ bη)}
            {ratℝ (2 *ℚ half ε)} {ratℝ (2 *ℚ half ε)} mc mc'))
      where
      aη = f (half ε) (half-pos p)
      bη = f' (half ε) (half-pos p)

      mc : absᴿ (lim c +ᴿ (-ᴿ aη)) ≤ᴿ ratℝ (2 *ℚ half ε)
      mc = lim-modulus c (half ε) (half-pos p)

      mc' : absᴿ (lim c' +ᴿ (-ᴿ bη)) ≤ᴿ ratℝ (2 *ℚ half ε)
      mc' = lim-modulus c' (half ε) (half-pos p)

      abstract
        two-half-two : ∀ ε → (2 *ℚ half ε) +ℚ (2 *ℚ half ε) ≡ 2 *ℚ ε
        two-half-two ε =
          ap₂ _+ℚ_ (th' ε) (th' ε) ∙ x+x≡x*2 ε ∙ *ℚ-commutative ε 2
          where
          th' : ∀ ε → 2 *ℚ half ε ≡ ε
          th' ε = *ℚ-commutative 2 (half ε)
            ∙ sym (x+x≡x*2 (half ε)) ∙ half-sum ε

      rat-eq : (ratℝ (2 *ℚ half ε) +ᴿ ratℝ (2 *ℚ half ε)) ≡ ratℝ (2 *ℚ ε)
      rat-eq = sym (ratℝ-+ (2 *ℚ half ε) (2 *ℚ half ε))
        ∙ ap ratℝ (two-half-two ε)
```
-->

```agda
lim-add
  : (c c' : CauchyApprox)
  → lim (c +ᶜ c') ≡ lim c +ᴿ lim c'
lim-add c c' = limit-unique (c +ᶜ c') (lim (c +ᶜ c')) (lim c +ᴿ lim c')
  (lim-is-limit (c +ᶜ c')) (sum-is-limit c c')

lim-mono
  : (c c' : CauchyApprox)
  → (∀ ε (p : 0 < ε) → c .fst ε p ≤ᴿ c' .fst ε p)
  → lim c ≤ᴿ lim c'
lim-mono c c' hyp q = □-map λ (ε , p , mem) →
  ε , p , hyp ε p (q +ℚ ε) mem

lim-const : (x : ℝ) → lim (const-approx x) ≡ x
lim-const x = limit-unique (const-approx x) (lim (const-approx x)) x
  (lim-is-limit (const-approx x)) x-is-limit
  where
  x-is-limit : is-limit (const-approx x) x
  x-is-limit ε p = subst (_≤ᴿ ratℝ (2 *ℚ ε)) (sym az) 0≤2ε
    where
    abs0 : absᴿ 0ᴿ ≡ 0ᴿ
    abs0 =
      maxᴿ 0ᴿ (-ᴿ 0ᴿ)       ≡⟨ ap (maxᴿ 0ᴿ) (ratℝ-neg 0) ⟩
      maxᴿ 0ᴿ (ratℝ (-ℚ 0)) ≡⟨ ap (λ z → maxᴿ 0ᴿ (ratℝ z)) neg-zero ⟩
      maxᴿ 0ᴿ 0ᴿ            ≡⟨ maxᴿ-idem 0ᴿ ⟩
      0ᴿ                    ∎

    az : absᴿ (x +ᴿ (-ᴿ x)) ≡ 0ᴿ
    az = ap absᴿ (+ᴿ-invr x) ∙ abs0

    0≤2ε : 0ᴿ ≤ᴿ ratℝ (2 *ℚ ε)
    0≤2ε = ratℝ-mono {0} {2 *ℚ ε} (<-weaken 0<2ε)
      where
      0<2ε : 0 < 2 *ℚ ε
      0<2ε = <-resp refl (x+x≡x*2 ε ∙ *ℚ-commutative ε 2) (<-trans p (add-pos-< ε ε p))
```
