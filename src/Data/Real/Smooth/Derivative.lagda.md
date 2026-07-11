<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Reciprocal
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Derivative where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
open positive-bounds
open negative-bounds

private
  ratℝ-mono : ∀ {p q} → p ≤ q → ratℝ p ≤ᴿ ratℝ q
  ratℝ-mono p≤q r r<p = <-≤-trans r<p p≤q

  neg1<0 : (-ℚ 1) < 0
  neg1<0 = <-resp refl neg-zero (negℚ-anti-< 0<1')
```
-->

# Separation and the derivative {defines="hadamard-separation real-derivative"}

A raw [[Hadamard tower|hadamard-tower]] pins its quotient off the
diagonal only; the [[bound data|bounded-smooth-function]] of the
enriched towers supplies exactly the missing modulus of continuity.
This module cashes that in: two bounded towers for the same
function have *equal* first quotients, so the derivative of a
bounded-smooth function is well defined even under propositional
truncation of the tower.

## The comparison toolkit

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  tele3
    : ∀ a b c
    → a R.+ (R.- c) ≡ (a R.+ (R.- b)) R.+ (b R.+ (R.- c))
  tele3 a b c = cring! S

  recompose : ∀ a b → a ≡ b R.+ (a R.+ (R.- b))
  recompose a b = cring! S

  neg-diff : ∀ a b → R.- (a R.+ (R.- b)) ≡ b R.+ (R.- a)
  neg-diff a b = cring! S

private module RI = Identities ℝ-comm
```
-->

The absolute value is nonnegative — locatedness between $q < -q$
lands in one of the two branches of the join.

```agda
abs-nonneg : ∀ x → 0ᴿ ≤ᴿ absᴿ x
abs-nonneg x q q<0 =
  ∥-∥-rec (absᴿ x .lower q .is-tr)
    (λ where
      (inl lq) → inc (inl lq)
      (inr uq) → inc (inr uq))
    (cut.cut-located x (<-trans q<0 0<-q))
  where
  0<-q : 0 < (-ℚ q)
  0<-q = <-resp refl (+ℚ-idl (-ℚ q)) (<→positive-diff q<0)
```

Negation and one-sided multiplication commute with the rational
embedding.

```agda
ratℝ-neg : ∀ p → -ᴿ ratℝ p ≡ ratℝ (-ℚ p)
ratℝ-neg p = ℝ-path
  (funext λ q → Ω-ua
    (λ p<-q → <-resp (negℚ-invol q) refl (negℚ-anti-< p<-q))
    (λ q<-p → <-resp (negℚ-invol p) refl (negℚ-anti-< q<-p)))
  (funext λ q → Ω-ua
    (λ -q<p → <-resp refl (negℚ-invol q) (negℚ-anti-< -q<p))
    (λ -p<q → <-resp refl (negℚ-invol p) (negℚ-anti-< -p<q)))

ratℝ-*-≤ : ∀ p q → (ratℝ p *ᴿ ratℝ q) ≤ᴿ ratℝ (p *ℚ q)
ratℝ-*-≤ p q r lr =
  □-rec (ratℝ (p *ℚ q) .lower r .is-tr)
    (λ (a , b , c , d , la , ub , lc , ud , r<min) →
      <-≤-trans r<min
        (bracket-lower p q a b c d
          (<-weaken la) (<-weaken ub) (<-weaken lc) (<-weaken ud)))
    lr
```

Cancellation by an invertible difference, and the fact that a zero
difference means equality.

```agda
diff-zero→≡ : ∀ {a b} → (a +ᴿ (-ᴿ b)) ≡ 0ᴿ → a ≡ b
diff-zero→≡ {a} {b} p =
    sym (+ᴿ-idr a)
  ∙ ap (a +ᴿ_) (sym (+ᴿ-comm (-ᴿ b) b ∙ +ᴿ-invr b))
  ∙ +ᴿ-assoc a (-ᴿ b) b
  ∙ ap (_+ᴿ b) p
  ∙ +ᴿ-comm 0ᴿ b
  ∙ +ᴿ-idr b

cancel-apart
  : (d : ℝ) (s : positive-bounds d ⊎ negative-bounds d) {a b : ℝ}
  → d *ᴿ a ≡ d *ᴿ b → a ≡ b
cancel-apart d s {a} {b} p =
    sym (*ᴿ-idl a)
  ∙ ap (_*ᴿ a) (sym (recip±-invr d s) ∙ *ᴿ-comm d r)
  ∙ *ᴿ-assoc r d a
  ∙ ap (r *ᴿ_) p
  ∙ sym (*ᴿ-assoc r d b)
  ∙ ap (_*ᴿ b) (*ᴿ-comm r d ∙ recip±-invr d s)
  ∙ *ᴿ-idl b
  where
  r : ℝ
  r = recip± d s
```

The differences $z - u$ that the pinning argument cancels by are
apart from zero as soon as a rational witness strictly separates
$u$ from $z$ — and the bounds records need only *merely* exist.

```agda
diff-pos-bounds
  : (z : ℝ) (u p : Ratio) → u < p → ∣ z .lower p ∣
  → ∥ positive-bounds (z +ᴿ (-ᴿ ratℝ u)) ∥
diff-pos-bounds z u p u<p lp = ∥-∥-map mk-bounds (cut.upper-inhab z)
  where
  m : Ratio
  m = midpoint u p

  gap : Ratio
  gap = p +ℚ (-ℚ m)

  0<gap : 0 < gap
  0<gap = <→positive-diff (mid-<r u<p)

  mk-bounds : Σ Ratio (λ v → ∣ z .upper v ∣) → positive-bounds (z +ᴿ (-ᴿ ratℝ u))
  mk-bounds (V , uV) .lo = half gap
  mk-bounds (V , uV) .hi = (V +ℚ (1 +ℚ (-ℚ u))) +ℚ 1
  mk-bounds (V , uV) .lo-mem = inc
    ( p , -ℚ m , lp
    , <-resp refl (sym (negℚ-invol m)) (mid-<l u<p)
    , half-lt 0<gap)
  mk-bounds (V , uV) .hi-mem = inc
    ( V , 1 +ℚ (-ℚ u) , uV
    , <-resp (sym (negu-eq u)) refl u-1<u
    , <-resp (+ℚ-idr (V +ℚ (1 +ℚ (-ℚ u)))) refl
        (+ℚ-preserves-<l (V +ℚ (1 +ℚ (-ℚ u))) 0<1'))
    where
    negu-eq : ∀ u → -ℚ (1 +ℚ (-ℚ u)) ≡ u +ℚ (-ℚ 1)
    negu-eq u = rational!

    u-1<u : (u +ℚ (-ℚ 1)) < u
    u-1<u = <-resp refl (+ℚ-idr u) (+ℚ-preserves-<l u neg1<0)
  mk-bounds (V , uV) .lo-pos = half-pos 0<gap

diff-neg-bounds
  : (z : ℝ) (w q : Ratio) → q < w → ∣ z .upper q ∣
  → ∥ negative-bounds (z +ᴿ (-ᴿ ratℝ w)) ∥
diff-neg-bounds z w q q<w uq = ∥-∥-map mk-bounds (cut.lower-inhab z)
  where
  m : Ratio
  m = midpoint q w

  gap : Ratio
  gap = m +ℚ (-ℚ q)

  0<gap : 0 < gap
  0<gap = <→positive-diff (mid-<l q<w)

  mk-bounds : Σ Ratio (λ v → ∣ z .lower v ∣) → negative-bounds (z +ᴿ (-ᴿ ratℝ w))
  mk-bounds (L , lL) .lo = (L +ℚ (-ℚ w)) +ℚ (-ℚ 2)
  mk-bounds (L , lL) .hi = -ℚ (half gap)
  mk-bounds (L , lL) .lo-mem = inc
    ( L , (-ℚ w) +ℚ (-ℚ 1) , lL
    , <-resp refl (neg-into w) w<w+1
    , lo-step)
    where
    neg-into : ∀ w → w +ℚ 1 ≡ -ℚ ((-ℚ w) +ℚ (-ℚ 1))
    neg-into w = rational!

    w<w+1 : w < (w +ℚ 1)
    w<w+1 = <-resp (+ℚ-idr w) refl (+ℚ-preserves-<l w 0<1')

    reshuffle : (L +ℚ (-ℚ w)) +ℚ (-ℚ 1) ≡ L +ℚ ((-ℚ w) +ℚ (-ℚ 1))
    reshuffle = rational!

    two-one : ((L +ℚ (-ℚ w)) +ℚ (-ℚ 2)) +ℚ 1 ≡ (L +ℚ (-ℚ w)) +ℚ (-ℚ 1)
    two-one = rational!

    lo-step : ((L +ℚ (-ℚ w)) +ℚ (-ℚ 2)) < (L +ℚ ((-ℚ w) +ℚ (-ℚ 1)))
    lo-step = <-resp (+ℚ-idr _) (two-one ∙ reshuffle)
      (+ℚ-preserves-<l ((L +ℚ (-ℚ w)) +ℚ (-ℚ 2)) 0<1')
  mk-bounds (L , lL) .hi-mem = inc
    ( q , -ℚ m , uq
    , <-resp (sym (negℚ-invol m)) refl (mid-<r q<w)
    , <-resp (neg-gap-eq q m) refl (negℚ-anti-< (half-lt 0<gap)))
    where
    neg-gap-eq : ∀ q m → -ℚ (m +ℚ (-ℚ q)) ≡ q +ℚ (-ℚ m)
    neg-gap-eq q m = rational!
  mk-bounds (L , lL) .hi-neg = <-resp refl neg-zero
    (negℚ-anti-< (half-pos 0<gap))
```

## Separation

Two Hadamard quotients for the same function, each with a bounded
next level, are equal *everywhere* — including on the diagonal. Off
the diagonal a rational pin cancels; the bounded second level is a
Lipschitz modulus that transports the pinned values onto the
diagonal, and the [[Archimedean squeeze|dedekind-reals]] finishes.

<!--
```agda
private
  set-cons
    : ∀ {n} (t r : ℝ) (x : Fin n → ℝ)
    → set (cons t x) fzero r ≡ cons r x
  set-cons {n} t r x = funext go where
    go : ∀ j → set (cons t x) fzero r j ≡ cons r x j
    go j with fin-view j
    ... | zero   = refl
    ... | suc j' = refl

  cons-eta
    : ∀ {n} (w : Fin (suc n) → ℝ)
    → cons (w fzero) (λ j → w (fsuc j)) ≡ w
  cons-eta w = funext go where
    go : ∀ l → cons (w fzero) (λ j → w (fsuc j)) l ≡ w l
    go l with fin-view l
    ... | zero   = refl
    ... | suc l' = refl

  ≤ᴿ-prop : ∀ {a b : ℝ} → is-prop (a ≤ᴿ b)
  ≤ᴿ-prop {a} {b} = Π-is-hlevel 1 λ q → Π-is-hlevel 1 λ _ →
    (b .lower q) .is-tr
```
-->

```agda
quot-agree
  : ∀ {n} (f : Fun n) (i : Fin n) (g₁ g₂ : Fun (suc n))
  → Quot n f i g₁ → Quot n f i g₂
  → (h₁ h₂ : Fun (suc (suc n)))
  → Quot (suc n) g₁ fzero h₁ → Quot (suc n) g₂ fzero h₂
  → Bd (suc (suc n)) h₁ → Bd (suc (suc n)) h₂
  → (t : ℝ) (x : Fin n → ℝ)
  → g₁ (cons t x) ≡ g₂ (cons t x)
quot-agree {n} f i g₁ g₂ q₁ q₂ h₁ h₂ qh₁ qh₂ bh₁ bh₂ t x =
  diff-zero→≡ (squeeze d λ ε 0<ε →
    let key = bound ε 0<ε in
      abs-out-l {d} {ratℝ ε} key
    , subst (_≤ᴿ d) (ratℝ-neg ε) (abs-out-r {d} {ratℝ ε} key))
  where
  g1w g2w : ℝ
  g1w = g₁ (cons t x)
  g2w = g₂ (cons t x)

  d : ℝ
  d = g1w +ᴿ (-ᴿ g2w)

  bound : (ε : Ratio) → 0 < ε → absᴿ d ≤ᴿ ratℝ ε
  bound ε 0<ε =
    ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε}) (λ xb →
    ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε}) (λ (Bt , tb) →
      stage2 xb Bt tb)
      (bounded-above (absᴿ t)))
      (finite-choice n (λ j → bounded-above (absᴿ (x j))))
    where
    stage2
      : ((j : Fin n) → Σ Ratio (λ V → absᴿ (x j) ≤ᴿ ratℝ V))
      → (Bt : Ratio) → absᴿ t ≤ᴿ ratℝ Bt
      → absᴿ d ≤ᴿ ratℝ ε
    stage2 xb Bt tb =
      ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε}) (λ (M₁ , H₁) →
      ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε}) (λ (M₂ , H₂) →
        stage3 M₁ H₁ M₂ H₂)
        (bh₂ R))
        (bh₁ R)
      where
      R₀ R : Ratio
      R₀ = maxℚ Bt (maxFin (λ j → xb j .fst))
      R  = R₀ +ℚ 1

      R₀≤R : R₀ ≤ R
      R₀≤R = ≤-resp (+ℚ-idr R₀) refl
        (+ℚ-preserves-≤ (≤-refl {R₀}) (<-weaken 0<1'))

      t-bound-R : absᴿ t ≤ᴿ ratℝ R
      t-bound-R = ≤ᴿ-trans {absᴿ t} {ratℝ Bt} {ratℝ R} tb
        (ratℝ-mono (≤-trans (maxℚ-≤l {Bt} {maxFin (λ j → xb j .fst)}) R₀≤R))

      x-bound-R : ∀ j → absᴿ (x j) ≤ᴿ ratℝ R
      x-bound-R j = ≤ᴿ-trans {absᴿ (x j)} {ratℝ (xb j .fst)} {ratℝ R}
        (xb j .snd)
        (ratℝ-mono (≤-trans (maxFin-≥ (λ j' → xb j' .fst) j)
          (≤-trans (maxℚ-≤r {Bt} {maxFin (λ j' → xb j' .fst)}) R₀≤R)))

      stage3
        : (M₁ : Ratio)
        → ((z : Fin (suc (suc n)) → ℝ) → InBox (suc (suc n)) R z → absᴿ (h₁ z) ≤ᴿ ratℝ M₁)
        → (M₂ : Ratio)
        → ((z : Fin (suc (suc n)) → ℝ) → InBox (suc (suc n)) R z → absᴿ (h₂ z) ≤ᴿ ratℝ M₂)
        → absᴿ d ≤ᴿ ratℝ ε
      stage3 M₁ H₁ M₂ H₂ =
        ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε})
          (λ (u , w' , lu , uw , width) → stage4 u w' lu uw width)
          (approx t (half δ) (half-pos 0<δ))
        where
        M₁' M₂' SS D : Ratio
        M₁' = maxℚ M₁ 0
        M₂' = maxℚ M₂ 0
        SS  = M₁' +ℚ M₂'
        D   = SS +ℚ 1

        0≤SS : 0 ≤ SS
        0≤SS = ≤-resp (+ℚ-idr 0) refl
          (+ℚ-preserves-≤ (maxℚ-≤r {M₁} {0}) (maxℚ-≤r {M₂} {0}))

        0<D : 0 < D
        0<D = <-≤-trans 0<1'
          (≤-resp (+ℚ-idl 1) refl (+ℚ-preserves-≤ 0≤SS (≤-refl {1})))

        D≠0 : Nonzero D
        D≠0 = inc (positive→nonzero (to-positive 0<D))

        δ' δ : Ratio
        δ' = (ε /ℚ D) ⦃ D≠0 ⦄
        δ  = minℚ δ' 1

        0<δ' : 0 < δ'
        0<δ' = div-pos ε D ⦃ D≠0 ⦄ 0<ε 0<D

        0<δ : 0 < δ
        0<δ = minℚ-glb 0<δ' 0<1'

        stage4
          : (u w' : Ratio)
          → ∣ t .lower u ∣ → ∣ t .upper w' ∣
          → (w' +ℚ (-ℚ u)) < half δ
          → absᴿ d ≤ᴿ ratℝ ε
        stage4 u w' lu uw width =
          ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε})
            (λ where
              (inl lp) →
                ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε})
                  (λ pb → main u (≤-refl {u}) (<-weaken u<w') (inl pb))
                  (diff-pos-bounds (x i) u p u<p lp)
              (inr uq) →
                ∥-∥-rec (≤ᴿ-prop {absᴿ d} {ratℝ ε})
                  (λ nb → main w' (<-weaken u<w') (≤-refl {w'}) (inr nb))
                  (diff-neg-bounds (x i) w' q' q'<w' uq))
            (cut.cut-located (x i) p<q')
          where
          u<w' : u < w'
          u<w' = lower<upper t lu uw

          p q' : Ratio
          p  = midpoint u w'
          q' = midpoint p w'

          u<p : u < p
          u<p = mid-<l u<w'

          p<q' : p < q'
          p<q' = mid-<l (mid-<r u<w')

          q'<w' : q' < w'
          q'<w' = mid-<r (mid-<r u<w')

          main
            : (s : Ratio) → u ≤ s → s ≤ w'
            → positive-bounds ((x i) +ᴿ (-ᴿ ratℝ s))
              ⊎ negative-bounds ((x i) +ᴿ (-ᴿ ratℝ s))
            → absᴿ d ≤ᴿ ratℝ ε
          main s u≤s s≤w' sd =
            subst (λ z → absᴿ z ≤ᴿ ratℝ ε) (sym dpath) big
            where
            g1ws g2ws : ℝ
            g1ws = g₁ (cons (ratℝ s) x)
            g2ws = g₂ (cons (ratℝ s) x)

            pin : g1ws ≡ g2ws
            pin = cancel-apart ((x i) +ᴿ (-ᴿ ratℝ s)) sd
              (sym (q₁ x (ratℝ s)) ∙ q₂ x (ratℝ s))

            dpath : d ≡ (g1w +ᴿ (-ᴿ g1ws)) +ᴿ (g2ws +ᴿ (-ᴿ g2w))
            dpath = RI.tele3 g1w g1ws g2w
              ∙ ap (λ z → (g1w +ᴿ (-ᴿ g1ws)) +ᴿ (z +ᴿ (-ᴿ g2w))) pin

            z⁺ : Fin (suc (suc n)) → ℝ
            z⁺ = cons (ratℝ s) (cons t x)

            Δ : ℝ
            Δ = t +ᴿ (-ᴿ ratℝ s)

            Δ-up : Δ ≤ᴿ ratℝ δ
            Δ-up = ≤ᴿ-trans {Δ} {ratℝ w' +ᴿ (-ᴿ ratℝ u)} {ratℝ δ}
              (+ᴿ-mono {t} {ratℝ w'} { -ᴿ ratℝ s} { -ᴿ ratℝ u}
                (upper→≤ratℝ {t} {w'} uw)
                (negᴿ-anti {ratℝ u} {ratℝ s} (ratℝ-mono u≤s)))
              (subst (_≤ᴿ ratℝ δ)
                (sym (ap (ratℝ w' +ᴿ_) (ratℝ-neg u) ∙ sym (ratℝ-+ w' (-ℚ u))))
                (ratℝ-mono (<-weaken (<-trans width (half-lt 0<δ)))))

            Δ-lo : (-ᴿ ratℝ δ) ≤ᴿ Δ
            Δ-lo = ≤ᴿ-trans { -ᴿ ratℝ δ} {ratℝ u +ᴿ (-ᴿ ratℝ w')} {Δ}
              (subst (_≤ᴿ (ratℝ u +ᴿ (-ᴿ ratℝ w')))
                (sym (ratℝ-neg δ))
                (subst (ratℝ (-ℚ δ) ≤ᴿ_)
                  (sym (ap (ratℝ u +ᴿ_) (ratℝ-neg w') ∙ sym (ratℝ-+ u (-ℚ w'))))
                  (ratℝ-mono neg-δ≤)))
              (+ᴿ-mono {ratℝ u} {t} { -ᴿ ratℝ w'} { -ᴿ ratℝ s}
                (lower→ratℝ≤ {t} {u} lu)
                (negᴿ-anti {ratℝ s} {ratℝ w'} (ratℝ-mono s≤w')))
              where
              flip-eq : -ℚ (w' +ℚ (-ℚ u)) ≡ u +ℚ (-ℚ w')
              flip-eq = rational!

              neg-δ≤ : (-ℚ δ) ≤ (u +ℚ (-ℚ w'))
              neg-δ≤ = ≤-resp refl flip-eq
                (negℚ-anti-≤ (<-weaken (<-trans width (half-lt 0<δ))))

            Δbound : absᴿ Δ ≤ᴿ ratℝ δ
            Δbound = abs-≤ {Δ} {ratℝ δ} Δ-up Δ-lo

            inbox : InBox (suc (suc n)) R z⁺
            inbox l with fin-view l
            ... | zero   = s-bound
              where
              s-decomp : ratℝ s ≡ t +ᴿ (ratℝ s +ᴿ (-ᴿ t))
              s-decomp = RI.recompose (ratℝ s) t

              sΔ : absᴿ (ratℝ s +ᴿ (-ᴿ t)) ≤ᴿ ratℝ 1
              sΔ = subst (λ z → absᴿ z ≤ᴿ ratℝ 1) (RI.neg-diff t (ratℝ s))
                (abs-neg {Δ} {ratℝ 1}
                  (≤ᴿ-trans {absᴿ Δ} {ratℝ δ} {ratℝ 1} Δbound
                    (ratℝ-mono (minℚ-≤r {δ'} {1}))))

              s-bound : absᴿ (ratℝ s) ≤ᴿ ratℝ R
              s-bound = subst (λ z → absᴿ z ≤ᴿ ratℝ R) (sym s-decomp)
                (subst (absᴿ (t +ᴿ (ratℝ s +ᴿ (-ᴿ t))) ≤ᴿ_)
                  (sym (ratℝ-+ R₀ 1))
                  (abs-sum {t} {ratℝ s +ᴿ (-ᴿ t)} {ratℝ R₀} {ratℝ 1}
                    (≤ᴿ-trans {absᴿ t} {ratℝ Bt} {ratℝ R₀} tb
                      (ratℝ-mono (maxℚ-≤l {Bt} {maxFin (λ j → xb j .fst)})))
                    sΔ))
            ... | suc l' = inner l'
              where
              inner : (l' : Fin (suc n)) → absᴿ (cons t x l') ≤ᴿ ratℝ R
              inner l' with fin-view l'
              ... | zero  = t-bound-R
              ... | suc j = x-bound-R j

            lip₁ : g1w +ᴿ (-ᴿ g1ws) ≡ Δ *ᴿ h₁ z⁺
            lip₁ =
                ap (λ z → g1w +ᴿ (-ᴿ g₁ z)) (sym (set-cons t (ratℝ s) x))
              ∙ qh₁ (cons t x) (ratℝ s)

            lip₂ : g2w +ᴿ (-ᴿ g2ws) ≡ Δ *ᴿ h₂ z⁺
            lip₂ =
                ap (λ z → g2w +ᴿ (-ᴿ g₂ z)) (sym (set-cons t (ratℝ s) x))
              ∙ qh₂ (cons t x) (ratℝ s)

            absA : absᴿ (g1w +ᴿ (-ᴿ g1ws)) ≤ᴿ ratℝ (δ *ℚ M₁')
            absA = subst (λ z → absᴿ z ≤ᴿ ratℝ (δ *ℚ M₁')) (sym lip₁)
              (≤ᴿ-trans {absᴿ (Δ *ᴿ h₁ z⁺)} {ratℝ δ *ᴿ ratℝ M₁'} {ratℝ (δ *ℚ M₁')}
                (abs-prod {Δ} {h₁ z⁺} {ratℝ δ} {ratℝ M₁'} Δbound
                  (≤ᴿ-trans {absᴿ (h₁ z⁺)} {ratℝ M₁} {ratℝ M₁'}
                    (H₁ z⁺ inbox) (ratℝ-mono (maxℚ-≤l {M₁} {0}))))
                (ratℝ-*-≤ δ M₁'))

            absB : absᴿ (g2ws +ᴿ (-ᴿ g2w)) ≤ᴿ ratℝ (δ *ℚ M₂')
            absB = subst (λ z → absᴿ z ≤ᴿ ratℝ (δ *ℚ M₂'))
              (RI.neg-diff g2w g2ws)
              (abs-neg {g2w +ᴿ (-ᴿ g2ws)} {ratℝ (δ *ℚ M₂')}
                (subst (λ z → absᴿ z ≤ᴿ ratℝ (δ *ℚ M₂')) (sym lip₂)
                  (≤ᴿ-trans {absᴿ (Δ *ᴿ h₂ z⁺)} {ratℝ δ *ᴿ ratℝ M₂'} {ratℝ (δ *ℚ M₂')}
                    (abs-prod {Δ} {h₂ z⁺} {ratℝ δ} {ratℝ M₂'} Δbound
                      (≤ᴿ-trans {absᴿ (h₂ z⁺)} {ratℝ M₂} {ratℝ M₂'}
                        (H₂ z⁺ inbox) (ratℝ-mono (maxℚ-≤l {M₂} {0}))))
                    (ratℝ-*-≤ δ M₂'))))

            rat-step : ((δ *ℚ M₁') +ℚ (δ *ℚ M₂')) ≤ ε
            rat-step = ≤-resp (sym distrib) cancel-D
              (≤-trans
                (*ℚ-preserves-≤r SS (minℚ-≤l {δ'} {1}) 0≤SS)
                (*ℚ-preserves-≤l δ' (<-weaken 0<δ')
                  (≤-resp (+ℚ-idr SS) refl
                    (+ℚ-preserves-≤ (≤-refl {SS}) (<-weaken 0<1')))))
              where
              distrib : (δ *ℚ M₁') +ℚ (δ *ℚ M₂') ≡ δ *ℚ SS
              distrib = rational!

              cancel-D : δ' *ℚ D ≡ ε
              cancel-D = /ℚ-scaler ⦃ D≠0 ⦄ ∙ /ℚ-factorr ⦃ D≠0 ⦄

            big : absᴿ ((g1w +ᴿ (-ᴿ g1ws)) +ᴿ (g2ws +ᴿ (-ᴿ g2w))) ≤ᴿ ratℝ ε
            big = ≤ᴿ-trans
              {absᴿ ((g1w +ᴿ (-ᴿ g1ws)) +ᴿ (g2ws +ᴿ (-ᴿ g2w)))}
              {ratℝ ((δ *ℚ M₁') +ℚ (δ *ℚ M₂'))} {ratℝ ε}
              (subst (absᴿ ((g1w +ᴿ (-ᴿ g1ws)) +ᴿ (g2ws +ᴿ (-ᴿ g2w))) ≤ᴿ_)
                (sym (ratℝ-+ (δ *ℚ M₁') (δ *ℚ M₂')))
                (abs-sum {g1w +ᴿ (-ᴿ g1ws)} {g2ws +ᴿ (-ᴿ g2w)}
                  {ratℝ (δ *ℚ M₁')} {ratℝ (δ *ℚ M₂')} absA absB))
              (ratℝ-mono rat-step)
```

## The derivative

The $i$-th derivative of a bounded-smooth function is the depth-two
quotient evaluated on the diagonal — and by separation this does
not depend on the tower, so it descends through the propositional
truncation.

```agda
∂-of : ∀ {n} (f : Fun n) (i : Fin n) → Smooth⁺ n f → Fun n
∂-of f i (S , _ , _) x = S 2 i .fst (cons (x i) x)

∂-unique
  : ∀ {n} (f : Fun n) (i : Fin n) (A B : Smooth⁺ n f)
  → ∂-of f i A ≡ ∂-of f i B
∂-unique f i (S , _ , BT) (S' , _ , BT') = funext λ x →
  quot-agree f i (S 2 i .fst) (S' 2 i .fst)
    (S 2 i .snd .fst) (S' 2 i .snd .fst)
    (S 2 i .snd .snd fzero .fst) (S' 2 i .snd .snd fzero .fst)
    (S 2 i .snd .snd fzero .snd .fst) (S' 2 i .snd .snd fzero .snd .fst)
    (BT 2 i .snd fzero .fst) (BT' 2 i .snd fzero .fst)
    (x i) x

∂ᴿ : ∀ {n} (f : Fun n) (i : Fin n) → ∥ Smooth⁺ n f ∥ → Fun n
∂ᴿ f i = ∥-∥-rec-set (Π-is-hlevel 2 λ _ → ℝ-is-set)
  (∂-of f i) (∂-unique f i)
```
