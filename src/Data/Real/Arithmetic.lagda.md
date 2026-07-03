<!--
```agda
open import 1Lab.Truncation
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Base
open import Data.Sum
open import Data.Dec
open import Data.Nat.Base using (Nat ; zero ; suc)

import Data.Nat.Base as Nat
import Data.Nat.Order as Nat
import Data.Nat.Properties as Nat
import Data.Int.Order as ℤ
import Data.Int.Properties as ℤ
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Real.Arithmetic where
```

# Arithmetic of real numbers {defines="real-addition"}

Having constructed the Dedekind reals as [[located|dedekind-cut]] cuts
of the rationals, we now equip them with arithmetic. The rationals
already form a field; what the reals need is the **archimedean
property** — every rational is bounded by a natural number — which
powers the one genuinely analytic step in the whole development: the
locatedness of the sum of two cuts.

## Private rational toolkit

The 1Lab's interface to `Ratio`{.Agda} does not (yet) expose
strict-order arithmetic, halving, or the archimedean property. We
rebuild the small toolkit of [[dedekind-real|Data.Real.Base]] here
privately, since it is not exported from that module.

<!--
```agda
private instance
  2-nonzero : Nonzero 2
  2-nonzero = inc (λ p → <-irrefl (sym p) 0<2) where
    0<2 : 0 < 2
    0<2 = decide!

private
  half : Ratio → Ratio
  half x = x *ℚ invℚ 2

  midpoint : Ratio → Ratio → Ratio
  midpoint x y = half (x +ℚ y)

private abstract
  ¬<→≥ : ∀ {x y} → ¬ x < y → y ≤ x
  ¬<→≥ {x} {y} ¬p with holds? (y ≤ x)
  ... | yes p = p
  ... | no ¬q with ≤-strengthen (≤-is-weakly-total y x ¬q)
  ... | inl e = subst (_≤ x) e ≤-refl
  ... | inr q = absurd (¬p q)

  <-cotrans : ∀ {x z} (y : Ratio) → x < z → (x < y) ⊎ (y < z)
  <-cotrans {x} {z} y p with holds? (x < y)
  ... | yes q = inl q
  ... | no ¬q = inr (≤-<-trans (¬<→≥ ¬q) p)

  +ℚ-cancelr : ∀ {x y} a → x +ℚ a ≡ y +ℚ a → x ≡ y
  +ℚ-cancelr {x} {y} a p =
    x                   ≡˘⟨ +ℚ-idr x ⟩
    x +ℚ 0              ≡˘⟨ ap (x +ℚ_) (+ℚ-invr a) ⟩
    x +ℚ (a +ℚ (-ℚ a))  ≡⟨ +ℚ-associative x a (-ℚ a) ⟩
    (x +ℚ a) +ℚ (-ℚ a)  ≡⟨ ap (_+ℚ (-ℚ a)) p ⟩
    (y +ℚ a) +ℚ (-ℚ a)  ≡˘⟨ +ℚ-associative y a (-ℚ a) ⟩
    y +ℚ (a +ℚ (-ℚ a))  ≡⟨ ap (y +ℚ_) (+ℚ-invr a) ⟩
    y +ℚ 0              ≡⟨ +ℚ-idr y ⟩
    y                   ∎

  +ℚ-preserves-<r : ∀ {x y} a → x < y → x +ℚ a < y +ℚ a
  +ℚ-preserves-<r a p = <-from-≤
    (+ℚ-preserves-≤ (<-weaken p) ≤-refl)
    (λ e → <-irrefl (+ℚ-cancelr a e) p)

  +ℚ-preserves-<l : ∀ {x y} a → x < y → a +ℚ x < a +ℚ y
  +ℚ-preserves-<l {x} {y} a p =
    transport (λ i → +ℚ-commutative x a i < +ℚ-commutative y a i)
      (+ℚ-preserves-<r a p)

  negℚ-invol : ∀ q → -ℚ (-ℚ q) ≡ q
  negℚ-invol q = +ℚ-cancelr (-ℚ q) $
    (-ℚ (-ℚ q)) +ℚ (-ℚ q)  ≡⟨ +ℚ-commutative _ _ ⟩
    (-ℚ q) +ℚ (-ℚ (-ℚ q))  ≡⟨ +ℚ-invr (-ℚ q) ⟩
    0                      ≡˘⟨ +ℚ-invr q ⟩
    q +ℚ (-ℚ q)            ∎

  x+x≡x*2 : ∀ x → x +ℚ x ≡ x *ℚ 2
  x+x≡x*2 x = sym $
    x *ℚ 2               ≡⟨ ap (x *ℚ_) two ⟩
    x *ℚ (1 +ℚ 1)        ≡⟨ *ℚ-distribl x 1 1 ⟩
    (x *ℚ 1) +ℚ (x *ℚ 1) ≡⟨ ap₂ _+ℚ_ (*ℚ-idr x) (*ℚ-idr x) ⟩
    x +ℚ x               ∎
    where
    two : Path Ratio 2 (1 +ℚ 1)
    two = decide!

  half-double : ∀ x → half (x +ℚ x) ≡ x
  half-double x =
      ap (_*ℚ invℚ 2) (x+x≡x*2 x)
    ∙ sym (*ℚ-associative x 2 (invℚ 2))
    ∙ ap (x *ℚ_) (*ℚ-invr {2} {2-nonzero})
    ∙ *ℚ-idr x

  half-sum : ∀ x → half x +ℚ half x ≡ x
  half-sum x =
      x+x≡x*2 (half x)
    ∙ sym (*ℚ-associative x (invℚ 2) 2)
    ∙ ap (x *ℚ_) (*ℚ-commutative (invℚ 2) 2 ∙ *ℚ-invr {2} {2-nonzero})
    ∙ *ℚ-idr x

  half-< : ∀ {x y} → x < y → half x < half y
  half-< {x} {y} p with holds? (half x < half y)
  ... | yes q = q
  ... | no ¬q = absurd (<-irrefl refl (≤-<-trans y≤x p)) where
    y≤x : y ≤ x
    y≤x = transport (λ i → half-sum y i ≤ half-sum x i)
      (+ℚ-preserves-≤ (¬<→≥ ¬q) (¬<→≥ ¬q))

  mid-<l : ∀ {x y} → x < y → x < midpoint x y
  mid-<l {x} {y} p = transport
    (λ i → half-double x i < midpoint x y)
    (half-< (+ℚ-preserves-<l x p))

  mid-<r : ∀ {x y} → x < y → midpoint x y < y
  mid-<r {x} {y} p = transport
    (λ i → midpoint x y < half-double y i)
    (half-< (+ℚ-preserves-<r y p))

  <→positive-diff : ∀ {x y} → x < y → 0 < y +ℚ (-ℚ x)
  <→positive-diff {x} {y} p = transport
    (λ i → +ℚ-invr x i < y +ℚ (-ℚ x))
    (+ℚ-preserves-<r (-ℚ x) p)

  positive-diff→< : ∀ {x y} → 0 < y +ℚ (-ℚ x) → x < y
  positive-diff→< {x} {y} p = transport (λ i → lhs i < rhs i) step
    where
    step : x +ℚ 0 < x +ℚ (y +ℚ (-ℚ x))
    step = +ℚ-preserves-<l x p

    lhs : x +ℚ 0 ≡ x
    lhs = +ℚ-idr x

    rhs : x +ℚ (y +ℚ (-ℚ x)) ≡ y
    rhs =
      x +ℚ (y +ℚ (-ℚ x))   ≡⟨ ap (x +ℚ_) (+ℚ-commutative y (-ℚ x)) ⟩
      x +ℚ ((-ℚ x) +ℚ y)   ≡⟨ +ℚ-associative x (-ℚ x) y ⟩
      (x +ℚ (-ℚ x)) +ℚ y   ≡⟨ ap (_+ℚ y) (+ℚ-invr x) ⟩
      0 +ℚ y               ≡⟨ +ℚ-idl y ⟩
      y                    ∎

  negatel : ∀ a b → (-ℚ a) *ℚ b ≡ -ℚ (a *ℚ b)
  negatel a b = +ℚ-cancelr (a *ℚ b)
    ( (-ℚ a) *ℚ b +ℚ a *ℚ b   ≡˘⟨ *ℚ-distribr b (-ℚ a) a ⟩
      ((-ℚ a) +ℚ a) *ℚ b      ≡⟨ ap (_*ℚ b) (+ℚ-invl a) ⟩
      0 *ℚ b                  ≡⟨ *ℚ-zerol b ⟩
      0                       ≡˘⟨ +ℚ-invl (a *ℚ b) ⟩
      (-ℚ (a *ℚ b)) +ℚ a *ℚ b ∎)

  half-pos : ∀ {ε} → 0 < ε → 0 < half ε
  half-pos {ε} p = transport (λ i → half-zero i < half ε) (half-< p)
    where
    half-zero : half 0 ≡ 0
    half-zero = ap (_*ℚ invℚ 2) (sym (*ℚ-zerol 1)) ∙ sym (*ℚ-associative 0 1 (invℚ 2)) ∙ *ℚ-zerol (1 *ℚ invℚ 2)

  half-lt : ∀ {ε} → 0 < ε → half ε < ε
  half-lt {ε} p = transport (λ i → +ℚ-idl (half ε) i < half-sum ε i)
    (+ℚ-preserves-<r (half ε) (half-pos p))

  *ℚ-preserves-<r : ∀ {u v w} → u < v → 0 < w → (u *ℚ w) < (v *ℚ w)
  *ℚ-preserves-<r {u} {v} {w} p q = positive-diff→< (transport (λ i → 0 < expand i) diff-pos)
    where
    diff-pos : 0 < (v +ℚ (-ℚ u)) *ℚ w
    diff-pos = from-positive (*ℚ-positive (to-positive (<→positive-diff p)) (to-positive q))

    expand : (v +ℚ (-ℚ u)) *ℚ w ≡ (v *ℚ w) +ℚ (-ℚ (u *ℚ w))
    expand = *ℚ-distribr w v (-ℚ u) ∙ ap (v *ℚ w +ℚ_) (negatel u w)
```
-->

## The archimedean property

Every rational is bounded above by some natural number, embedded into
$\bQ$ through the integers.

```agda
nℚ : Nat → Ratio
nℚ n = ℤ.pos n / 1
```

<!--
```agda
private abstract
  nℚ-suc : ∀ n → nℚ (suc n) ≡ 1 +ℚ nℚ n
  nℚ-suc n =
    ℤ.pos (suc n) / 1        ≡˘⟨ ap (_/ 1) one+pos ⟩
    (1 ℤ.+ℤ ℤ.pos n) / 1     ≡˘⟨ +ℚ-common-denom 1 1 (ℤ.pos n) ⟩
    (1 / 1) +ℚ (ℤ.pos n / 1) ∎
    where
    one+pos : (1 ℤ.+ℤ ℤ.pos n) ≡ ℤ.pos (suc n)
    one+pos = refl
```
-->

The proof that every rational lies below some natural number goes
through a fraction $x/s$: since $s$ is positive (hence $s \ge 1$), we
have $x \le \abs x < \suc(\abs x) \le \suc(\abs x) \cdot s$, and this
last inequality is precisely $q < \nQ(\suc(\abs x))$ unfolded at the
level of fractions.

```agda
bound-above : ∀ q → ∥ Σ Nat (λ n → q < nℚ n) ∥
```

<!--
```agda
private abstract
  x≤abs : ∀ (x : ℤ.Int) → x ℤ.≤ ℤ.pos (ℤ.abs x)
  x≤abs (ℤ.pos m)    = ℤ.≤-refl
  x≤abs (ℤ.negsuc m) = ℤ.<-weaken ℤ.neg<pos

  s≥1 : ∀ {s} → ℤ.Positive s → (1 ℤ.≤ s)
  s≥1 (ℤ.pos m) = ℤ.pos≤pos (Nat.s≤s Nat.0≤x)

  abs<suc-abs : ∀ (x : ℤ.Int) → ℤ.pos (ℤ.abs x) ℤ.< ℤ.pos (suc (ℤ.abs x))
  abs<suc-abs x = ℤ.pos<pos Nat.≤-refl

  suc-abs≤suc-abs*s
    : ∀ (x : ℤ.Int) {s : ℤ.Int} (p : ℤ.Positive s)
    → ℤ.pos (suc (ℤ.abs x)) ℤ.≤ (ℤ.pos (suc (ℤ.abs x)) ℤ.*ℤ s)
  suc-abs≤suc-abs*s x {s} p = ℤ.≤-trans
    (ℤ.≤-refl' (sym (ℤ.*ℤ-oner (ℤ.pos (suc (ℤ.abs x))))))
    (ℤ.≤-trans
      (ℤ.≤-refl' (ℤ.*ℤ-commutative (ℤ.pos (suc (ℤ.abs x))) 1))
      (ℤ.≤-trans
        (ℤ.*ℤ-preserves-≤r {1} {s} (ℤ.pos (suc (ℤ.abs x))) (s≥1 p))
        (ℤ.≤-refl' (ℤ.*ℤ-commutative s (ℤ.pos (suc (ℤ.abs x)))))))

  bound-reduce
    : ∀ (x : ℤ.Int) {s} (p : ℤ.Positive s)
    → (x ℤ.*ℤ 1) ℤ.< (ℤ.pos (suc (ℤ.abs x)) ℤ.*ℤ s)
  bound-reduce x {s} p = subst (λ z → z ℤ.< (ℤ.pos (suc (ℤ.abs x)) ℤ.*ℤ s)) (sym (ℤ.*ℤ-oner x))
    (ℤ.≤-<-trans (x≤abs x) (ℤ.<-≤-trans (abs<suc-abs x) (suc-abs≤suc-abs*s x p)))

bound-above = ℚ-elim-prop (λ _ → squash) go
  where
  go : ∀ f → ∥ Σ Nat (λ n → toℚ f < nℚ n) ∥
  go (x / s [ p ]) = inc (suc (ℤ.abs x) , toℚ< (bound-reduce x p))
```

