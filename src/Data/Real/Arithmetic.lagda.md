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
-->

From boundedness above, the full archimedean property follows: given a
positive step $\varepsilon$, any gap between two rationals $a \le b$
can be crossed by finitely many steps of size $\varepsilon$ starting
from $a$.

```agda
archimedean
  : ∀ a b ε → 0 < ε
  → ∥ Σ Nat (λ n → b < a +ℚ nℚ n *ℚ ε) ∥
```

<!--
```agda
private abstract
  /ℚ-cancel : ∀ x y ⦃ p : Nonzero y ⦄ → (x /ℚ y) *ℚ y ≡ x
  /ℚ-cancel x y = ap (_*ℚ y) /ℚ-def ∙ sym (*ℚ-associative x (invℚ y) y) ∙ ap (x *ℚ_) *ℚ-invl ∙ *ℚ-idr x

archimedean a b ε 0<ε = ∥-∥-map bound (bound-above ((b +ℚ (-ℚ a)) /ℚ ε))
  where
  instance
    ε-nonzero : Nonzero ε
    ε-nonzero = inc (positive→nonzero (to-positive 0<ε))

  bound : Σ Nat (λ n → ((b +ℚ (-ℚ a)) /ℚ ε) < nℚ n) → Σ Nat (λ n → b < a +ℚ nℚ n *ℚ ε)
  bound (n , p) = n , positive-diff→< (transport (λ i → 0 < step i) diff-pos)
    where
    diff-pos : 0 < (nℚ n +ℚ (-ℚ ((b +ℚ (-ℚ a)) /ℚ ε))) *ℚ ε
    diff-pos = from-positive (*ℚ-positive (to-positive (<→positive-diff p)) (to-positive 0<ε))

    step
      : (nℚ n +ℚ (-ℚ ((b +ℚ (-ℚ a)) /ℚ ε))) *ℚ ε
      ≡ (a +ℚ nℚ n *ℚ ε) +ℚ (-ℚ b)
    step =
      (nℚ n +ℚ (-ℚ ((b +ℚ (-ℚ a)) /ℚ ε))) *ℚ ε
        ≡⟨ *ℚ-distribr ε (nℚ n) (-ℚ ((b +ℚ (-ℚ a)) /ℚ ε)) ⟩
      nℚ n *ℚ ε +ℚ (-ℚ ((b +ℚ (-ℚ a)) /ℚ ε)) *ℚ ε
        ≡⟨ ap (nℚ n *ℚ ε +ℚ_) (negatel ((b +ℚ (-ℚ a)) /ℚ ε) ε) ⟩
      nℚ n *ℚ ε +ℚ (-ℚ (((b +ℚ (-ℚ a)) /ℚ ε) *ℚ ε))
        ≡⟨ ap (λ e → nℚ n *ℚ ε +ℚ (-ℚ e)) (/ℚ-cancel (b +ℚ (-ℚ a)) ε) ⟩
      nℚ n *ℚ ε +ℚ (-ℚ (b +ℚ (-ℚ a)))
        ≡⟨ ap (nℚ n *ℚ ε +ℚ_) (negate-diff b (-ℚ a) ∙ ap ((-ℚ b) +ℚ_) (negℚ-invol a)) ⟩
      nℚ n *ℚ ε +ℚ ((-ℚ b) +ℚ a)
        ≡⟨ ap (nℚ n *ℚ ε +ℚ_) (+ℚ-commutative (-ℚ b) a) ⟩
      nℚ n *ℚ ε +ℚ (a +ℚ (-ℚ b))
        ≡⟨ +ℚ-associative (nℚ n *ℚ ε) a (-ℚ b) ⟩
      (nℚ n *ℚ ε +ℚ a) +ℚ (-ℚ b)
        ≡⟨ ap (_+ℚ (-ℚ b)) (+ℚ-commutative (nℚ n *ℚ ε) a) ⟩
      (a +ℚ nℚ n *ℚ ε) +ℚ (-ℚ b) ∎
      where
      negate-diff : ∀ u v → -ℚ (u +ℚ v) ≡ (-ℚ u) +ℚ (-ℚ v)
      negate-diff u v = +ℚ-cancelr (u +ℚ v)
        ( (-ℚ (u +ℚ v)) +ℚ (u +ℚ v)               ≡⟨ +ℚ-invl (u +ℚ v) ⟩
          0                                        ≡˘⟨ +ℚ-invl u ⟩
          (-ℚ u) +ℚ u                              ≡˘⟨ ap ((-ℚ u) +ℚ_) (+ℚ-idl u) ⟩
          (-ℚ u) +ℚ (0 +ℚ u)                       ≡˘⟨ ap (λ e → (-ℚ u) +ℚ (e +ℚ u)) (+ℚ-invl v) ⟩
          (-ℚ u) +ℚ (((-ℚ v) +ℚ v) +ℚ u)           ≡⟨ ap ((-ℚ u) +ℚ_) (sym (+ℚ-associative (-ℚ v) v u)) ⟩
          (-ℚ u) +ℚ ((-ℚ v) +ℚ (v +ℚ u))           ≡⟨ +ℚ-associative (-ℚ u) (-ℚ v) (v +ℚ u) ⟩
          ((-ℚ u) +ℚ (-ℚ v)) +ℚ (v +ℚ u)           ≡⟨ ap (((-ℚ u) +ℚ (-ℚ v)) +ℚ_) (+ℚ-commutative v u) ⟩
          ((-ℚ u) +ℚ (-ℚ v)) +ℚ (u +ℚ v)           ∎)
```
-->

## Approximation within $\varepsilon$

The archimedean property lets us find, for a real number $x$ and any
positive rational slack $\varepsilon$, rationals $u$ in the lower cut
and $v$ in the upper cut with $v - u < \varepsilon$: a finite search
along an arithmetic progression, climbing from a starting point in the
lower cut in steps of size $\tfrac{1}{4}\varepsilon$ until locatedness
forces the upper cut to be hit.

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
```
-->

```agda
approx
  : (x : ℝ) (ε : Ratio) → 0 < ε
  → ∥ Σ Ratio (λ u → Σ Ratio (λ v →
      ∣ x .lower u ∣ × ∣ x .upper v ∣ × ((v +ℚ (-ℚ u)) < ε))) ∥
```

<!--
```agda
private abstract
  nℚ-zero : nℚ zero ≡ 0
  nℚ-zero = refl

  ring-lemma-climb
    : ∀ u h n → (u +ℚ h) +ℚ nℚ n *ℚ h ≡ u +ℚ nℚ (suc n) *ℚ h
  ring-lemma-climb u h n =
    (u +ℚ h) +ℚ nℚ n *ℚ h      ≡˘⟨ +ℚ-associative u h (nℚ n *ℚ h) ⟩
    u +ℚ (h +ℚ nℚ n *ℚ h)      ≡˘⟨ ap (λ e → u +ℚ (e +ℚ nℚ n *ℚ h)) (*ℚ-idl h) ⟩
    u +ℚ (1 *ℚ h +ℚ nℚ n *ℚ h) ≡˘⟨ ap (u +ℚ_) (*ℚ-distribr h 1 (nℚ n)) ⟩
    u +ℚ (1 +ℚ nℚ n) *ℚ h      ≡˘⟨ ap (λ e → u +ℚ e *ℚ h) (nℚ-suc n) ⟩
    u +ℚ nℚ (suc n) *ℚ h       ∎

  gap-lemma
    : ∀ u h → ((u +ℚ h) +ℚ h) +ℚ (-ℚ u) ≡ h +ℚ h
  gap-lemma u h = +ℚ-cancelr u
    ( (((u +ℚ h) +ℚ h) +ℚ (-ℚ u)) +ℚ u ≡⟨ sym (+ℚ-associative ((u +ℚ h) +ℚ h) (-ℚ u) u) ⟩
      ((u +ℚ h) +ℚ h) +ℚ ((-ℚ u) +ℚ u) ≡⟨ ap (((u +ℚ h) +ℚ h) +ℚ_) (+ℚ-invl u) ⟩
      ((u +ℚ h) +ℚ h) +ℚ 0             ≡⟨ +ℚ-idr _ ⟩
      (u +ℚ h) +ℚ h                    ≡˘⟨ +ℚ-associative u h h ⟩
      u +ℚ (h +ℚ h)                    ≡⟨ +ℚ-commutative u (h +ℚ h) ⟩
      (h +ℚ h) +ℚ u ∎)

approx x ε 0<ε = do
  (a , la) ← cut.lower-inhab x
  (b , ub) ← cut.upper-inhab x
  (n , bnd) ← archimedean a b h h-pos
  climb b ub n a la bnd
  where
  h : Ratio
  h = half (half ε)

  h-pos : 0 < h
  h-pos = half-pos (half-pos 0<ε)

  hh<ε : h +ℚ h < ε
  hh<ε = transport (λ i → half-sum (half ε) (~ i) < ε) (half-lt 0<ε)

  climb
    : ∀ b → ∣ x .upper b ∣
    → ∀ n u → ∣ x .lower u ∣ → b < u +ℚ nℚ n *ℚ h
    → ∥ Σ Ratio (λ u' → Σ Ratio (λ v →
        ∣ x .lower u' ∣ × ∣ x .upper v ∣ × ((v +ℚ (-ℚ u')) < ε))) ∥
  climb b ub zero u lu bnd = absurd (<-irrefl refl (<-trans u<b b<u))
    where
    zero-lemma : u +ℚ nℚ zero *ℚ h ≡ u
    zero-lemma = ap (u +ℚ_) (ap (_*ℚ h) nℚ-zero ∙ *ℚ-zerol h) ∙ +ℚ-idr u

    b<u : b < u
    b<u = transport (λ i → b < zero-lemma i) bnd

    u<b : u < b
    u<b = lower<upper x lu ub
  climb b ub (suc m) u lu bnd = ∥-∥-rec squash cases (cut.cut-located x {u +ℚ h} {(u +ℚ h) +ℚ h} step-<)
    where
    step-< : u +ℚ h < (u +ℚ h) +ℚ h
    step-< = transport (λ i → +ℚ-idr (u +ℚ h) i < (u +ℚ h) +ℚ h) (+ℚ-preserves-<l (u +ℚ h) h-pos)

    cases
      : ∣ x .lower (u +ℚ h) ∣ ⊎ ∣ x .upper ((u +ℚ h) +ℚ h) ∣
      → ∥ Σ Ratio (λ u' → Σ Ratio (λ v →
          ∣ x .lower u' ∣ × ∣ x .upper v ∣ × ((v +ℚ (-ℚ u')) < ε))) ∥
    cases (inl l') = climb b ub m (u +ℚ h) l' bnd'
      where
      bnd' : b < (u +ℚ h) +ℚ nℚ m *ℚ h
      bnd' = transport (λ i → b < ring-lemma-climb u h m (~ i)) bnd
    cases (inr u') = inc (u , (u +ℚ h) +ℚ h , lu , u' , gap)
      where
      gap : ((u +ℚ h) +ℚ h) +ℚ (-ℚ u) < ε
      gap = subst (_< ε) (sym (gap-lemma u h)) hh<ε
```
-->

## Addition

Addition of Dedekind cuts is Minkowski addition: the lower cut of
$x + y$ consists of the rationals strictly below some sum of a
witness from $x$'s lower cut and one from $y$'s, and dually for the
upper cut. Downward/upward closure and roundedness follow from the
existence of a midpoint; disjointness and locatedness are where the
[[approximation|approx]] lemma above is spent.

<!--
```agda
private abstract
  <-sum : ∀ {p q r s} → p < q → r < s → p +ℚ r < q +ℚ s
  <-sum {p} {q} {r} {s} p<q r<s = <-trans (+ℚ-preserves-<r r p<q) (+ℚ-preserves-<l q r<s)

  +ℚ-swap-inner : ∀ a b c d → (a +ℚ b) +ℚ (c +ℚ d) ≡ (a +ℚ c) +ℚ (b +ℚ d)
  +ℚ-swap-inner a b c d =
    (a +ℚ b) +ℚ (c +ℚ d)   ≡˘⟨ +ℚ-associative a b (c +ℚ d) ⟩
    a +ℚ (b +ℚ (c +ℚ d))   ≡⟨ ap (a +ℚ_) (+ℚ-associative b c d) ⟩
    a +ℚ ((b +ℚ c) +ℚ d)   ≡⟨ ap (λ e → a +ℚ (e +ℚ d)) (+ℚ-commutative b c) ⟩
    a +ℚ ((c +ℚ b) +ℚ d)   ≡˘⟨ ap (a +ℚ_) (+ℚ-associative c b d) ⟩
    a +ℚ (c +ℚ (b +ℚ d))   ≡⟨ +ℚ-associative a c (b +ℚ d) ⟩
    (a +ℚ c) +ℚ (b +ℚ d)   ∎

  q+[r-q]≡r : ∀ q r → q +ℚ (r +ℚ (-ℚ q)) ≡ r
  q+[r-q]≡r q r =
    q +ℚ (r +ℚ (-ℚ q))   ≡⟨ ap (q +ℚ_) (+ℚ-commutative r (-ℚ q)) ⟩
    q +ℚ ((-ℚ q) +ℚ r)   ≡⟨ +ℚ-associative q (-ℚ q) r ⟩
    (q +ℚ (-ℚ q)) +ℚ r   ≡⟨ ap (_+ℚ r) (+ℚ-invr q) ⟩
    0 +ℚ r               ≡⟨ +ℚ-idl r ⟩
    r                    ∎

  diff-swap : ∀ v v' u u' → (v +ℚ (-ℚ u)) +ℚ (v' +ℚ (-ℚ u')) ≡ (v +ℚ v') +ℚ (-ℚ (u +ℚ u'))
  diff-swap v v' u u' =
    (v +ℚ (-ℚ u)) +ℚ (v' +ℚ (-ℚ u'))   ≡⟨ +ℚ-swap-inner v (-ℚ u) v' (-ℚ u') ⟩
    (v +ℚ v') +ℚ ((-ℚ u) +ℚ (-ℚ u'))   ≡˘⟨ ap ((v +ℚ v') +ℚ_) negsum ⟩
    (v +ℚ v') +ℚ (-ℚ (u +ℚ u'))        ∎
    where
    negsum : -ℚ (u +ℚ u') ≡ (-ℚ u) +ℚ (-ℚ u')
    negsum = +ℚ-cancelr (u +ℚ u')
      ( (-ℚ (u +ℚ u')) +ℚ (u +ℚ u')             ≡⟨ +ℚ-invl (u +ℚ u') ⟩
        0                                        ≡˘⟨ +ℚ-invl u ⟩
        (-ℚ u) +ℚ u                              ≡˘⟨ ap ((-ℚ u) +ℚ_) (+ℚ-idl u) ⟩
        (-ℚ u) +ℚ (0 +ℚ u)                       ≡˘⟨ ap (λ e → (-ℚ u) +ℚ (e +ℚ u)) (+ℚ-invl u') ⟩
        (-ℚ u) +ℚ (((-ℚ u') +ℚ u') +ℚ u)         ≡⟨ ap ((-ℚ u) +ℚ_) (sym (+ℚ-associative (-ℚ u') u' u)) ⟩
        (-ℚ u) +ℚ ((-ℚ u') +ℚ (u' +ℚ u))         ≡⟨ +ℚ-associative (-ℚ u) (-ℚ u') (u' +ℚ u) ⟩
        ((-ℚ u) +ℚ (-ℚ u')) +ℚ (u' +ℚ u)         ≡⟨ ap (((-ℚ u) +ℚ (-ℚ u')) +ℚ_) (+ℚ-commutative u' u) ⟩
        ((-ℚ u) +ℚ (-ℚ u')) +ℚ (u +ℚ u')         ∎)

  located-lemma
    : ∀ q r → q < r → ∀ u v u' v' → (u +ℚ u') ≤ q
    → (v +ℚ (-ℚ u)) < half (half (r +ℚ (-ℚ q)))
    → (v' +ℚ (-ℚ u')) < half (half (r +ℚ (-ℚ q)))
    → (v +ℚ v') < r
  located-lemma q r q<r u v u' v' uu'≤q gapx gapy =
    subst (v +ℚ v' <_) (q+[r-q]≡r q r) vv'<q+[r-q]
    where
    ε : Ratio
    ε = half (half (r +ℚ (-ℚ q)))

    diffs<εε : ((v +ℚ v') +ℚ (-ℚ (u +ℚ u'))) < (ε +ℚ ε)
    diffs<εε = subst (_< (ε +ℚ ε)) (diff-swap v v' u u') (<-sum gapx gapy)

    vv'<uu'+εε : (v +ℚ v') < (u +ℚ u') +ℚ (ε +ℚ ε)
    vv'<uu'+εε = transport (λ i → lhs i < rhs i) (+ℚ-preserves-<r (u +ℚ u') diffs<εε)
      where
      lhs : ((v +ℚ v') +ℚ (-ℚ (u +ℚ u'))) +ℚ (u +ℚ u') ≡ v +ℚ v'
      lhs =
        ((v +ℚ v') +ℚ (-ℚ (u +ℚ u'))) +ℚ (u +ℚ u')  ≡˘⟨ +ℚ-associative (v +ℚ v') (-ℚ (u +ℚ u')) (u +ℚ u') ⟩
        (v +ℚ v') +ℚ ((-ℚ (u +ℚ u')) +ℚ (u +ℚ u'))  ≡⟨ ap ((v +ℚ v') +ℚ_) (+ℚ-invl (u +ℚ u')) ⟩
        (v +ℚ v') +ℚ 0                              ≡⟨ +ℚ-idr (v +ℚ v') ⟩
        v +ℚ v'                                     ∎

      rhs : (ε +ℚ ε) +ℚ (u +ℚ u') ≡ (u +ℚ u') +ℚ (ε +ℚ ε)
      rhs = +ℚ-commutative (ε +ℚ ε) (u +ℚ u')

    uu'+εε≤q+εε : ((u +ℚ u') +ℚ (ε +ℚ ε)) ≤ (q +ℚ (ε +ℚ ε))
    uu'+εε≤q+εε = +ℚ-preserves-≤ uu'≤q ≤-refl

    vv'<q+εε : (v +ℚ v') < q +ℚ (ε +ℚ ε)
    vv'<q+εε = <-≤-trans vv'<uu'+εε uu'+εε≤q+εε

    εε<r-q : (ε +ℚ ε) < (r +ℚ (-ℚ q))
    εε<r-q = transport (λ i → half-sum (half (r +ℚ (-ℚ q))) (~ i) < (r +ℚ (-ℚ q)))
      (half-lt (<→positive-diff q<r))

    vv'<q+[r-q] : (v +ℚ v') < q +ℚ (r +ℚ (-ℚ q))
    vv'<q+[r-q] = <-trans vv'<q+εε (+ℚ-preserves-<l q εε<r-q)

  sum-minus-one< : ∀ r s → (r +ℚ s) +ℚ (-ℚ 1) < r +ℚ s
  sum-minus-one< r s = subst ((r +ℚ s) +ℚ (-ℚ 1) <_) (+ℚ-idr (r +ℚ s)) (+ℚ-preserves-<l (r +ℚ s) neg1<0)
    where
    neg1<0 : -ℚ 1 < 0
    neg1<0 = decide!

  sum<sum-plus-one : ∀ v w → v +ℚ w < (v +ℚ w) +ℚ 1
  sum<sum-plus-one v w = subst (_< (v +ℚ w) +ℚ 1) (+ℚ-idr (v +ℚ w)) (+ℚ-preserves-<l (v +ℚ w) 0<1)
    where
    0<1 : 0 < 1
    0<1 = decide!
```
-->

```agda
_+ᴿ_ : ℝ → ℝ → ℝ
(x +ᴿ y) .lower q = elΩ (Σ Ratio λ r → Σ Ratio λ s →
  ∣ x .lower r ∣ × ∣ y .lower s ∣ × (q < r +ℚ s))
(x +ᴿ y) .upper q = elΩ (Σ Ratio λ v → Σ Ratio λ w →
  ∣ x .upper v ∣ × ∣ y .upper w ∣ × (v +ℚ w < q))
```

<!--
```agda
(x +ᴿ y) .has-is-cut = record
  { lower-inhab = ∥-∥-map₂
      (λ (r , lr) (s , ls) →
        (r +ℚ s) +ℚ (-ℚ 1) , inc (r , s , lr , ls , sum-minus-one< r s))
      (cut.lower-inhab x) (cut.lower-inhab y)
  ; upper-inhab = ∥-∥-map₂
      (λ (v , uv) (w , uw) →
        (v +ℚ w) +ℚ 1 , inc (v , w , uv , uw , sum<sum-plus-one v w))
      (cut.upper-inhab x) (cut.upper-inhab y)
  ; lower-round = λ q lq → □-tr lq >>= λ (r , s , lr , ls , q<rs) →
      inc (midpoint q (r +ℚ s) , mid-<l q<rs ,
           inc (r , s , lr , ls , mid-<r q<rs))
  ; lower-close = λ q<q' lq' → □-elim (λ _ → hlevel 1)
      (λ (r , s , lr , ls , q'<rs) → inc (r , s , lr , ls , <-trans q<q' q'<rs))
      lq'
  ; upper-round = λ r ur → □-tr ur >>= λ (v , w , uv , uw , vw<r) →
      inc (midpoint (v +ℚ w) r , mid-<r vw<r ,
           inc (v , w , uv , uw , mid-<l vw<r))
  ; upper-close = λ q<r uq → □-elim (λ _ → hlevel 1)
      (λ (v , w , uv , uw , vw<q) → inc (v , w , uv , uw , <-trans vw<q q<r))
      uq
  ; cut-disjoint = λ q lq uq → □-elim (λ _ → hlevel 1)
      (λ (r , s , lr , ls , q<rs) → □-elim (λ _ → hlevel 1)
        (λ (v , w , uv , uw , vw<q) →
          <-irrefl refl (<-trans (<-sum (lower<upper x lr uv) (lower<upper y ls uw))
                                  (<-trans vw<q q<rs)))
        uq)
      lq
  ; cut-located = λ {q} {r} q<r → do
      (u  , v  , lu  , uv  , gapx) ← approx x (half (half (r +ℚ (-ℚ q))))
          (half-pos (half-pos (<→positive-diff q<r)))
      (u' , v' , lu' , uv' , gapy) ← approx y (half (half (r +ℚ (-ℚ q))))
          (half-pos (half-pos (<→positive-diff q<r)))
      decide-side q r q<r u v lu uv gapx u' v' lu' uv' gapy
  }
  where
  decide-side
    : ∀ q r → q < r → ∀ u v → ∣ x .lower u ∣ → ∣ x .upper v ∣ → (v +ℚ (-ℚ u)) < half (half (r +ℚ (-ℚ q)))
    → ∀ u' v' → ∣ y .lower u' ∣ → ∣ y .upper v' ∣ → (v' +ℚ (-ℚ u')) < half (half (r +ℚ (-ℚ q)))
    → ∥ ∣ (x +ᴿ y) .lower q ∣ ⊎ ∣ (x +ᴿ y) .upper r ∣ ∥
  decide-side q r q<r u v lu uv gapx u' v' lu' uv' gapy with holds? (q < u +ℚ u')
  ... | yes q<uu' = inc (inl (inc (u , u' , lu , lu' , q<uu')))
  ... | no ¬q<uu' = inc (inr (inc (v , v' , uv , uv' ,
      located-lemma q r q<r u v u' v' (¬<→≥ ¬q<uu') gapx gapy)))
```
-->

## Additive laws

The additive identity is the embedded rational zero.

```agda
0ᴿ : ℝ
0ᴿ = ratℝ 0
```

Commutativity holds because the defining conditions of $x + y$ and $y +
x$ are literally the same up to swapping witnesses and commuting their
sum in $\bQ$.

```agda
+ᴿ-comm : ∀ x y → x +ᴿ y ≡ y +ᴿ x
```

<!--
```agda
+ᴿ-comm x y = ℝ-path
  (funext λ q → Ω-ua (swap-lower x y) (swap-lower y x))
  (funext λ q → Ω-ua (swap-upper x y) (swap-upper y x))
  where
  swap-lower
    : ∀ x y {q} → ∣ (x +ᴿ y) .lower q ∣ → ∣ (y +ᴿ x) .lower q ∣
  swap-lower x y {q} = □-map λ (r , s , lr , ls , q<rs) →
    s , r , ls , lr , subst (q <_) (+ℚ-commutative r s) q<rs

  swap-upper
    : ∀ x y {q} → ∣ (x +ᴿ y) .upper q ∣ → ∣ (y +ᴿ x) .upper q ∣
  swap-upper x y {q} = □-map λ (v , w , uv , uw , vw<q) →
    w , v , uw , uv , subst (_< q) (+ℚ-commutative v w) vw<q
```
-->

Adding zero does nothing: the lower cut of $x + 0$ consists of
rationals $q < r + s$ with $r$ below $x$ and $s < 0$, which is exactly
the rationals below some element of $x$'s lower cut — by roundedness,
exactly $x$'s lower cut.

```agda
+ᴿ-idr : ∀ x → x +ᴿ 0ᴿ ≡ x
```

<!--
```agda
private abstract
  half-zero : half 0 ≡ 0
  half-zero = ap (_*ℚ invℚ 2) (sym (*ℚ-zerol 1)) ∙ sym (*ℚ-associative 0 1 (invℚ 2)) ∙ *ℚ-zerol (1 *ℚ invℚ 2)

  r+s<r : ∀ r s → s < 0 → r +ℚ s < r
  r+s<r r s s<0 = subst (r +ℚ s <_) (+ℚ-idr r) (+ℚ-preserves-<l r s<0)

  r+[q-r]≡q : ∀ q r → r +ℚ (q +ℚ (-ℚ r)) ≡ q
  r+[q-r]≡q q r =
    r +ℚ (q +ℚ (-ℚ r))   ≡⟨ ap (r +ℚ_) (+ℚ-commutative q (-ℚ r)) ⟩
    r +ℚ ((-ℚ r) +ℚ q)   ≡⟨ +ℚ-associative r (-ℚ r) q ⟩
    (r +ℚ (-ℚ r)) +ℚ q   ≡⟨ ap (_+ℚ q) (+ℚ-invr r) ⟩
    0 +ℚ q               ≡⟨ +ℚ-idl q ⟩
    q                    ∎

  slack-neg : ∀ q r → q < r → half (q +ℚ (-ℚ r)) < 0
  slack-neg q r q<r = subst (half (q +ℚ (-ℚ r)) <_) half-zero (half-< diff-neg)
    where
    diff-neg : q +ℚ (-ℚ r) < 0
    diff-neg = subst (q +ℚ (-ℚ r) <_) (+ℚ-invr r) (+ℚ-preserves-<r (-ℚ r) q<r)

  q<r+slack : ∀ q r → q < r → q < r +ℚ half (q +ℚ (-ℚ r))
  q<r+slack q r q<r = transport (λ i → r+[q-r]≡q q r i < rhs i) step
    where
    diff-neg : q +ℚ (-ℚ r) < 0
    diff-neg = subst (q +ℚ (-ℚ r) <_) (+ℚ-invr r) (+ℚ-preserves-<r (-ℚ r) q<r)

    diff<half : (q +ℚ (-ℚ r)) < half (q +ℚ (-ℚ r))
    diff<half = transport (λ i → (q +ℚ (-ℚ r)) < midpoint-eq i) (mid-<l diff-neg)
      where
      midpoint-eq : midpoint (q +ℚ (-ℚ r)) 0 ≡ half (q +ℚ (-ℚ r))
      midpoint-eq = ap half (+ℚ-idr (q +ℚ (-ℚ r)))

    step : r +ℚ (q +ℚ (-ℚ r)) < r +ℚ half (q +ℚ (-ℚ r))
    step = +ℚ-preserves-<l r diff<half

    rhs : r +ℚ half (q +ℚ (-ℚ r)) ≡ r +ℚ half (q +ℚ (-ℚ r))
    rhs = refl

+ᴿ-idr x = ≤ᴿ-antisym shrink grow
  where
  shrink : ∀ q → ∣ (x +ᴿ 0ᴿ) .lower q ∣ → ∣ x .lower q ∣
  shrink q lq = □-elim (λ _ → hlevel 1)
    (λ (r , s , lr , s<0 , q<rs) →
      cut.lower-close x (<-trans q<rs (r+s<r r s s<0)) lr)
    lq

  grow : ∀ q → ∣ x .lower q ∣ → ∣ (x +ᴿ 0ᴿ) .lower q ∣
  grow q lq = □-map
    (λ (r , q<r , lr) →
      r , half (q +ℚ (-ℚ r)) , lr , slack-neg q r q<r , q<r+slack q r q<r)
    (tr-□ (cut.lower-round x q lq))
```
-->

A real number and its negation sum to zero: this is the one place
[[approximation|approx]] is used symmetrically on both sides of an
equation, rather than to establish locatedness.

```agda
+ᴿ-invr : ∀ x → x +ᴿ (-ᴿ x) ≡ 0ᴿ
```

<!--
```agda
private abstract
  r<negs→rs<0 : ∀ r s → r < (-ℚ s) → r +ℚ s < 0
  r<negs→rs<0 r s r<negs = subst (r +ℚ s <_) (+ℚ-invl s) (+ℚ-preserves-<r s r<negs)

  neg-diff-swap : ∀ u v → -ℚ (v +ℚ (-ℚ u)) ≡ u +ℚ (-ℚ v)
  neg-diff-swap u v = +ℚ-cancelr (v +ℚ (-ℚ u))
    ( (-ℚ (v +ℚ (-ℚ u))) +ℚ (v +ℚ (-ℚ u))               ≡⟨ +ℚ-invl (v +ℚ (-ℚ u)) ⟩
      0                                                  ≡˘⟨ rhs-vanishes ⟩
      (u +ℚ (-ℚ v)) +ℚ (v +ℚ (-ℚ u))                     ∎)
    where
    rhs-vanishes : (u +ℚ (-ℚ v)) +ℚ (v +ℚ (-ℚ u)) ≡ 0
    rhs-vanishes =
      (u +ℚ (-ℚ v)) +ℚ (v +ℚ (-ℚ u))   ≡⟨ +ℚ-swap-inner u (-ℚ v) v (-ℚ u) ⟩
      (u +ℚ v) +ℚ ((-ℚ v) +ℚ (-ℚ u))   ≡˘⟨ ap ((u +ℚ v) +ℚ_) negsum ⟩
      (u +ℚ v) +ℚ (-ℚ (v +ℚ u))        ≡⟨ ap (λ e → (u +ℚ v) +ℚ (-ℚ e)) (+ℚ-commutative v u) ⟩
      (u +ℚ v) +ℚ (-ℚ (u +ℚ v))        ≡⟨ +ℚ-invr (u +ℚ v) ⟩
      0                                 ∎
      where
      negsum : -ℚ (v +ℚ u) ≡ (-ℚ v) +ℚ (-ℚ u)
      negsum = +ℚ-cancelr (v +ℚ u)
        ( (-ℚ (v +ℚ u)) +ℚ (v +ℚ u)             ≡⟨ +ℚ-invl (v +ℚ u) ⟩
          0                                      ≡˘⟨ +ℚ-invl v ⟩
          (-ℚ v) +ℚ v                            ≡˘⟨ ap ((-ℚ v) +ℚ_) (+ℚ-idl v) ⟩
          (-ℚ v) +ℚ (0 +ℚ v)                     ≡˘⟨ ap (λ e → (-ℚ v) +ℚ (e +ℚ v)) (+ℚ-invl u) ⟩
          (-ℚ v) +ℚ (((-ℚ u) +ℚ u) +ℚ v)         ≡⟨ ap ((-ℚ v) +ℚ_) (sym (+ℚ-associative (-ℚ u) u v)) ⟩
          (-ℚ v) +ℚ ((-ℚ u) +ℚ (u +ℚ v))         ≡⟨ +ℚ-associative (-ℚ v) (-ℚ u) (u +ℚ v) ⟩
          ((-ℚ v) +ℚ (-ℚ u)) +ℚ (u +ℚ v)         ≡⟨ ap (((-ℚ v) +ℚ (-ℚ u)) +ℚ_) (+ℚ-commutative u v) ⟩
          ((-ℚ v) +ℚ (-ℚ u)) +ℚ (v +ℚ u)         ∎)

  neg-lt-swap : ∀ u v q → (v +ℚ (-ℚ u)) < (-ℚ q) → q < (u +ℚ (-ℚ v))
  neg-lt-swap u v q p =
    subst₂ _<_ (negℚ-invol q) (neg-diff-swap u v) (negℚ-anti-< p)

  0<-q→positive : ∀ q → q < 0 → 0 < (-ℚ q)
  0<-q→positive q q<0 = transport (λ i → +ℚ-invr q i < +ℚ-idl (-ℚ q) i) (+ℚ-preserves-<r (-ℚ q) q<0)

+ᴿ-invr x = ≤ᴿ-antisym shrink grow
  where
  shrink : ∀ q → ∣ (x +ᴿ (-ᴿ x)) .lower q ∣ → ∣ 0ᴿ .lower q ∣
  shrink q lq = □-elim (λ _ → hlevel 1)
    (λ (r , s , lr , ux' , q<rs) →
      <-trans q<rs (r<negs→rs<0 r s (lower<upper x lr ux')))
    lq

  grow : ∀ q → ∣ 0ᴿ .lower q ∣ → ∣ (x +ᴿ (-ᴿ x)) .lower q ∣
  grow q q<0 = ∥-∥-rec (hlevel 1) mk (approx x (-ℚ q) (0<-q→positive q q<0))
    where
    mk : (Σ Ratio λ u → Σ Ratio λ v →
           ∣ x .lower u ∣ × ∣ x .upper v ∣ × ((v +ℚ (-ℚ u)) < (-ℚ q)))
       → ∣ (x +ᴿ (-ᴿ x)) .lower q ∣
    mk (u , v , lu , uv , gap) = inc (u , -ℚ v , lu ,
      subst (λ z → ∣ x .upper z ∣) (sym (negℚ-invol v)) uv ,
      neg-lt-swap u v q gap)
```
-->
