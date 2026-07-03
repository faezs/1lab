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
```
-->
