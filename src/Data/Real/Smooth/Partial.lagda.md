<!--
```agda
open import 1Lab.Prelude

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Reciprocal
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Smooth

open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Partial where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
open positive-bounds
```
-->

# Opens and partial smoothness {defines="rational-box partial-smooth-function"}

The paper's site condition (2.) quantifies over *differentiably
good open covers*: covers of $\bR^n$ by opens diffeomorphic to
$\bR^n$. The constructive substrate for this is a layer of
**rational open boxes** and functions smooth *on* a box — the
Hadamard towers of the [[smooth calculus|hadamard-tower]], with
every quantifier relativised so that both the unmoved and the moved
point stay inside the box.

## Rational boxes

A box assigns each coordinate a rational open interval; membership
is a proposition, so partial functions defined on box points need
no coherence data.

```agda
Box : Nat → Type
Box n = Fin n → Ratio × Ratio

_∈ᵇ_ : ∀ {n} → (Fin n → ℝ) → Box n → Type
x ∈ᵇ B = (i : _) →
  (ratℝ (B i .fst) <ᴿ x i) × (x i <ᴿ ratℝ (B i .snd))

∈ᵇ-is-prop : ∀ {n} (x : Fin n → ℝ) (B : Box n) → is-prop (x ∈ᵇ B)
∈ᵇ-is-prop x B = Π-is-hlevel 1 λ i → ×-is-hlevel 1
  (<ᴿ-is-prop {ratℝ (B i .fst)} {x i})
  (<ᴿ-is-prop {x i} {ratℝ (B i .snd)})
  where
  <ᴿ-is-prop : ∀ {a b} → is-prop (a <ᴿ b)
  <ᴿ-is-prop = squash
```

The tower of a partial function in direction $i$ lives on the
**cylinder** box, which repeats the $i$-th interval for the fresh
variable.

```agda
cylᵇ : ∀ {n} → Box n → Fin n → Box (suc n)
cylᵇ B i l with fin-view l
... | zero  = B i
... | suc j = B j

PFun : ∀ n → Box n → Type
PFun n B = (x : Fin n → ℝ) → x ∈ᵇ B → ℝ
```

Membership bookkeeping: setting the $i$-th coordinate to a point of
the $i$-th interval stays in the box, and consing a point of the
$i$-th interval onto a box point lands in the cylinder.

```agda
set-∈ᵇ
  : ∀ {n} {B : Box n} {x : Fin n → ℝ} (i : Fin n) {t : ℝ}
  → x ∈ᵇ B
  → (ratℝ (B i .fst) <ᴿ t) × (t <ᴿ ratℝ (B i .snd))
  → set x i t ∈ᵇ B
set-∈ᵇ {n} {B} {x} i {t} px pt j with Discrete-Fin .decide i j
... | yes p = subst (λ w → (ratℝ (B w .fst) <ᴿ t) × (t <ᴿ ratℝ (B w .snd))) p pt
... | no  _ = px j

cons-∈ᵇ
  : ∀ {n} {B : Box n} {x : Fin n → ℝ} (i : Fin n) {t : ℝ}
  → (ratℝ (B i .fst) <ᴿ t) × (t <ᴿ ratℝ (B i .snd))
  → x ∈ᵇ B
  → (λ l → cons t x l) ∈ᵇ cylᵇ B i
cons-∈ᵇ {n} {B} {x} i {t} pt px l with fin-view l
... | zero  = pt
... | suc j = px j
```

## Partial towers

The Hadamard tower on a box: identical to the global one, with all
three points — unmoved, moved, and the quotient's argument —
relativised to the box and its cylinder.

```agda
QuotOn
  : ∀ {n} (B : Box n) → PFun n B → (i : Fin n)
  → PFun (suc n) (cylᵇ B i) → Type
QuotOn {n} B f i g =
  (x : Fin n → ℝ) (px : x ∈ᵇ B) (t : ℝ)
  (pt : (ratℝ (B i .fst) <ᴿ t) × (t <ᴿ ratℝ (B i .snd)))
  → f x px −ᴿ f (set x i t) (set-∈ᵇ i px pt)
  ≡ (x i −ᴿ t) *ᴿ g (cons t x) (cons-∈ᵇ i pt px)

TowerOnTo : Nat → ∀ {n} (B : Box n) → PFun n B → Type
TowerOnTo zero    B f = Lift lzero ⊤
TowerOnTo (suc k) {n} B f =
  (i : Fin n) →
    Σ[ g ∈ PFun (suc n) (cylᵇ B i) ]
      (QuotOn B f i g × TowerOnTo k (cylᵇ B i) g)

SmoothOn : ∀ {n} (B : Box n) → PFun n B → Type
SmoothOn B f = (k : Nat) → TowerOnTo k B f
```

Globally smooth functions restrict to every box: the towers
specialise pointwise, forgetting the membership proofs.

```agda
restrict : ∀ {n} (B : Box n) → Fun n → PFun n B
restrict B f x _ = f x

tower-restrict
  : ∀ k {n} (B : Box n) (f : Fun n)
  → TowerTo k n f → TowerOnTo k B (restrict B f)
tower-restrict zero    B f T = lift tt
tower-restrict (suc k) B f T i =
    restrict (cylᵇ B i) (T i .fst)
  , (λ x px t pt → T i .snd .fst x t)
  , tower-restrict k (cylᵇ B i) (T i .fst) (T i .snd .snd)

smooth-restrict
  : ∀ {n} (B : Box n) {f : Fun n}
  → Smooth n f → SmoothOn B (restrict B f)
smooth-restrict B S k = tower-restrict k B _ (S k)
```

## The reciprocal as a partial function

The first genuinely partial smooth function is the reciprocal, on
boxes bounded away from zero. Its value does not depend on which
bounds witness the positivity — inverses in a commutative ring are
unique — so it descends through the truncated bounds that box
membership provides.

```agda
inverse-unique
  : (x r r' : ℝ) → x *ᴿ r ≡ 1ᴿ → x *ᴿ r' ≡ 1ᴿ → r ≡ r'
inverse-unique x r r' p p' =
    sym (*ᴿ-idl r)
  ∙ ap (_*ᴿ r) (sym p' ∙ *ᴿ-comm x r')
  ∙ *ᴿ-assoc r' x r
  ∙ ap (r' *ᴿ_) p
  ∙ *ᴿ-idr r'

recip∥ : (x : ℝ) → ∥ positive-bounds x ∥ → ℝ
recip∥ x = ∥-∥-rec-set ℝ-is-set (recip x)
  (λ pb pb' → inverse-unique x (recip x pb) (recip x pb')
    (recip-invr x pb) (recip-invr x pb'))

recip∥-invr
  : ∀ x (p : ∥ positive-bounds x ∥) → x *ᴿ recip∥ x p ≡ 1ᴿ
recip∥-invr x = ∥-∥-elim (λ _ → ℝ-is-set _ _) (recip-invr x)
```

A box point of a positive interval merely carries positive bounds:
roundedness turns the strict rational comparisons into cut
witnesses.

```agda
box-positive-bounds
  : (a b : Ratio) → 0 < a → (z : ℝ)
  → (ratℝ a <ᴿ z) × (z <ᴿ ratℝ b)
  → ∥ positive-bounds z ∥
box-positive-bounds a b 0<a z (lo<z , z<hi) =
  ∥-∥-rec₂ squash
    (λ (r , ur , lr) (r' , ur' , lr') → inc (mk r r' ur lr ur' lr'))
    lo<z z<hi
  where
  mk
    : ∀ r r' → ∣ ratℝ a .upper r ∣ → ∣ z .lower r ∣
    → ∣ z .upper r' ∣ → ∣ ratℝ b .lower r' ∣
    → positive-bounds z
  mk r r' ur lr ur' lr' .lo = r
  mk r r' ur lr ur' lr' .hi = r'
  mk r r' ur lr ur' lr' .lo-mem = lr
  mk r r' ur lr ur' lr' .hi-mem = ur'
  mk r r' ur lr ur' lr' .lo-pos = <-trans 0<a ur

recipᵇ
  : (a b : Ratio) → 0 < a
  → PFun 1 (λ _ → a , b)
recipᵇ a b 0<a x px =
  recip∥ (x fzero) (box-positive-bounds a b 0<a (x fzero) (px fzero))
```

The Hadamard tower of the reciprocal — with the algebraic quotient
$\frac1x - \frac1t = (x - t)\cdot\frac{-1}{xt}$ — together with its
bounds on compactly-contained sub-boxes, is the next rung: it is
what the good-cover diffeomorphisms of the site's coverage are made
of.
