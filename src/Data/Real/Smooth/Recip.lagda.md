<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Reciprocal
open import Data.Real.Smooth.Partial
open import Data.Real.Smooth
open import Data.Real.Base
open import Data.Real.Ring

open import Data.Rational.Order
open import Data.Rational.Base

open import Data.Bool.Base
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum
```
-->

```agda
module Data.Real.Smooth.Recip where
```

# The reciprocal's Hadamard towers on positive boxes {defines="reciprocal-tower"}

The [[reciprocal|real-reciprocal]] is the first genuinely *partial*
[[smooth function|partial-smooth-function]]: it lives on boxes whose
lower endpoints are positive rationals, and its Hadamard quotient

$$
\frac1x - \frac1t = (x - t)\cdot\frac{-1}{x\,t}
$$

is again built from coordinate reciprocals. The class that is closed
under taking quotients is the class of **signed reciprocal
monomials**: products, over a Boolean mask of coordinates, of the
reciprocals of those coordinates, with an overall sign. Each
quotient in a masked direction is the monomial with the *fresh*
variable's reciprocal adjoined and the sign flipped; quotients in
unmasked directions vanish. This module builds that class and
recurses through it, producing towers of every depth for every
monomial — and in particular for the reciprocal itself.

## Positive boxes

A box is positive when every lower endpoint is a positive rational;
positivity is inherited by all the cylinders that the tower climbs
through.

```agda
PosBox : ∀ {n} → Box n → Type
PosBox {n} B = (i : Fin n) → 0 < B i .fst

cyl-pos
  : ∀ {n} (B : Box n) (pB : PosBox B) (i : Fin n)
  → PosBox (cylᵇ B i)
cyl-pos B pB i l with fin-view l
... | zero  = pB i
... | suc j = pB j
```

## Coordinate reciprocals

On a positive box, every coordinate of every box point merely has
positive bounds, so its reciprocal through the truncation is
defined. Since the bounds inhabit a proposition, the reciprocal
of a coordinate depends only on the coordinate itself:

```agda
rvec
  : ∀ {n} (B : Box n) (pB : PosBox B)
  → (x : Fin n → ℝ) → x ∈ᵇ B → Fin n → ℝ
rvec B pB x px i =
  recip∥ (x i)
    (box-positive-bounds (B i .fst) (B i .snd) (pB i) (x i) (px i))

recip∥-ap
  : {z w : ℝ} (p : z ≡ w)
    (pz : ∥ positive-bounds z ∥) (pw : ∥ positive-bounds w ∥)
  → recip∥ z pz ≡ recip∥ w pw
recip∥-ap {z} {w} p pz pw i = recip∥ (p i) (q i) where
  q : PathP (λ i → ∥ positive-bounds (p i) ∥) pz pw
  q = is-prop→pathp (λ i → squash) pz pw
```

## Mask products

A **mask** selects a subset of the coordinates; the masked product
multiplies the selected entries of a vector, head first, so that
adjoining a fresh entry at the front of both mask and vector is
definitionally a single multiplication.

```agda
Πmask : ∀ {n} → (Fin n → Bool) → (Fin n → ℝ) → ℝ
Πmask {zero}  m r = 1ᴿ
Πmask {suc n} m r =
  (if m fzero then r fzero else 1ᴿ) *ᴿ
  Πmask (λ j → m (fsuc j)) (λ j → r (fsuc j))

clear : ∀ {n} → Fin n → (Fin n → Bool) → Fin n → Bool
clear i m j with Discrete-Fin .decide i j
... | yes _ = false
... | no  _ = m j

bcons : ∀ {n} → Bool → (Fin n → Bool) → Fin (suc n) → Bool
bcons b m j with fin-view j
... | zero  = b
... | suc l = m l
```

<!--
```agda
private
  clear-same : ∀ {n} (i : Fin n) (m : Fin n → Bool) → clear i m i ≡ false
  clear-same i m with Discrete-Fin .decide i i
  ... | yes _ = refl
  ... | no ¬p = absurd (¬p refl)

  clear-other
    : ∀ {n} (i j : Fin n) (m : Fin n → Bool)
    → ¬ i ≡ j → clear i m j ≡ m j
  clear-other i j m ne with Discrete-Fin .decide i j
  ... | yes p = absurd (ne p)
  ... | no  _ = refl

  clear-suc
    : ∀ {n} (i : Fin n) (m : Fin (suc n) → Bool) (j : Fin n)
    → clear (fsuc i) m (fsuc j) ≡ clear i (λ l → m (fsuc l)) j
  clear-suc i m j
    with Discrete-Fin .decide (fsuc i) (fsuc j) | Discrete-Fin .decide i j
  ... | yes _ | yes _ = refl
  ... | yes p | no ¬q = absurd (¬q (fsuc-inj p))
  ... | no ¬p | yes q = absurd (¬p (ap fsuc q))
  ... | no  _ | no  _ = refl

  set-same : ∀ {n} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) → set x i t i ≡ t
  set-same x i t with Discrete-Fin .decide i i
  ... | yes _ = refl
  ... | no ¬p = absurd (¬p refl)

  set-other
    : ∀ {n} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ)
    → ¬ i ≡ j → set x i t j ≡ x j
  set-other x i j t ne with Discrete-Fin .decide i j
  ... | yes p = absurd (ne p)
  ... | no  _ = refl
```
-->

The masked product only looks at the selected entries, and a
selected entry can be factored out, leaving the product over the
mask with that coordinate cleared.

```agda
Πmask-ext
  : ∀ {n} (m : Fin n → Bool) (r r' : Fin n → ℝ)
  → ((j : Fin n) → m j ≡ true → r j ≡ r' j)
  → Πmask m r ≡ Πmask m r'
Πmask-ext {zero}  m r r' h = refl
Πmask-ext {suc n} m r r' h = ap₂ _*ᴿ_
  (head-eq (m fzero) (h fzero))
  (Πmask-ext (λ j → m (fsuc j)) (λ j → r (fsuc j)) (λ j → r' (fsuc j))
    (λ j e → h (fsuc j) e))
  where
  head-eq
    : (b : Bool) → (b ≡ true → r fzero ≡ r' fzero)
    → (if b then r fzero else 1ᴿ) ≡ (if b then r' fzero else 1ᴿ)
  head-eq true  h0 = h0 refl
  head-eq false h0 = refl
```

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  swap-mult : ∀ h a p → h R.* (a R.* p) ≡ a R.* (h R.* p)
  swap-mult h a p = cring! S

  quot-id
    : ∀ u v ru rv
    → (ru R.* (v R.* rv)) R.+ (R.- ((u R.* ru) R.* rv))
    ≡ (u R.+ (R.- v)) R.* (R.- (ru R.* rv))
  quot-id u v ru rv = cring! S

  factor-diff
    : ∀ a b p
    → (a R.* p) R.+ (R.- (b R.* p)) ≡ (a R.+ (R.- b)) R.* p
  factor-diff a b p = cring! S

  reassoc-pos
    : ∀ d a b p
    → (d R.* (R.- (a R.* b))) R.* p ≡ d R.* (R.- (b R.* (a R.* p)))
  reassoc-pos d a b p = cring! S

  factor-diff-neg
    : ∀ a b p
    → (R.- (a R.* p)) R.+ (R.- (R.- (b R.* p)))
    ≡ (a R.+ (R.- b)) R.* (R.- p)
  factor-diff-neg a b p = cring! S

  reassoc-neg
    : ∀ d a b p
    → (d R.* (R.- (a R.* b))) R.* (R.- p) ≡ d R.* (b R.* (a R.* p))
  reassoc-neg d a b p = cring! S

private module RI = Identities ℝ-comm

private
  absorbr : ∀ x → x *ᴿ 0ᴿ ≡ 0ᴿ
  absorbr x =
      sym (+ᴿ-idr (x *ᴿ 0ᴿ))
    ∙ ap ((x *ᴿ 0ᴿ) +ᴿ_) (sym (+ᴿ-invr (x *ᴿ 0ᴿ)))
    ∙ +ᴿ-assoc (x *ᴿ 0ᴿ) (x *ᴿ 0ᴿ) (-ᴿ (x *ᴿ 0ᴿ))
    ∙ ap (_+ᴿ (-ᴿ (x *ᴿ 0ᴿ)))
        ( sym (*ᴿ-distribˡ x 0ᴿ 0ᴿ)
        ∙ ap (x *ᴿ_) (+ᴿ-idr 0ᴿ))
    ∙ +ᴿ-invr (x *ᴿ 0ᴿ)
```
-->

```agda
Πmask-factor
  : ∀ {n} (i : Fin n) (m : Fin n → Bool) (r : Fin n → ℝ)
  → m i ≡ true
  → Πmask m r ≡ r i *ᴿ Πmask (clear i m) r
Πmask-factor {zero}  i m r e = absurd (Fin-absurd i)
Πmask-factor {suc n} i m r e with fin-view i
... | zero =
      ap (λ b → (if b then r fzero else 1ᴿ) *ᴿ tl) e
    ∙ ap (r fzero *ᴿ_) (sym tail-eq)
  where
    tl = Πmask (λ j → m (fsuc j)) (λ j → r (fsuc j))

    tail-eq : Πmask (clear fzero m) r ≡ tl
    tail-eq =
        ap₂ (λ b mm → (if b then r fzero else 1ᴿ) *ᴿ
              Πmask mm (λ j → r (fsuc j)))
          (clear-same fzero m)
          (funext λ j → clear-other fzero (fsuc j) m fzero≠fsuc)
      ∙ *ᴿ-idl tl
... | suc i' =
      ap (hd *ᴿ_)
        (Πmask-factor i' (λ j → m (fsuc j)) (λ j → r (fsuc j)) e)
    ∙ RI.swap-mult hd (r (fsuc i')) tl'
    ∙ ap (r (fsuc i') *ᴿ_) (sym tail-eq)
  where
    hd  = if m fzero then r fzero else 1ᴿ
    tl' = Πmask (clear i' (λ j → m (fsuc j))) (λ j → r (fsuc j))

    tail-eq : Πmask (clear (fsuc i') m) r ≡ hd *ᴿ tl'
    tail-eq = ap₂
      (λ b mm → (if b then r fzero else 1ᴿ) *ᴿ
        Πmask mm (λ j → r (fsuc j)))
      (clear-other (fsuc i') fzero m fsuc≠fzero)
      (funext λ j → clear-suc i' m j)
```

## Signed reciprocal monomials

A signed monomial is a mask product of coordinate reciprocals with
an overall sign, recorded as a Boolean (`true`{.Agda} is $+$).

```agda
signᴿ : Bool → ℝ → ℝ
signᴿ true  z = z
signᴿ false z = -ᴿ z

mval
  : ∀ {n} (B : Box n) (pB : PosBox B)
  → Bool → (Fin n → Bool) → PFun n B
mval B pB s m x px = signᴿ s (Πmask m (rvec B pB x px))
```

## The quotient identity

For any two elements with chosen inverses, the difference of the
inverses factors through the difference of the elements — this is
Hadamard's quotient for the reciprocal, and it is pure ring algebra
once both inverse laws are in hand.

```agda
recip-diff
  : ∀ u v ru rv → u *ᴿ ru ≡ 1ᴿ → v *ᴿ rv ≡ 1ᴿ
  → ru −ᴿ rv ≡ (u −ᴿ v) *ᴿ (-ᴿ (ru *ᴿ rv))
recip-diff u v ru rv hu hv =
    ap₂ _−ᴿ_
      (sym (ap (ru *ᴿ_) hv ∙ *ᴿ-idr ru))
      (sym (ap (_*ᴿ rv) hu ∙ *ᴿ-idl rv))
  ∙ RI.quot-id u v ru rv
```

Lifting the identity across a common factor and a sign: this is the
exact shape of the tower step below, stated once for both signs.

<!--
```agda
private
  lift-quot
    : ∀ (s : Bool) (ru rv P d : ℝ)
    → ru −ᴿ rv ≡ d *ᴿ (-ᴿ (ru *ᴿ rv))
    → signᴿ s (ru *ᴿ P) −ᴿ signᴿ s (rv *ᴿ P)
    ≡ d *ᴿ signᴿ (not s) (rv *ᴿ (ru *ᴿ P))
  lift-quot true ru rv P d h =
    RI.factor-diff ru rv P ∙ ap (_*ᴿ P) h ∙ RI.reassoc-pos d ru rv P
  lift-quot false ru rv P d h =
      RI.factor-diff-neg ru rv P
    ∙ ap (_*ᴿ (-ᴿ P)) h
    ∙ RI.reassoc-neg d ru rv P
```
-->

## Tower closure

Constant partial functions carry towers of every depth, exactly as
in the global case.

```agda
towerOn-const : ∀ k {n} (B : Box n) (c : ℝ) → TowerOnTo k B (λ _ _ → c)
towerOn-const zero    B c = lift tt
towerOn-const (suc k) B c i =
    (λ _ _ → 0ᴿ)
  , (λ x px t pt → +ᴿ-invr c ∙ sym (absorbr (x i −ᴿ t)))
  , towerOn-const k (cylᵇ B i) 0ᴿ
```

The main recursion: every signed monomial carries a tower of every
depth. In a masked direction the quotient is the monomial on the
cylinder with the fresh variable's reciprocal adjoined and the sign
flipped; in an unmasked direction the value does not move, and the
quotient is zero.

```agda
towerOn-mono
  : ∀ k {n} (B : Box n) (pB : PosBox B) (s : Bool) (m : Fin n → Bool)
  → TowerOnTo k B (mval B pB s m)
towerOn-mono zero    B pB s m = lift tt
towerOn-mono (suc k) {n} B pB s m i = go (m i) refl where
  go
    : (b : Bool) → m i ≡ b
    → Σ[ g ∈ PFun (suc n) (cylᵇ B i) ]
        (QuotOn B (mval B pB s m) i g × TowerOnTo k (cylᵇ B i) g)
  go true e =
      g₀
    , quot
    , towerOn-mono k (cylᵇ B i) (cyl-pos B pB i) (not s) (bcons true m)
    where
    g₀ : PFun (suc n) (cylᵇ B i)
    g₀ = mval (cylᵇ B i) (cyl-pos B pB i) (not s) (bcons true m)

    quot : QuotOn B (mval B pB s m) i g₀
    quot x px t pt =
      let
        R   = rvec B pB x px
        R'  = rvec B pB (set x i t) (set-∈ᵇ i px pt)
        pbx = box-positive-bounds (B i .fst) (B i .snd) (pB i) (x i) (px i)
        pbt = box-positive-bounds (B i .fst) (B i .snd) (pB i) t pt
        ru  = recip∥ (x i) pbx
        rv  = recip∥ t pbt
        P   = Πmask (clear i m) R

        fac : Πmask m R ≡ ru *ᴿ P
        fac = Πmask-factor i m R e

        P'≡P : Πmask (clear i m) R' ≡ P
        P'≡P = Πmask-ext (clear i m) R' R λ j e' →
          recip∥-ap
            (set-other x i j t λ p →
              true≠false (sym e' ∙ ap (clear i m) (sym p) ∙ clear-same i m))
            _ _

        R'i≡rv : R' i ≡ rv
        R'i≡rv = recip∥-ap (set-same x i t) _ _

        key : ru −ᴿ rv ≡ (x i −ᴿ t) *ᴿ (-ᴿ (ru *ᴿ rv))
        key = recip-diff (x i) t ru rv
          (recip∥-invr (x i) pbx) (recip∥-invr t pbt)
      in
        ap₂ (λ a b → signᴿ s a −ᴿ signᴿ s b)
          fac
          (Πmask-factor i m R' e ∙ ap₂ _*ᴿ_ R'i≡rv P'≡P)
      ∙ lift-quot s ru rv P (x i −ᴿ t) key
      ∙ ap (λ w → (x i −ᴿ t) *ᴿ signᴿ (not s) (rv *ᴿ w)) (sym fac)
  go false e =
      (λ _ _ → 0ᴿ)
    , (λ x px t pt →
          ap (λ w → mval B pB s m x px −ᴿ signᴿ s w)
            (Πmask-ext m
              (rvec B pB (set x i t) (set-∈ᵇ i px pt))
              (rvec B pB x px)
              (λ j e' → recip∥-ap
                (set-other x i j t λ p →
                  true≠false (sym e' ∙ sym (ap m p) ∙ e))
                _ _))
        ∙ +ᴿ-invr (mval B pB s m x px)
        ∙ sym (absorbr (x i −ᴿ t)))
    , towerOn-const k (cylᵇ B i) 0ᴿ
```

## The reciprocal is smooth on positive boxes

Partial smoothness respects pointwise equality of values, since a
partial function is literally a (dependent) function of the point
and the membership proof.

```agda
smoothOn-ext
  : ∀ {n} (B : Box n) (f g : PFun n B)
  → ((x : Fin n → ℝ) (px : x ∈ᵇ B) → f x px ≡ g x px)
  → SmoothOn B f → SmoothOn B g
smoothOn-ext B f g h S =
  subst (SmoothOn B) (funext λ x → funext λ px → h x px) S

recip-mono-smooth
  : ∀ {n} (B : Box n) (pB : PosBox B) (s : Bool) (m : Fin n → Bool)
  → SmoothOn B (mval B pB s m)
recip-mono-smooth B pB s m k = towerOn-mono k B pB s m
```

The reciprocal on a positive interval is the singleton-mask
monomial, up to a unit law, so it is smooth on the box.

```agda
recipᵇ-smooth
  : (a b : Ratio) (0<a : 0 < a)
  → SmoothOn (λ _ → a , b) (recipᵇ a b 0<a)
recipᵇ-smooth a b 0<a = smoothOn-ext (λ _ → a , b)
  (mval (λ _ → a , b) (λ _ → 0<a) true (λ _ → true))
  (recipᵇ a b 0<a)
  (λ x px → *ᴿ-idr _)
  (recip-mono-smooth (λ _ → a , b) (λ _ → 0<a) true (λ _ → true))
```
