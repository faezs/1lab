<!--
```agda
open import 1Lab.Truncation
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Base where
```

# Dedekind real numbers {defines="dedekind-real real-number dedekind-cut"}

A **Dedekind real number** is a two-sided cut in the rationals: a
pair of predicates carving out the rationals strictly below and
strictly above the number, each *rounded* (containing no endpoint),
together *disjoint*, and — the constructive heart of the definition —
**located**: between any two rationals, the cut must commit to one
side or the other. No choice, no excluded middle, and no limits are
involved; and since the 1Lab's type `Ω`{.Agda} of propositions is
[[resized|propositional-resizing]], the type of reals lives in the
lowest universe.

```agda
record is-cut (L U : Ratio → Ω) : Type where
  no-eta-equality
  field
    lower-inhab : ∥ Σ Ratio (λ q → ∣ L q ∣) ∥
    upper-inhab : ∥ Σ Ratio (λ r → ∣ U r ∣) ∥

    lower-round : ∀ q → ∣ L q ∣ → ∥ Σ Ratio (λ r → (q < r) × ∣ L r ∣) ∥
    lower-close : ∀ {q r} → q < r → ∣ L r ∣ → ∣ L q ∣

    upper-round : ∀ r → ∣ U r ∣ → ∥ Σ Ratio (λ q → (q < r) × ∣ U q ∣) ∥
    upper-close : ∀ {q r} → q < r → ∣ U q ∣ → ∣ U r ∣

    cut-disjoint : ∀ q → ∣ L q ∣ → ∣ U q ∣ → ⊥
    cut-located  : ∀ {q r} → q < r → ∥ ∣ L q ∣ ⊎ ∣ U r ∣ ∥
```

<!--
```agda
unquoteDecl H-Level-is-cut = declare-record-hlevel 1 H-Level-is-cut (quote is-cut)

open is-cut
```
-->

```agda
record ℝ : Type where
  no-eta-equality
  field
    lower upper : Ratio → Ω
    has-is-cut  : is-cut lower upper
```

<!--
```agda
open ℝ public

private module cut (x : ℝ) = is-cut (x .has-is-cut)

private unquoteDecl eqv = declare-record-iso eqv (quote ℝ)

ℝ-path
  : {x y : ℝ} → x .lower ≡ y .lower → x .upper ≡ y .upper → x ≡ y
ℝ-path p q i .lower = p i
ℝ-path p q i .upper = q i
ℝ-path {x} {y} p q i .has-is-cut = is-prop→pathp
  (λ i → hlevel {T = is-cut (p i) (q i)} 1)
  (x .has-is-cut) (y .has-is-cut) i

ℝ-is-set : is-set ℝ
ℝ-is-set = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → hlevel 2) λ L →
  Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → hlevel 2) λ U →
  is-prop→is-set (hlevel 1)

instance
  H-Level-ℝ : ∀ {n} → H-Level ℝ (2 + n)
  H-Level-ℝ = basic-instance 2 ℝ-is-set
```
-->

## Order bootstrap on the rationals

The rationals have a *decidable* order, and everything the cut
axioms ask for — density, cotransitivity — follows from that by pure
logic plus a little ring algebra. These lemmas are stated here
because the 1Lab's rational-number interface does not yet provide
them.

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

## The rationals embed

A rational $t$ determines the cut of rationals strictly below and
strictly above it. Roundedness is the density of the rational order
— witnessed by midpoints — and locatedness is its cotransitivity,
which holds outright because the order is decidable.

```agda
ratℝ : Ratio → ℝ
ratℝ t .lower q = el (q < t) (hlevel 1)
ratℝ t .upper r = el (t < r) (hlevel 1)
ratℝ t .has-is-cut = record
  { lower-inhab  = inc (t +ℚ (-ℚ 1) , below) 
  ; upper-inhab  = inc (t +ℚ 1 , above)
  ; lower-round  = λ q q<t → inc (midpoint q t , mid-<l q<t , mid-<r q<t)
  ; lower-close  = λ q<r r<t → <-trans q<r r<t
  ; upper-round  = λ r t<r → inc (midpoint t r , mid-<r t<r , mid-<l t<r)
  ; upper-close  = λ q<r t<q → <-trans t<q q<r
  ; cut-disjoint = λ q q<t t<q → <-irrefl refl (<-trans q<t t<q)
  ; cut-located  = λ q<r → inc (<-cotrans t q<r)
  }
  where abstract
    neg1<0 : -ℚ 1 < 0
    neg1<0 = decide!

    0<1 : 0 < 1
    0<1 = decide!

    below : t +ℚ (-ℚ 1) < t
    below = subst (t +ℚ (-ℚ 1) <_) (+ℚ-idr t)
      (+ℚ-preserves-<l t neg1<0)

    above : t < t +ℚ 1
    above = subst (_< t +ℚ 1) (+ℚ-idr t)
      (+ℚ-preserves-<l t 0<1)
```

## Order

A real is less than another when some rational fits strictly between
them — above the first, below the second. The non-strict order is
inclusion of lower cuts.

```agda
_<ᴿ_ : ℝ → ℝ → Type
x <ᴿ y = ∥ Σ Ratio (λ q → ∣ x .upper q ∣ × ∣ y .lower q ∣) ∥

_≤ᴿ_ : ℝ → ℝ → Type
x ≤ᴿ y = ∀ q → ∣ x .lower q ∣ → ∣ y .lower q ∣
```

Anything in the lower cut is smaller than anything in the upper cut
— by disjointness and decidability of the rational order — and from
this the expected order theory follows.

```agda
lower<upper
  : (x : ℝ) → ∀ {q r} → ∣ x .lower q ∣ → ∣ x .upper r ∣ → q < r
lower<upper x {q} {r} lq ur with holds? (q < r)
... | yes p = p
... | no ¬p with ≤-strengthen (¬<→≥ ¬p)
... | inl e   = absurd (cut.cut-disjoint x q lq
                  (subst (λ z → ∣ x .upper z ∣) e ur))
... | inr r<q = absurd (cut.cut-disjoint x q lq
                  (cut.upper-close x r<q ur))

<ᴿ-irrefl : ∀ {x} → x <ᴿ x → ⊥
<ᴿ-irrefl {x} = ∥-∥-rec (hlevel 1) λ (q , u , l) →
  cut.cut-disjoint x q l u

<ᴿ-trans : ∀ {x y z} → x <ᴿ y → y <ᴿ z → x <ᴿ z
<ᴿ-trans {x} {y} {z} = ∥-∥-rec₂ squash λ (q , ux , ly) (r , uy , lz) →
  inc (q , ux , cut.lower-close z (lower<upper y ly uy) lz)

<ᴿ-weaken : ∀ {x y} → x <ᴿ y → x ≤ᴿ y
<ᴿ-weaken {x} {y} p q lq = ∥-∥-rec ((y .lower q) .is-tr)
  (λ (s , ux , ly) → cut.lower-close y (lower<upper x lq ux) ly) p

≤ᴿ-refl : ∀ {x} → x ≤ᴿ x
≤ᴿ-refl q lq = lq

≤ᴿ-trans : ∀ {x y z} → x ≤ᴿ y → y ≤ᴿ z → x ≤ᴿ z
≤ᴿ-trans p q s ls = q s (p s ls)
```

Antisymmetry is where locatedness earns its keep: a cut is
determined by its lower part alone, since the upper part is forced —
so mutual inclusion of lower cuts is equality of reals.

```agda
≤ᴿ-antisym : ∀ {x y} → x ≤ᴿ y → y ≤ᴿ x → x ≡ y
≤ᴿ-antisym {x} {y} p q = ℝ-path
  (funext λ s → Ω-ua (p s) (q s))
  (funext λ s → Ω-ua (upper-sub x y q s) (upper-sub y x p s))
  where
  upper-sub
    : (x y : ℝ) → y ≤ᴿ x
    → ∀ r → ∣ x .upper r ∣ → ∣ y .upper r ∣
  upper-sub x y q r ur = ∥-∥-rec ((y .upper r) .is-tr)
    (λ (r' , r'<r , ur') → ∥-∥-rec ((y .upper r) .is-tr)
      (λ { (inl ly) → absurd (cut.cut-disjoint x r' (q r' ly) ur')
         ; (inr uy) → uy })
      (cut.cut-located y r'<r))
    (cut.upper-round x r ur)
```

The embedding of the rationals is an order embedding, and the
rationals are **dense**: strictly between any two reals lies a
rational.

```agda
ratℝ-preserves-< : ∀ {q r} → q < r → ratℝ q <ᴿ ratℝ r
ratℝ-preserves-< {q} {r} p =
  inc (midpoint q r , mid-<l p , mid-<r p)

ratℝ-reflects-< : ∀ {q r} → ratℝ q <ᴿ ratℝ r → q < r
ratℝ-reflects-< = ∥-∥-rec (hlevel 1) λ (s , q<s , s<r) →
  <-trans q<s s<r

rational-density
  : ∀ {x y} → x <ᴿ y
  → ∥ Σ Ratio (λ q → (x <ᴿ ratℝ q) × (ratℝ q <ᴿ y)) ∥
rational-density {x} {y} = ∥-∥-rec squash λ (q , ux , ly) →
  ∥-∥-rec₂ squash
    (λ (s , s<q , ux') (r , q<r , ly') →
      inc (q , inc (s , ux' , s<q) , inc (r , q<r , ly')))
    (cut.upper-round x q ux)
    (cut.lower-round y q ly)
```

## Negation

Negation swaps the two halves of the cut, reflecting each through
zero. It is an involution, and reverses the order.

```agda
-ᴿ_ : ℝ → ℝ
(-ᴿ x) .lower q = x .upper (-ℚ q)
(-ᴿ x) .upper q = x .lower (-ℚ q)
(-ᴿ x) .has-is-cut = record
  { lower-inhab = ∥-∥-map
      (λ (r , ur) → -ℚ r ,
        subst (λ z → ∣ x .upper z ∣) (sym (negℚ-invol r)) ur)
      (cut.upper-inhab x)
  ; upper-inhab = ∥-∥-map
      (λ (q , lq) → -ℚ q ,
        subst (λ z → ∣ x .lower z ∣) (sym (negℚ-invol q)) lq)
      (cut.lower-inhab x)
  ; lower-round = λ q uq → ∥-∥-map
      (λ (s , s<-q , us) → -ℚ s ,
        transport (λ i → negℚ-invol q i < -ℚ s) (negℚ-anti-< s<-q) ,
        subst (λ z → ∣ x .upper z ∣) (sym (negℚ-invol s)) us)
      (cut.upper-round x (-ℚ q) uq)
  ; lower-close = λ q<r ur → cut.upper-close x (negℚ-anti-< q<r) ur
  ; upper-round = λ r lr → ∥-∥-map
      (λ (s , -r<s , ls) → -ℚ s ,
        transport (λ i → -ℚ s < negℚ-invol r i) (negℚ-anti-< -r<s) ,
        subst (λ z → ∣ x .lower z ∣) (sym (negℚ-invol s)) ls)
      (cut.lower-round x (-ℚ r) lr)
  ; upper-close = λ q<r lq → cut.lower-close x (negℚ-anti-< q<r) lq
  ; cut-disjoint = λ q uq lq → cut.cut-disjoint x (-ℚ q) lq uq
  ; cut-located = λ q<r → ∥-∥-map
      (λ { (inl l) → inr l ; (inr u) → inl u })
      (cut.cut-located x (negℚ-anti-< q<r))
  }

-ᴿ-invol : ∀ x → -ᴿ (-ᴿ x) ≡ x
-ᴿ-invol x = ℝ-path
  (funext λ q → ap (x .lower) (negℚ-invol q))
  (funext λ q → ap (x .upper) (negℚ-invol q))

-ᴿ-anti : ∀ {x y} → x <ᴿ y → (-ᴿ y) <ᴿ (-ᴿ x)
-ᴿ-anti {x} {y} = ∥-∥-map λ (q , ux , ly) →
  -ℚ q ,
  subst (λ z → ∣ y .lower z ∣) (sym (negℚ-invol q)) ly ,
  subst (λ z → ∣ x .upper z ∣) (sym (negℚ-invol q)) ux
```

## What arithmetic needs

Addition of cuts is Minkowski addition, and proving *its*
locatedness is the one place the archimedean property of the
rationals enters: one must approximate each summand by rationals to
within half the target gap, which is a finite search along an
arithmetic progression — constructively unproblematic, but requiring
an archimedean interface for `Ratio`{.Agda} (every rational is
bounded by a natural number, by induction on its fraction
representation) that the 1Lab does not yet provide. Multiplication
then follows the standard constructive treatment. With the field
structure in place, the classical smooth site comes into reach:
opens of $\bR^n$, and — after a constructive theory of $C^\infty$
maps — the good-open-cover coverage that the paper's diagram (7)
localises along. The reals as an *object*, with their order theory,
density of the rationals, and negation, are complete above.
