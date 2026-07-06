<!--
```agda
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Rational where
```

# A rational toolkit for the reals {defines="rational-toolkit"}

The construction of the [[Dedekind reals|dedekind-real]] and their
[[order|real-lattice]], [[addition|real-addition]] and
[[multiplication|real-multiplication]] all rest on the same body of
rational arithmetic that the 1Lab's `Data.Rational`{.Agda} interface
does not itself provide: strict-order arithmetic, halving and
midpoints, monotonicity of multiplication, and the binary and
four-fold minima and maxima with their lattice laws. Rather than
re-derive this toolkit in each module, we collect it here once.

Equational goals with no division are dispatched by the rational
ring solver `rational!`{.Agda}; the few facts that genuinely involve
$\tfrac12$ (whose nonzeroness the solver does not see through) are
proved by hand.

## Halving and strict order

<!--
```agda
instance
  2-nonzero : Nonzero 2
  2-nonzero = inc (λ p → <-irrefl (sym p) 0<2) where
    0<2 : 0 < 2
    0<2 = decide!

half : Ratio → Ratio
half x = x *ℚ invℚ 2

midpoint : Ratio → Ratio → Ratio
midpoint x y = half (x +ℚ y)

abstract
  ≤-resp : ∀ {a b a' b'} → a ≡ a' → b ≡ b' → a ≤ b → a' ≤ b'
  ≤-resp p q r = transport (λ i → (p i) ≤ (q i)) r

  <-resp : ∀ {a b a' b'} → a ≡ a' → b ≡ b' → a < b → a' < b'
  <-resp p q r = transport (λ i → (p i) < (q i)) r

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
  negℚ-invol q = rational!

  neg-zero : Path Ratio (-ℚ 0) 0
  neg-zero = decide!

  ≤→diff-nonneg : ∀ {u v} → u ≤ v → 0 ≤ (v +ℚ (-ℚ u))
  ≤→diff-nonneg {u} {v} p = ≤-resp (+ℚ-invr u) refl (+ℚ-preserves-≤ p (≤-refl { -ℚ u}))

  negℚ-anti-≤ : ∀ {x y} → x ≤ y → (-ℚ y) ≤ (-ℚ x)
  negℚ-anti-≤ {x} {y} p = ≤-resp eq1 eq2 (+ℚ-preserves-≤ p (≤-refl {(-ℚ x) +ℚ (-ℚ y)}))
    where
    eq1 : x +ℚ ((-ℚ x) +ℚ (-ℚ y)) ≡ -ℚ y
    eq1 = rational!
    eq2 : y +ℚ ((-ℚ x) +ℚ (-ℚ y)) ≡ -ℚ x
    eq2 = rational!

  negatel : ∀ a b → (-ℚ a) *ℚ b ≡ -ℚ (a *ℚ b)
  negatel a b = rational!

  x+x≡x*2 : ∀ x → x +ℚ x ≡ x *ℚ 2
  x+x≡x*2 x = sym $
    x *ℚ 2               ≡⟨ ap (x *ℚ_) two ⟩
    x *ℚ (1 +ℚ 1)        ≡⟨ *ℚ-distribl x 1 1 ⟩
    (x *ℚ 1) +ℚ (x *ℚ 1) ≡⟨ ap₂ _+ℚ_ (*ℚ-idr x) (*ℚ-idr x) ⟩
    x +ℚ x               ∎
    where
    two : Path Ratio 2 (1 +ℚ 1)
    two = decide!

  half-zero : half 0 ≡ 0
  half-zero = decide!

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

  half-pos : ∀ {ε} → 0 < ε → 0 < half ε
  half-pos {ε} p = transport (λ i → half-zero i < half ε) (half-< p)

  half-lt : ∀ {ε} → 0 < ε → half ε < ε
  half-lt {ε} p = transport (λ i → +ℚ-idl (half ε) i < half-sum ε i)
    (+ℚ-preserves-<r (half ε) (half-pos p))

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
    rhs = rational!

  0≤1' : 0 ≤ 1
  0≤1' = decide!

  0<1' : 0 < 1
  0<1' = decide!

  sub-pos-< : ∀ z ε → 0 < ε → (z +ℚ (-ℚ ε)) < z
  sub-pos-< z ε e = <-resp refl (+ℚ-idr z) (+ℚ-preserves-<l z neg<0)
    where
    neg<0 : (-ℚ ε) < 0
    neg<0 = <-resp refl neg-zero (negℚ-anti-< e)

  add-pos-< : ∀ z ε → 0 < ε → z < (z +ℚ ε)
  add-pos-< z ε e = <-resp (+ℚ-idr z) refl (+ℚ-preserves-<l z e)
```
-->

## Monotonicity of multiplication

<!--
```agda
abstract
  *ℚ-preserves-≤r : ∀ {u v} w → u ≤ v → 0 ≤ w → (u *ℚ w) ≤ (v *ℚ w)
  *ℚ-preserves-≤r {u} {v} w p q = ≤-resp (+ℚ-idl (u *ℚ w)) eq base
    where
    base : (0 +ℚ (u *ℚ w)) ≤ (((v +ℚ (-ℚ u)) *ℚ w) +ℚ (u *ℚ w))
    base = +ℚ-preserves-≤ (*ℚ-nonnegative (≤→diff-nonneg p) q) (≤-refl {u *ℚ w})

    eq : ((v +ℚ (-ℚ u)) *ℚ w) +ℚ (u *ℚ w) ≡ v *ℚ w
    eq = rational!

  *ℚ-preserves-≤l : ∀ {u v} w → 0 ≤ w → u ≤ v → (w *ℚ u) ≤ (w *ℚ v)
  *ℚ-preserves-≤l {u} {v} w q p = ≤-resp (*ℚ-commutative u w) (*ℚ-commutative v w)
    (*ℚ-preserves-≤r w p q)

  *ℚ-preserves-<r : ∀ {u v} w → u < v → 0 < w → (u *ℚ w) < (v *ℚ w)
  *ℚ-preserves-<r {u} {v} w p q = positive-diff→< (transport (λ i → 0 < expand i) diff-pos)
    where
    diff-pos : 0 < (v +ℚ (-ℚ u)) *ℚ w
    diff-pos = from-positive (*ℚ-positive (to-positive (<→positive-diff p)) (to-positive q))

    expand : (v +ℚ (-ℚ u)) *ℚ w ≡ (v *ℚ w) +ℚ (-ℚ (u *ℚ w))
    expand = *ℚ-distribr w v (-ℚ u) ∙ ap (v *ℚ w +ℚ_) (negatel u w)

  /ℚ-cancel : ∀ x y ⦃ p : Nonzero y ⦄ → (x /ℚ y) *ℚ y ≡ x
  /ℚ-cancel x y = ap (_*ℚ y) /ℚ-def ∙ sym (*ℚ-associative x (invℚ y) y) ∙ ap (x *ℚ_) *ℚ-invl ∙ *ℚ-idr x

  div-pos : ∀ n d ⦃ nz : Nonzero d ⦄ → 0 < n → 0 < d → 0 < (n /ℚ d) ⦃ nz ⦄
  div-pos n d ⦃ nz ⦄ np dp with holds? (0 < (n /ℚ d) ⦃ nz ⦄)
  ... | yes p = p
  ... | no ¬p = absurd (<-irrefl refl (≤-<-trans n≤0 np))
    where
    n≤0 : n ≤ 0
    n≤0 = ≤-resp (/ℚ-cancel n d ⦃ nz ⦄) (*ℚ-zerol d)
      (*ℚ-preserves-≤r d (¬<→≥ ¬p) (<-weaken dp))
```
-->

## Binary and four-fold extrema

The rational order is decidable, so binary minima and maxima exist
by case analysis. On top of them we define the four-fold versions,
with their universal properties and — crucial for the width
estimates of the [[interval product|real-multiplication]] — the fact
that a four-fold minimum or maximum *is one of* its arguments.

```agda
maxℚ minℚ : Ratio → Ratio → Ratio
maxℚ x y with holds? (x ≤ y)
... | yes _ = y
... | no _  = x

minℚ x y with holds? (x ≤ y)
... | yes _ = x
... | no _  = y

min₄ max₄ : Ratio → Ratio → Ratio → Ratio → Ratio
min₄ p q r s = minℚ (minℚ p q) (minℚ r s)
max₄ p q r s = maxℚ (maxℚ p q) (maxℚ r s)
```

<!--
```agda
abstract
  maxℚ-≤l : ∀ {x y} → x ≤ maxℚ x y
  maxℚ-≤l {x} {y} with holds? (x ≤ y)
  ... | yes p = p
  ... | no _  = ≤-refl

  maxℚ-≤r : ∀ {x y} → y ≤ maxℚ x y
  maxℚ-≤r {x} {y} with holds? (x ≤ y)
  ... | yes _ = ≤-refl
  ... | no ¬p = ≤-is-weakly-total x y ¬p

  maxℚ-lub : ∀ {x y z} → x < z → y < z → maxℚ x y < z
  maxℚ-lub {x} {y} {z} p q with holds? (x ≤ y)
  ... | yes _ = q
  ... | no _  = p

  maxℚ-lub-≤ : ∀ {x y z} → x ≤ z → y ≤ z → maxℚ x y ≤ z
  maxℚ-lub-≤ {x} {y} {z} p q with holds? (x ≤ y)
  ... | yes _ = q
  ... | no _  = p

  minℚ-≤l : ∀ {x y} → minℚ x y ≤ x
  minℚ-≤l {x} {y} with holds? (x ≤ y)
  ... | yes _ = ≤-refl
  ... | no ¬p = ≤-is-weakly-total x y ¬p

  minℚ-≤r : ∀ {x y} → minℚ x y ≤ y
  minℚ-≤r {x} {y} with holds? (x ≤ y)
  ... | yes p = p
  ... | no _  = ≤-refl

  minℚ-glb : ∀ {x y z} → z < x → z < y → z < minℚ x y
  minℚ-glb {x} {y} {z} p q with holds? (x ≤ y)
  ... | yes _ = p
  ... | no _  = q

  minℚ-glb-≤ : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ minℚ x y
  minℚ-glb-≤ {x} {y} {z} p q with holds? (x ≤ y)
  ... | yes _ = p
  ... | no _  = q

  minℚ-choice : ∀ x y → (minℚ x y ≡ x) ⊎ (minℚ x y ≡ y)
  minℚ-choice x y with holds? (x ≤ y)
  ... | yes _ = inl refl
  ... | no _  = inr refl

  maxℚ-choice : ∀ x y → (maxℚ x y ≡ x) ⊎ (maxℚ x y ≡ y)
  maxℚ-choice x y with holds? (x ≤ y)
  ... | yes _ = inr refl
  ... | no _  = inl refl

  min₄-≤₁ : ∀ {p q r s} → min₄ p q r s ≤ p
  min₄-≤₁ {p} {q} {r} {s} = ≤-trans (minℚ-≤l {minℚ p q} {minℚ r s}) (minℚ-≤l {p} {q})

  min₄-≤₂ : ∀ {p q r s} → min₄ p q r s ≤ q
  min₄-≤₂ {p} {q} {r} {s} = ≤-trans (minℚ-≤l {minℚ p q} {minℚ r s}) (minℚ-≤r {p} {q})

  min₄-≤₃ : ∀ {p q r s} → min₄ p q r s ≤ r
  min₄-≤₃ {p} {q} {r} {s} = ≤-trans (minℚ-≤r {minℚ p q} {minℚ r s}) (minℚ-≤l {r} {s})

  min₄-≤₄ : ∀ {p q r s} → min₄ p q r s ≤ s
  min₄-≤₄ {p} {q} {r} {s} = ≤-trans (minℚ-≤r {minℚ p q} {minℚ r s}) (minℚ-≤r {r} {s})

  min₄-univ : ∀ {p q r s z} → z ≤ p → z ≤ q → z ≤ r → z ≤ s → z ≤ min₄ p q r s
  min₄-univ hp hq hr hs = minℚ-glb-≤ (minℚ-glb-≤ hp hq) (minℚ-glb-≤ hr hs)

  min₄-univ-< : ∀ {p q r s z} → z < p → z < q → z < r → z < s → z < min₄ p q r s
  min₄-univ-< hp hq hr hs = minℚ-glb (minℚ-glb hp hq) (minℚ-glb hr hs)

  max₄-≥₁ : ∀ {p q r s} → p ≤ max₄ p q r s
  max₄-≥₁ {p} {q} {r} {s} = ≤-trans (maxℚ-≤l {p} {q}) (maxℚ-≤l {maxℚ p q} {maxℚ r s})

  max₄-≥₂ : ∀ {p q r s} → q ≤ max₄ p q r s
  max₄-≥₂ {p} {q} {r} {s} = ≤-trans (maxℚ-≤r {p} {q}) (maxℚ-≤l {maxℚ p q} {maxℚ r s})

  max₄-≥₃ : ∀ {p q r s} → r ≤ max₄ p q r s
  max₄-≥₃ {p} {q} {r} {s} = ≤-trans (maxℚ-≤l {r} {s}) (maxℚ-≤r {maxℚ p q} {maxℚ r s})

  max₄-≥₄ : ∀ {p q r s} → s ≤ max₄ p q r s
  max₄-≥₄ {p} {q} {r} {s} = ≤-trans (maxℚ-≤r {r} {s}) (maxℚ-≤r {maxℚ p q} {maxℚ r s})

  max₄-univ : ∀ {p q r s z} → p ≤ z → q ≤ z → r ≤ z → s ≤ z → max₄ p q r s ≤ z
  max₄-univ hp hq hr hs = maxℚ-lub-≤ (maxℚ-lub-≤ hp hq) (maxℚ-lub-≤ hr hs)

  max₄-univ-< : ∀ {p q r s z} → p < z → q < z → r < z → s < z → max₄ p q r s < z
  max₄-univ-< hp hq hr hs = maxℚ-lub (maxℚ-lub hp hq) (maxℚ-lub hr hs)

  min₄-choice
    : ∀ p q r s
    → (min₄ p q r s ≡ p) ⊎ ((min₄ p q r s ≡ q) ⊎ ((min₄ p q r s ≡ r) ⊎ (min₄ p q r s ≡ s)))
  min₄-choice p q r s with minℚ-choice (minℚ p q) (minℚ r s) | minℚ-choice p q | minℚ-choice r s
  ... | inl e | inl e' | _      = inl (e ∙ e')
  ... | inl e | inr e' | _      = inr (inl (e ∙ e'))
  ... | inr e | _      | inl e' = inr (inr (inl (e ∙ e')))
  ... | inr e | _      | inr e' = inr (inr (inr (e ∙ e')))
```
-->
