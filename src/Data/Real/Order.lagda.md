<!--
```agda
open import 1Lab.Truncation
open import 1Lab.Resizing
open import 1Lab.Prelude

open import Data.Rational.Properties
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Base
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.Real.Order where
```

# The lattice of real numbers {defines="real-lattice real-absolute-value"}

The Dedekind reals carry a **lattice** structure induced pointwise
from their cuts: the join of two reals takes the union of the
rationals below each (a rational is below the join iff it is below
one of the summands), and the meet takes the intersection (a rational
is below the meet iff it is below both). Dually the upper cuts take
the intersection and union respectively, and negation exchanges the
two operations — reflecting the familiar fact that $\max(x, y) = -
\min(-x, -y)$.

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)
```
-->

## Maximum and minimum of rationals

The rational order is decidable, so we may define the binary maximum
and minimum by case analysis, entirely by hand — the 1Lab's rational
interface does not (yet) provide these.

```agda
private
  maxℚ minℚ : Ratio → Ratio → Ratio
  maxℚ x y with holds? (x ≤ y)
  ... | yes _ = y
  ... | no _  = x

  minℚ x y with holds? (x ≤ y)
  ... | yes _ = x
  ... | no _  = y
```

<!--
```agda
private abstract
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

  maxℚ-choice : ∀ {x y} → (maxℚ x y ≡ x) ⊎ (maxℚ x y ≡ y)
  maxℚ-choice {x} {y} with holds? (x ≤ y)
  ... | yes _ = inr refl
  ... | no _  = inl refl

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

  minℚ-choice : ∀ {x y} → (minℚ x y ≡ x) ⊎ (minℚ x y ≡ y)
  minℚ-choice {x} {y} with holds? (x ≤ y)
  ... | yes _ = inl refl
  ... | no _  = inr refl
```
-->

A rational $q$ that lies below one of $x, y$, or lies weakly below
the maximum of two witnesses of the upper cuts, still lies in the
corresponding cut at the rounded target — a fact needed repeatedly
below, since `maxℚ`{.Agda}'s two defining inequalities are only
*weak*.

<!--
```agda
private abstract
  ≤-transport-upper
    : ∀ (x : ℝ) {q r} → q ≤ r → ∣ x .upper q ∣ → ∣ x .upper r ∣
  ≤-transport-upper x {q} {r} p uq with ≤-strengthen p
  ... | inl e  = subst (λ z → ∣ x .upper z ∣) e uq
  ... | inr lt = cut.upper-close x lt uq

  ≤-transport-lower
    : ∀ (x : ℝ) {q r} → q ≤ r → ∣ x .lower r ∣ → ∣ x .lower q ∣
  ≤-transport-lower x {q} {r} p lr with ≤-strengthen p
  ... | inl e  = subst (λ z → ∣ x .lower z ∣) (sym e) lr
  ... | inr lt = cut.lower-close x lt lr
```
-->

## The join of two reals

A rational lies below $\max(x, y)$ exactly when it lies below $x$ or
below $y$; it lies above $\max(x,y)$ exactly when it lies above
*both*. The former is a disjunction, resized into $\Omega$ via
`elΩ`{.Agda}; the latter is already a proposition, being a product of
two propositions.

```agda
maxᴿ : ℝ → ℝ → ℝ
maxᴿ x y .lower q = elΩ (∣ x .lower q ∣ ⊎ ∣ y .lower q ∣)
maxᴿ x y .upper q = el (∣ x .upper q ∣ × ∣ y .upper q ∣)
  (×-is-hlevel 1 ((x .upper q) .is-tr) ((y .upper q) .is-tr))
maxᴿ x y .has-is-cut = record
  { lower-inhab = ∥-∥-map (λ (q , lq) → q , inc (inl lq)) (cut.lower-inhab x)

  ; upper-inhab = ∥-∥-rec₂ squash
      (λ (v , ux) (w , uy) → inc
        ( maxℚ v w
        , ≤-transport-upper x (maxℚ-≤l {v} {w}) ux
        , ≤-transport-upper y (maxℚ-≤r {v} {w}) uy
        ))
      (cut.upper-inhab x) (cut.upper-inhab y)

  ; lower-round = λ q → □-rec squash
      (λ where
        (inl lq) → ∥-∥-map (λ (r , q<r , lr) → r , q<r , inc (inl lr)) (cut.lower-round x q lq)
        (inr lq) → ∥-∥-map (λ (r , q<r , lr) → r , q<r , inc (inr lr)) (cut.lower-round y q lq))

  ; lower-close = λ q<r → □-map (λ where
      (inl lr) → inl (cut.lower-close x q<r lr)
      (inr lr) → inr (cut.lower-close y q<r lr))

  ; upper-round = λ r (ux , uy) → ∥-∥-rec₂ squash
      (λ (v , v<r , ux') (w , w<r , uy') → inc
        ( maxℚ v w
        , maxℚ-lub v<r w<r
        , ≤-transport-upper x (maxℚ-≤l {v} {w}) ux'
        , ≤-transport-upper y (maxℚ-≤r {v} {w}) uy'
        ))
      (cut.upper-round x r ux) (cut.upper-round y r uy)

  ; upper-close = λ q<r (uq , uq') →
      cut.upper-close x q<r uq , cut.upper-close y q<r uq'

  ; cut-disjoint = λ q lq (uq , uq') → □-rec (hlevel 1)
      (λ where
        (inl lq') → cut.cut-disjoint x q lq' uq
        (inr lq') → cut.cut-disjoint y q lq' uq')
      lq

  ; cut-located = λ q<r → ∥-∥-rec₂ squash
      (λ where
        (inl lq) _         → inc (inl (inc (inl lq)))
        (inr uq) (inl lq)  → inc (inl (inc (inr lq)))
        (inr uq) (inr uq') → inc (inr (uq , uq'))
      )
      (cut.cut-located x q<r) (cut.cut-located y q<r)
  }
```
