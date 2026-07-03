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
