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

## The meet of two reals

Dually, a rational lies below $\min(x,y)$ exactly when it lies below
*both*, and lies above $\min(x,y)$ exactly when it lies above one of
$x, y$.

```agda
minᴿ : ℝ → ℝ → ℝ
minᴿ x y .lower q = el (∣ x .lower q ∣ × ∣ y .lower q ∣)
  (×-is-hlevel 1 ((x .lower q) .is-tr) ((y .lower q) .is-tr))
minᴿ x y .upper q = elΩ (∣ x .upper q ∣ ⊎ ∣ y .upper q ∣)
minᴿ x y .has-is-cut = record
  { lower-inhab = ∥-∥-rec₂ squash
      (λ (v , lx) (w , ly) → inc
        ( minℚ v w
        , ≤-transport-lower x (minℚ-≤l {v} {w}) lx
        , ≤-transport-lower y (minℚ-≤r {v} {w}) ly
        ))
      (cut.lower-inhab x) (cut.lower-inhab y)

  ; upper-inhab = ∥-∥-map (λ (q , uq) → q , inc (inl uq)) (cut.upper-inhab x)

  ; lower-round = λ q (lx , ly) → ∥-∥-rec₂ squash
      (λ (v , q<v , lx') (w , q<w , ly') → inc
        ( minℚ v w
        , minℚ-glb q<v q<w
        , ≤-transport-lower x (minℚ-≤l {v} {w}) lx'
        , ≤-transport-lower y (minℚ-≤r {v} {w}) ly'
        ))
      (cut.lower-round x q lx) (cut.lower-round y q ly)

  ; lower-close = λ q<r (lr , lr') →
      cut.lower-close x q<r lr , cut.lower-close y q<r lr'

  ; upper-round = λ r → □-rec squash
      (λ where
        (inl uq) → ∥-∥-map (λ (q , q<r , uq') → q , q<r , inc (inl uq')) (cut.upper-round x r uq)
        (inr uq) → ∥-∥-map (λ (q , q<r , uq') → q , q<r , inc (inr uq')) (cut.upper-round y r uq))

  ; upper-close = λ q<r → □-map (λ where
      (inl uq) → inl (cut.upper-close x q<r uq)
      (inr uq) → inr (cut.upper-close y q<r uq))

  ; cut-disjoint = λ q (lq , lq') → □-rec (hlevel 1)
      (λ where
        (inl uq) → cut.cut-disjoint x q lq uq
        (inr uq) → cut.cut-disjoint y q lq' uq)

  ; cut-located = λ q<r → ∥-∥-rec₂ squash
      (λ where
        (inl lq)  (inl lq') → inc (inl (lq , lq'))
        (inl lq)  (inr uq)  → inc (inr (inc (inr uq)))
        (inr uq)  _         → inc (inr (inc (inl uq)))
      )
      (cut.cut-located x q<r) (cut.cut-located y q<r)
  }
```

## Lattice laws

Every law below reduces, via `≤ᴿ-antisym`{.Agda}, to a manipulation
of lower-cut inclusions — plain logic on `□`{.Agda} and `_⊎_`, with no
further appeal to the cut axioms. First, the two injections and the
universal property of the join.

```agda
maxᴿ-≤l : ∀ x y → x ≤ᴿ maxᴿ x y
maxᴿ-≤l x y q lq = inc (inl lq)

maxᴿ-≤r : ∀ x y → y ≤ᴿ maxᴿ x y
maxᴿ-≤r x y q lq = inc (inr lq)

maxᴿ-universal : ∀ {x y z} → x ≤ᴿ z → y ≤ᴿ z → maxᴿ x y ≤ᴿ z
maxᴿ-universal {x} {y} {z} p q r = □-rec ((z .lower r) .is-tr)
  (λ where
    (inl lx) → p r lx
    (inr ly) → q r ly)
```

The commutative, idempotent, and associative laws all follow purely
formally from the universal property together with the two
injections.

Every application of the universal properties below names its
implicit arguments explicitly: the goal types are inclusions of
*record projections* `_.lower`{.Agda} applied to the (as yet
unknown) join or meet, and Agda's unifier cannot invert through a
projection blocked on a metavariable, however obvious the intended
solution looks on paper.

```agda
maxᴿ-comm : ∀ x y → maxᴿ x y ≡ maxᴿ y x
maxᴿ-comm x y = ≤ᴿ-antisym p q
  where
  p : maxᴿ x y ≤ᴿ maxᴿ y x
  p = maxᴿ-universal {x = x} {y = y} {z = maxᴿ y x} (maxᴿ-≤r y x) (maxᴿ-≤l y x)
  q : maxᴿ y x ≤ᴿ maxᴿ x y
  q = maxᴿ-universal {x = y} {y = x} {z = maxᴿ x y} (maxᴿ-≤r x y) (maxᴿ-≤l x y)

maxᴿ-idem : ∀ x → maxᴿ x x ≡ x
maxᴿ-idem x = ≤ᴿ-antisym p (maxᴿ-≤l x x)
  where
  p : maxᴿ x x ≤ᴿ x
  p = maxᴿ-universal {x = x} {y = x} {z = x} (≤ᴿ-refl {x = x}) (≤ᴿ-refl {x = x})

maxᴿ-assoc : ∀ x y z → maxᴿ (maxᴿ x y) z ≡ maxᴿ x (maxᴿ y z)
maxᴿ-assoc x y z = ≤ᴿ-antisym p q
  where
  y≤yz : y ≤ᴿ maxᴿ y z
  y≤yz = maxᴿ-≤l y z
  z≤yz : z ≤ᴿ maxᴿ y z
  z≤yz = maxᴿ-≤r y z
  x≤xy : x ≤ᴿ maxᴿ x y
  x≤xy = maxᴿ-≤l x y
  y≤xy : y ≤ᴿ maxᴿ x y
  y≤xy = maxᴿ-≤r x y

  y≤xyz : y ≤ᴿ maxᴿ x (maxᴿ y z)
  y≤xyz = ≤ᴿ-trans {x = y} {y = maxᴿ y z} {z = maxᴿ x (maxᴿ y z)} y≤yz
            (maxᴿ-≤r x (maxᴿ y z))
  z≤xyz : z ≤ᴿ maxᴿ x (maxᴿ y z)
  z≤xyz = ≤ᴿ-trans {x = z} {y = maxᴿ y z} {z = maxᴿ x (maxᴿ y z)} z≤yz
            (maxᴿ-≤r x (maxᴿ y z))
  x≤xyz' : x ≤ᴿ maxᴿ (maxᴿ x y) z
  x≤xyz' = ≤ᴿ-trans {x = x} {y = maxᴿ x y} {z = maxᴿ (maxᴿ x y) z} x≤xy
             (maxᴿ-≤l (maxᴿ x y) z)
  y≤xyz' : y ≤ᴿ maxᴿ (maxᴿ x y) z
  y≤xyz' = ≤ᴿ-trans {x = y} {y = maxᴿ x y} {z = maxᴿ (maxᴿ x y) z} y≤xy
             (maxᴿ-≤l (maxᴿ x y) z)

  p : maxᴿ (maxᴿ x y) z ≤ᴿ maxᴿ x (maxᴿ y z)
  p = maxᴿ-universal {x = maxᴿ x y} {y = z} {z = maxᴿ x (maxᴿ y z)}
        (maxᴿ-universal {x = x} {y = y} {z = maxᴿ x (maxᴿ y z)} (maxᴿ-≤l x (maxᴿ y z)) y≤xyz)
        z≤xyz
  q : maxᴿ x (maxᴿ y z) ≤ᴿ maxᴿ (maxᴿ x y) z
  q = maxᴿ-universal {x = x} {y = maxᴿ y z} {z = maxᴿ (maxᴿ x y) z}
        x≤xyz'
        (maxᴿ-universal {x = y} {y = z} {z = maxᴿ (maxᴿ x y) z} y≤xyz' (maxᴿ-≤r (maxᴿ x y) z))
```

Dually for the meet: two projections, a universal property landing
*into* $\min(x,y)$, and the same three laws.

```agda
minᴿ-≥l : ∀ x y → minᴿ x y ≤ᴿ x
minᴿ-≥l x y q (lx , ly) = lx

minᴿ-≥r : ∀ x y → minᴿ x y ≤ᴿ y
minᴿ-≥r x y q (lx , ly) = ly

minᴿ-universal : ∀ {x y z} → z ≤ᴿ x → z ≤ᴿ y → z ≤ᴿ minᴿ x y
minᴿ-universal {x} {y} {z} p q r lr = p r lr , q r lr

minᴿ-comm : ∀ x y → minᴿ x y ≡ minᴿ y x
minᴿ-comm x y = ≤ᴿ-antisym p q
  where
  p : minᴿ x y ≤ᴿ minᴿ y x
  p = minᴿ-universal {x = y} {y = x} {z = minᴿ x y} (minᴿ-≥r x y) (minᴿ-≥l x y)
  q : minᴿ y x ≤ᴿ minᴿ x y
  q = minᴿ-universal {x = x} {y = y} {z = minᴿ y x} (minᴿ-≥r y x) (minᴿ-≥l y x)

minᴿ-idem : ∀ x → minᴿ x x ≡ x
minᴿ-idem x = ≤ᴿ-antisym (minᴿ-≥l x x) p
  where
  p : x ≤ᴿ minᴿ x x
  p = minᴿ-universal {x = x} {y = x} {z = x} (≤ᴿ-refl {x = x}) (≤ᴿ-refl {x = x})

minᴿ-assoc : ∀ x y z → minᴿ (minᴿ x y) z ≡ minᴿ x (minᴿ y z)
minᴿ-assoc x y z = ≤ᴿ-antisym p q
  where
  xy≤x : minᴿ x y ≤ᴿ x
  xy≤x = minᴿ-≥l x y
  xy≤y : minᴿ x y ≤ᴿ y
  xy≤y = minᴿ-≥r x y
  yz≤y : minᴿ y z ≤ᴿ y
  yz≤y = minᴿ-≥l y z
  yz≤z : minᴿ y z ≤ᴿ z
  yz≤z = minᴿ-≥r y z

  xyz≤x : minᴿ (minᴿ x y) z ≤ᴿ x
  xyz≤x = ≤ᴿ-trans {x = minᴿ (minᴿ x y) z} {y = minᴿ x y} {z = x}
            (minᴿ-≥l (minᴿ x y) z) xy≤x
  xyz≤y : minᴿ (minᴿ x y) z ≤ᴿ y
  xyz≤y = ≤ᴿ-trans {x = minᴿ (minᴿ x y) z} {y = minᴿ x y} {z = y}
            (minᴿ-≥l (minᴿ x y) z) xy≤y
  xyz≤y' : minᴿ x (minᴿ y z) ≤ᴿ y
  xyz≤y' = ≤ᴿ-trans {x = minᴿ x (minᴿ y z)} {y = minᴿ y z} {z = y}
             (minᴿ-≥r x (minᴿ y z)) yz≤y
  xyz≤z' : minᴿ x (minᴿ y z) ≤ᴿ z
  xyz≤z' = ≤ᴿ-trans {x = minᴿ x (minᴿ y z)} {y = minᴿ y z} {z = z}
             (minᴿ-≥r x (minᴿ y z)) yz≤z

  p : minᴿ (minᴿ x y) z ≤ᴿ minᴿ x (minᴿ y z)
  p = minᴿ-universal {x = x} {y = minᴿ y z} {z = minᴿ (minᴿ x y) z}
        xyz≤x
        (minᴿ-universal {x = y} {y = z} {z = minᴿ (minᴿ x y) z} xyz≤y (minᴿ-≥r (minᴿ x y) z))
  q : minᴿ x (minᴿ y z) ≤ᴿ minᴿ (minᴿ x y) z
  q = minᴿ-universal {x = minᴿ x y} {y = z} {z = minᴿ x (minᴿ y z)}
        (minᴿ-universal {x = x} {y = y} {z = minᴿ x (minᴿ y z)} (minᴿ-≥l x (minᴿ y z)) xyz≤y')
        xyz≤z'
```

## Absolute value

The absolute value is the join of a real with its negation — the
smallest real that dominates both $x$ and $-x$.

```agda
absᴿ : ℝ → ℝ
absᴿ x = maxᴿ x (-ᴿ x)

absᴿ-≥ : ∀ x → x ≤ᴿ absᴿ x
absᴿ-≥ x = maxᴿ-≤l x (-ᴿ x)

absᴿ-≥' : ∀ x → (-ᴿ x) ≤ᴿ absᴿ x
absᴿ-≥' x = maxᴿ-≤r x (-ᴿ x)

absᴿ-neg : ∀ x → absᴿ (-ᴿ x) ≡ absᴿ x
absᴿ-neg x =
  maxᴿ (-ᴿ x) (-ᴿ (-ᴿ x))  ≡⟨ ap (maxᴿ (-ᴿ x)) (-ᴿ-invol x) ⟩
  maxᴿ (-ᴿ x) x            ≡⟨ maxᴿ-comm (-ᴿ x) x ⟩
  maxᴿ x (-ᴿ x)            ∎
```

Finally, the absorption law linking the two operations: joining $x$
with anything smaller than it — in particular with $\min(x,y)$ — just
gives back $x$.

```agda
max-min-absorb : ∀ x y → maxᴿ x (minᴿ x y) ≡ x
max-min-absorb x y = ≤ᴿ-antisym p (maxᴿ-≤l x (minᴿ x y))
  where
  p : maxᴿ x (minᴿ x y) ≤ᴿ x
  p = maxᴿ-universal {x = x} {y = minᴿ x y} {z = x} (≤ᴿ-refl {x = x}) (minᴿ-≥l x y)
```
