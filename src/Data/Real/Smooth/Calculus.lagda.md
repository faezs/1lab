<!--
```agda
open import 1Lab.Prelude

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative

open import Data.Fin.Properties using (finite-choice)
open import Data.Fin
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Calculus where
```

# The derivative calculus {defines="derivative-calculus"}

The [[derivative|real-derivative]] of a [[bounded-smooth
function|bounded-smooth-function]] is its depth-two Hadamard
quotient evaluated on the diagonal. Since every canonical
bounded-smooth structure — constants, projections, sums,
negations, products, composites — is assembled from an explicit
tower whose first quotient is a concrete formula, the derivative
of each construction *computes*. This module records the
resulting differentiation rules: the easy ones hold by
`refl`{.Agda}, the Leibniz rule needs one diagonal identification,
and the chain rule is an induction over the fuel of the
telescoping sum.

## Diagonal bookkeeping

Evaluating the tower combinators on the diagonal point
$(x_i, x)$ produces tuples like $j \mapsto (x_i \cdot x)(\sigma_i\,
j)$, which are extensionally the update of $x$ at $i$ by its own
value — that is, $x$ itself.

```agda
set-diag : ∀ {n} (x : Fin n → ℝ) (i : Fin n) → set x i (x i) ≡ x
set-diag {n} x i = funext go where
  go : ∀ j → set x i (x i) j ≡ x j
  go j with Discrete-Fin .decide i j
  ... | yes p = ap x p
  ... | no  _ = refl
```

## The easy rules

Constants have vanishing derivative — the constant tower's first
quotient is literally the zero function.

```agda
∂-const
  : ∀ {n} (c : ℝ) (i : Fin n) (x : Fin n → ℝ)
  → ∂-of (λ _ → c) i (smooth⁺-const c) x ≡ 0ᴿ
∂-const c i x = refl
```

A projection differentiates to the Kronecker delta. The
projection tower branches on whether the differentiation
direction hits the projected coordinate, so the proof branches on
the same decision; in each branch the quotient is a constant
function and the goal is `refl`{.Agda}.

```agda
∂-proj-same
  : ∀ {n} (j i : Fin n) (x : Fin n → ℝ) → i ≡ j
  → ∂-of (λ v → v j) i (smooth⁺-proj j) x ≡ 1ᴿ
∂-proj-same j i x i≡j with Discrete-Fin .decide i j
... | yes _ = refl
... | no ¬p = absurd (¬p i≡j)

∂-proj-diff
  : ∀ {n} (j i : Fin n) (x : Fin n → ℝ) → ¬ i ≡ j
  → ∂-of (λ v → v j) i (smooth⁺-proj j) x ≡ 0ᴿ
∂-proj-diff j i x i≢j with Discrete-Fin .decide i j
... | yes p = absurd (i≢j p)
... | no  _ = refl
```

Sums and negations differentiate pointwise, definitionally: the
first quotient of `tower-add`{.Agda} is the pointwise sum of the
first quotients, and likewise for `tower-neg`{.Agda}.

```agda
∂-add
  : ∀ {n} {f g : Fun n} (A : Smooth⁺ n f) (B : Smooth⁺ n g)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂-of (λ v → f v +ᴿ g v) i (smooth⁺-add A B) x
  ≡ ∂-of f i A x +ᴿ ∂-of g i B x
∂-add A B i x = refl

∂-neg
  : ∀ {n} {f : Fun n} (A : Smooth⁺ n f)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂-of (λ v → -ᴿ f v) i (smooth⁺-neg A) x ≡ -ᴿ ∂-of f i A x
∂-neg A i x = refl
```

## The Leibniz rule

The first quotient of a product evaluates one factor at the
unmoved tuple and the other at the $\sigma_i$-shuffled tuple. On
the diagonal the unmoved tuple is $x$ definitionally, and the
shuffled tuple is $x$ by the diagonal bookkeeping above — so the
Leibniz rule is a single `ap`{.Agda}.

```agda
∂-mul
  : ∀ {n} {f g : Fun n} (A : Smooth⁺ n f) (B : Smooth⁺ n g)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂-of (λ v → f v *ᴿ g v) i (smooth⁺-mul A B) x
  ≡ (f x *ᴿ ∂-of g i B x) +ᴿ (g x *ᴿ ∂-of f i A x)
∂-mul {f = f} {g = g} A B i x =
  ap (λ w → (f x *ᴿ ∂-of g i B x) +ᴿ (g w *ᴿ ∂-of f i A x))
    (σᵢ-set i x (x i) ∙ set-diag x i)
```

## The chain rule

The composite's first quotient is the fuel-indexed telescoping
sum `Comp.Qs`{.Agda}; on the diagonal each summand collapses to a
product of derivatives. We package the same fuel-indexed
recursion as a sum of reals, with the coordinate `fin c`{.Agda}
constructed exactly as in `Comp.Qs`{.Agda} so that the two
recursions stay definitionally aligned.

```agda
Σ-fuel : ∀ {m} (h : Fin m → ℝ) (fuel c : Nat) → c Nat.+ fuel ≡ m → ℝ
Σ-fuel h zero c eq = 0ᴿ
Σ-fuel {m} h (suc fuel) c eq =
  h cf +ᴿ Σ-fuel h fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq)
  where
  cf : Fin m
  cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
        (Nat.s≤s (le-plus c fuel)) ⦄

Σᴰ : ∀ {m} (h : Fin m → ℝ) → ℝ
Σᴰ {m} h = Σ-fuel h m 0 refl
```

The mixed frames of the telescope also collapse on the diagonal:
every coordinate of the frame tuple — moved, unmoved, or current
— evaluates to the corresponding component's value at $x$, by the
same $\sigma_i$ bookkeeping.

```agda
∂-chain
  : ∀ {n m} (F : Fin m → Fun n) (g : Fun m)
  → (SF : ∀ j → Smooth⁺ n (F j)) (Sg : Smooth⁺ m g)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂-of (λ v → g (λ j → F j v)) i (smooth⁺-comp SF Sg) x
  ≡ Σᴰ (λ j → ∂-of (F j) i (SF j) x *ᴿ ∂-of g j Sg (λ l → F l x))
∂-chain {n} {m} F g SF Sg i x = Qs-diag m 0 refl
  where
  TF : ∀ j → TowerTo 2 n (F j)
  TF j = SF j .fst 2

  Tg : TowerTo 2 m g
  Tg = Sg .fst 2

  summand : Fin m → ℝ
  summand j = ∂-of (F j) i (SF j) x *ᴿ ∂-of g j Sg (λ l → F l x)

  Frame-diag
    : (c : Nat) (cf : Fin m)
    → (λ l → Frame F i c cf l (cons (x i) x))
    ≡ cons (F cf x) (λ l → F l x)
  Frame-diag c cf = funext go where
    go : ∀ l → Frame F i c cf l (cons (x i) x)
       ≡ cons (F cf x) (λ l' → F l' x) l
    go l with fin-view l
    ... | zero = ap (F cf) (σᵢ-set i x (x i) ∙ set-diag x i)
    ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
    ...   | yes _ = ap (F l') (σᵢ-set i x (x i) ∙ set-diag x i)
    ...   | no  _ = refl

  Qs-diag
    : (fuel c : Nat) (eq : c Nat.+ fuel ≡ m)
    → Comp.Qs 1 F g TF Tg i fuel c eq (cons (x i) x)
    ≡ Σ-fuel summand fuel c eq
  Qs-diag zero c eq = refl
  Qs-diag (suc fuel) c eq =
    ap₂ _+ᴿ_
      (ap (λ w → TF cf i .fst (cons (x i) x) *ᴿ Tg cf .fst w)
        (Frame-diag c cf))
      (Qs-diag fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    where
    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄
```

## Descending to the truncation

Equations between reals are propositions, so every rule above
lifts through the propositional truncation of the bounded tower —
the form in which smooth structures are actually carried by the
[[ring of smooth functions|smooth-function]]. For the chain rule
the family of inner structures is collected with [[finite
choice|finite-choice]].

```agda
∂ᴿ-add
  : ∀ {n} {f g : Fun n}
  → (sf : ∥ Smooth⁺ n f ∥) (sg : ∥ Smooth⁺ n g ∥)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂ᴿ (λ v → f v +ᴿ g v) i (∥-∥-map₂ smooth⁺-add sf sg) x
  ≡ ∂ᴿ f i sf x +ᴿ ∂ᴿ g i sg x
∂ᴿ-add {n} {f} {g} sf sg i x = ∥-∥-elim₂
  {P = λ sf sg →
      ∂ᴿ (λ v → f v +ᴿ g v) i (∥-∥-map₂ smooth⁺-add sf sg) x
    ≡ ∂ᴿ f i sf x +ᴿ ∂ᴿ g i sg x}
  (λ _ _ → ℝ-is-set _ _)
  (λ A B → ∂-add A B i x)
  sf sg

∂ᴿ-neg
  : ∀ {n} {f : Fun n} (sf : ∥ Smooth⁺ n f ∥)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂ᴿ (λ v → -ᴿ f v) i (∥-∥-map smooth⁺-neg sf) x
  ≡ -ᴿ ∂ᴿ f i sf x
∂ᴿ-neg {n} {f} sf i x = ∥-∥-elim
  {P = λ sf →
      ∂ᴿ (λ v → -ᴿ f v) i (∥-∥-map smooth⁺-neg sf) x
    ≡ -ᴿ ∂ᴿ f i sf x}
  (λ _ → ℝ-is-set _ _)
  (λ A → ∂-neg A i x)
  sf

∂ᴿ-mul
  : ∀ {n} {f g : Fun n}
  → (sf : ∥ Smooth⁺ n f ∥) (sg : ∥ Smooth⁺ n g ∥)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂ᴿ (λ v → f v *ᴿ g v) i (∥-∥-map₂ smooth⁺-mul sf sg) x
  ≡ (f x *ᴿ ∂ᴿ g i sg x) +ᴿ (g x *ᴿ ∂ᴿ f i sf x)
∂ᴿ-mul {n} {f} {g} sf sg i x = ∥-∥-elim₂
  {P = λ sf sg →
      ∂ᴿ (λ v → f v *ᴿ g v) i (∥-∥-map₂ smooth⁺-mul sf sg) x
    ≡ (f x *ᴿ ∂ᴿ g i sg x) +ᴿ (g x *ᴿ ∂ᴿ f i sf x)}
  (λ _ _ → ℝ-is-set _ _)
  (λ A B → ∂-mul A B i x)
  sf sg

∂ᴿ-chain
  : ∀ {n m} (F : Fin m → Fun n) (g : Fun m)
  → (sF : ∀ j → ∥ Smooth⁺ n (F j) ∥) (sg : ∥ Smooth⁺ m g ∥)
  → (i : Fin n) (x : Fin n → ℝ)
  → ∂ᴿ (λ v → g (λ j → F j v)) i
      (∥-∥-map₂ smooth⁺-comp (finite-choice m sF) sg) x
  ≡ Σᴰ (λ j → ∂ᴿ (F j) i (sF j) x *ᴿ ∂ᴿ g j sg (λ l → F l x))
∂ᴿ-chain {n} {m} F g sF sg i x = ∥-∥-elim₂
  {P = λ sA sg →
      ∂ᴿ (λ v → g (λ j → F j v)) i (∥-∥-map₂ smooth⁺-comp sA sg) x
    ≡ Σᴰ (λ j → ∂ᴿ (F j) i (sF j) x *ᴿ ∂ᴿ g j sg (λ l → F l x))}
  (λ _ _ → ℝ-is-set _ _)
  (λ A B →
      ∂-chain F g A B i x
    ∙ ap Σᴰ (funext λ j →
        ap (λ s → ∂ᴿ (F j) i s x *ᴿ ∂-of g j B (λ l → F l x))
          (squash (inc (A j)) (sF j))))
  (finite-choice m sF) sg
```
