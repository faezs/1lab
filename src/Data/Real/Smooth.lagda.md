<!--
```agda
open import 1Lab.Prelude

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base

open import Data.Fin
open import Data.Dec

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth where
```

# Smooth functions on the Dedekind reals {defines="smooth-function hadamard-tower"}

The paper's site of probes has the Cartesian spaces $\bR^n$ as
objects and the *smooth* maps between them as morphisms. What makes
a function of real variables smooth, constructively and with no
recourse to limits, is **Hadamard's characterization**: $f$ is
$C^1$ exactly when its difference quotients extend to the diagonal
— when there is a function $g$ with

$$
f(x) - f(x[i \mapsto t]) = (x_i - t)\, g(t, x)
$$

— and $f$ is $C^{k+1}$ when moreover each such $g$ is $C^k$. A
function is **smooth** when it carries a Hadamard tower of every
finite depth. The definition is entirely algebraic in the
[[ring of Dedekind reals|dedekind-reals]]: differentiation is
division that has already happened.

```agda
Fun : Nat → Type
Fun n = (Fin n → ℝ) → ℝ

cons : ∀ {n} → ℝ → (Fin n → ℝ) → Fin (suc n) → ℝ
cons t x i with fin-view i
... | zero  = t
... | suc j = x j

set : ∀ {n} → (Fin n → ℝ) → Fin n → ℝ → (Fin n → ℝ)
set x i t j with Discrete-Fin {n = _} .decide i j
... | yes _ = t
... | no  _ = x j

_−ᴿ_ : ℝ → ℝ → ℝ
a −ᴿ b = a +ᴿ (-ᴿ b)

Quot : (n : Nat) → Fun n → Fin n → Fun (suc n) → Type
Quot n f i g =
  (x : Fin n → ℝ) (t : ℝ)
  → f x −ᴿ f (set x i t) ≡ (x i −ᴿ t) *ᴿ g (cons t x)

TowerTo : Nat → (n : Nat) → Fun n → Type
TowerTo zero n f = Lift lzero ⊤
TowerTo (suc k) n f =
  (i : Fin n) →
    Σ[ g ∈ Fun (suc n) ] (Quot n f i g × TowerTo k (suc n) g)

Smooth : (n : Nat) → Fun n → Type
Smooth n f = (k : Nat) → TowerTo k n f
```

## Ring bookkeeping

<!--
```agda
private
  set-same : ∀ {n} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) → set x i t i ≡ t
  set-same x i t with Discrete-Fin .decide i i
  ... | yes _ = refl
  ... | no ¬p = absurd (¬p refl)

  set-other
    : ∀ {n} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ)
    → ¬ (i ≡ j) → set x i t j ≡ x j
  set-other x i j t ne with Discrete-Fin .decide i j
  ... | yes p = absurd (ne p)
  ... | no  _ = refl

  +ᴿ-idl : ∀ x → 0ᴿ +ᴿ x ≡ x
  +ᴿ-idl x = +ᴿ-comm 0ᴿ x ∙ +ᴿ-idr x

  +ᴿ-invl : ∀ x → (-ᴿ x) +ᴿ x ≡ 0ᴿ
  +ᴿ-invl x = +ᴿ-comm (-ᴿ x) x ∙ +ᴿ-invr x

  neg-unique : ∀ x y → x +ᴿ y ≡ 0ᴿ → y ≡ -ᴿ x
  neg-unique x y p =
      sym (+ᴿ-idl y)
    ∙ ap (_+ᴿ y) (sym (+ᴿ-invl x))
    ∙ sym (+ᴿ-assoc (-ᴿ x) x y)
    ∙ ap ((-ᴿ x) +ᴿ_) p
    ∙ +ᴿ-idr (-ᴿ x)

  interchange
    : ∀ a b c d → (a +ᴿ b) +ᴿ (c +ᴿ d) ≡ (a +ᴿ c) +ᴿ (b +ᴿ d)
  interchange a b c d =
      sym (+ᴿ-assoc a b (c +ᴿ d))
    ∙ ap (a +ᴿ_)
        ( +ᴿ-assoc b c d
        ∙ ap (_+ᴿ d) (+ᴿ-comm b c)
        ∙ sym (+ᴿ-assoc c b d))
    ∙ +ᴿ-assoc a c (b +ᴿ d)

  neg-distr : ∀ a b → -ᴿ (a +ᴿ b) ≡ (-ᴿ a) +ᴿ (-ᴿ b)
  neg-distr a b = sym (neg-unique (a +ᴿ b) ((-ᴿ a) +ᴿ (-ᴿ b))
    ( interchange a b (-ᴿ a) (-ᴿ b)
    ∙ ap₂ _+ᴿ_ (+ᴿ-invr a) (+ᴿ-invr b)
    ∙ +ᴿ-idr 0ᴿ))

  neg-invol : ∀ a → -ᴿ (-ᴿ a) ≡ a
  neg-invol a = sym (neg-unique (-ᴿ a) a (+ᴿ-invl a))

  *ᴿ-absorbr : ∀ x → x *ᴿ 0ᴿ ≡ 0ᴿ
  *ᴿ-absorbr x =
      sym (+ᴿ-idr (x *ᴿ 0ᴿ))
    ∙ ap ((x *ᴿ 0ᴿ) +ᴿ_) (sym (+ᴿ-invr (x *ᴿ 0ᴿ)))
    ∙ +ᴿ-assoc (x *ᴿ 0ᴿ) (x *ᴿ 0ᴿ) (-ᴿ (x *ᴿ 0ᴿ))
    ∙ ap (_+ᴿ (-ᴿ (x *ᴿ 0ᴿ)))
        ( sym (*ᴿ-distribˡ x 0ᴿ 0ᴿ)
        ∙ ap (x *ᴿ_) (+ᴿ-idr 0ᴿ))
    ∙ +ᴿ-invr (x *ᴿ 0ᴿ)

  *ᴿ-negr : ∀ a b → a *ᴿ (-ᴿ b) ≡ -ᴿ (a *ᴿ b)
  *ᴿ-negr a b = neg-unique (a *ᴿ b) (a *ᴿ (-ᴿ b))
    ( sym (*ᴿ-distribˡ a b (-ᴿ b))
    ∙ ap (a *ᴿ_) (+ᴿ-invr b)
    ∙ *ᴿ-absorbr a)

  diff-neg : ∀ a b → (-ᴿ a) −ᴿ (-ᴿ b) ≡ -ᴿ (a −ᴿ b)
  diff-neg a b =
      ap ((-ᴿ a) +ᴿ_) (neg-invol b)
    ∙ ap ((-ᴿ a) +ᴿ_) (sym (neg-invol b))
    ∙ sym (neg-distr a (-ᴿ b))
```
-->

## Closure under the ring operations

Constants and coordinate projections are smooth, and smoothness is
closed under pointwise negation and addition — each combinator
computes the quotient tower explicitly, by induction on the depth.

```agda
tower-const : ∀ k n (c : ℝ) → TowerTo k n (λ _ → c)
tower-const zero n c = lift tt
tower-const (suc k) n c i =
    (λ _ → 0ᴿ)
  , (λ x t → +ᴿ-invr c ∙ sym (*ᴿ-absorbr (x i −ᴿ t)))
  , tower-const k (suc n) 0ᴿ

tower-proj : ∀ k n (j : Fin n) → TowerTo k n (λ x → x j)
tower-proj zero n j = lift tt
tower-proj (suc k) n j i with Discrete-Fin .decide i j
... | yes p =
    (λ _ → 1ᴿ)
  , (λ x t →
        ap (λ z → x z −ᴿ t) (sym p)
      ∙ sym (*ᴿ-idr (x i −ᴿ t)))
  , tower-const k (suc n) 1ᴿ
... | no ¬p =
    (λ _ → 0ᴿ)
  , (λ x t →
        +ᴿ-invr (x j)
      ∙ sym (*ᴿ-absorbr (x i −ᴿ t)))
  , tower-const k (suc n) 0ᴿ

tower-neg
  : ∀ k n (f : Fun n)
  → TowerTo k n f → TowerTo k n (λ x → -ᴿ f x)
tower-neg zero n f _ = lift tt
tower-neg (suc k) n f T i =
  let (g , q , T') = T i in
    (λ y → -ᴿ g y)
  , (λ x t →
        diff-neg (f x) (f (set x i t))
      ∙ ap -ᴿ_ (q x t)
      ∙ sym (*ᴿ-negr (x i −ᴿ t) (g (cons t x))))
  , tower-neg k (suc n) g T'

tower-add
  : ∀ k n (f g : Fun n)
  → TowerTo k n f → TowerTo k n g
  → TowerTo k n (λ x → f x +ᴿ g x)
tower-add zero n f g _ _ = lift tt
tower-add (suc k) n f g T S i =
  let (gf , qf , T') = T i
      (gg , qg , S') = S i
  in
    (λ y → gf y +ᴿ gg y)
  , (λ x t →
        ap ((f x +ᴿ g x) +ᴿ_)
          (neg-distr (f (set x i t)) (g (set x i t)))
      ∙ interchange (f x) (g x)
          (-ᴿ f (set x i t)) (-ᴿ g (set x i t))
      ∙ ap₂ _+ᴿ_ (qf x t) (qg x t)
      ∙ sym (*ᴿ-distribˡ (x i −ᴿ t) (gf (cons t x)) (gg (cons t x))))
  , tower-add k (suc n) gf gg T' S'

smooth-const : ∀ {n} (c : ℝ) → Smooth n (λ _ → c)
smooth-const c k = tower-const k _ c

smooth-proj : ∀ {n} (j : Fin n) → Smooth n (λ x → x j)
smooth-proj j k = tower-proj k _ j

smooth-neg : ∀ {n} {f : Fun n} → Smooth n f → Smooth n (λ x → -ᴿ f x)
smooth-neg S k = tower-neg k _ _ (S k)

smooth-add
  : ∀ {n} {f g : Fun n}
  → Smooth n f → Smooth n g → Smooth n (λ x → f x +ᴿ g x)
smooth-add S T k = tower-add k _ _ _ (S k) (T k)
```
