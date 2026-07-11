<!--
```agda
open import 1Lab.Prelude

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base

open import Data.Fin
open import Data.Dec
open import Data.Sum

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

## Renaming variables

Smoothness is closed under precomposition with an injective
renaming of variables: a direction either misses the image — the
quotient is zero — or has a unique preimage, and the quotient is
the renamed quotient in that direction, with the renaming lifted
under the fresh variable.

<!--
```agda
private
  lift-ρ : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  lift-ρ ρ j with fin-view j
  ... | zero   = fzero
  ... | suc j' = fsuc (ρ j')

  lift-ρ-inj
    : ∀ {n m} (ρ : Fin n → Fin m)
    → (∀ a b → ρ a ≡ ρ b → a ≡ b)
    → ∀ a b → lift-ρ ρ a ≡ lift-ρ ρ b → a ≡ b
  lift-ρ-inj ρ inj a b e with fin-view a | fin-view b
  ... | zero   | zero   = refl
  ... | zero   | suc b' = absurd (fzero≠fsuc e)
  ... | suc a' | zero   = absurd (fsuc≠fzero e)
  ... | suc a' | suc b' = ap fsuc (inj a' b' (fsuc-inj e))

  cons-rename
    : ∀ {n m} (ρ : Fin n → Fin m) (t : ℝ) (y : Fin m → ℝ)
    → (λ j → cons t y (lift-ρ ρ j)) ≡ cons t (λ j → y (ρ j))
  cons-rename ρ t y = funext λ j → go j where
    go : ∀ j → cons t y (lift-ρ ρ j) ≡ cons t (λ l → y (ρ l)) j
    go j with fin-view j
    ... | zero   = refl
    ... | suc j' = refl

  set-miss
    : ∀ {n m} (ρ : Fin n → Fin m) (d : Fin m)
    → (∀ j → ¬ (ρ j ≡ d))
    → (y : Fin m → ℝ) (t : ℝ)
    → (λ j → set y d t (ρ j)) ≡ (λ j → y (ρ j))
  set-miss ρ d miss y t = funext λ j →
    set-other y d (ρ j) t (λ e → miss j (sym e))

  set-hit
    : ∀ {n m} (ρ : Fin n → Fin m)
    → (∀ a b → ρ a ≡ ρ b → a ≡ b)
    → (d : Fin m) (j₀ : Fin n) → ρ j₀ ≡ d
    → (y : Fin m → ℝ) (t : ℝ)
    → (λ j → set y d t (ρ j)) ≡ set (λ j → y (ρ j)) j₀ t
  set-hit ρ inj d j₀ hit y t = funext λ j → go j where
    go : ∀ j → set y d t (ρ j) ≡ set (λ l → y (ρ l)) j₀ t j
    go j with Discrete-Fin .decide j₀ j
    ... | yes p =
        ap (set y d t) (ap ρ (sym p) ∙ hit)
      ∙ set-same y d t
    ... | no ¬p = set-other y d (ρ j) t
        (λ e → ¬p (inj j₀ j (hit ∙ e)))
```
-->

```agda
tower-rename
  : ∀ k {n m} (ρ : Fin n → Fin m)
  → (∀ a b → ρ a ≡ ρ b → a ≡ b)
  → (f : Fun n) → TowerTo k n f
  → TowerTo k m (λ y → f (λ j → y (ρ j)))
tower-rename zero ρ inj f _ = lift tt
tower-rename (suc k) {n} {m} ρ inj f T d
  with holds? (Σ[ j ∈ Fin n ] (ρ j ≡ d))
... | yes (j₀ , hit) =
  let (g , q , T') = T j₀ in
    (λ y → g (λ l → y (lift-ρ ρ l)))
  , (λ y t →
        ap (λ w → f (λ j → y (ρ j)) −ᴿ f w) (set-hit ρ inj d j₀ hit y t)
      ∙ q (λ j → y (ρ j)) t
      ∙ ap₂ (λ a w → (a −ᴿ t) *ᴿ g w)
          (ap y hit)
          (sym (cons-rename ρ t y)))
  , tower-rename k (lift-ρ ρ) (lift-ρ-inj ρ inj) g T'
... | no miss =
    (λ _ → 0ᴿ)
  , (λ y t →
        ap (λ w → f (λ j → y (ρ j)) −ᴿ f w)
          (set-miss ρ d (λ j e → miss (j , e)) y t)
      ∙ +ᴿ-invr (f (λ j → y (ρ j)))
      ∙ sym (*ᴿ-absorbr (y d −ᴿ t)))
  , tower-const k (suc m) 0ᴿ

smooth-rename
  : ∀ {n m} (ρ : Fin n → Fin m)
  → (∀ a b → ρ a ≡ ρ b → a ≡ b)
  → {f : Fun n} → Smooth n f
  → Smooth m (λ y → f (λ j → y (ρ j)))
smooth-rename ρ inj S k = tower-rename k ρ inj _ (S k)
```

## The Leibniz rule

The quotient of a product telescopes: evaluate the first factor at
the unmoved point and the second at the moved one, and each summand
picks up one factor's quotient.

<!--
```agda
private
  tele : ∀ a b c → a −ᴿ c ≡ (a −ᴿ b) +ᴿ (b −ᴿ c)
  tele a b c = sym
    ( sym (+ᴿ-assoc a (-ᴿ b) (b −ᴿ c))
    ∙ ap (a +ᴿ_)
        ( +ᴿ-assoc (-ᴿ b) b (-ᴿ c)
        ∙ ap (_+ᴿ (-ᴿ c)) (+ᴿ-invl b)
        ∙ +ᴿ-idl (-ᴿ c)))

  factor-l : ∀ a b c → (a *ᴿ b) −ᴿ (a *ᴿ c) ≡ a *ᴿ (b −ᴿ c)
  factor-l a b c =
      ap ((a *ᴿ b) +ᴿ_) (sym (*ᴿ-negr a c))
    ∙ sym (*ᴿ-distribˡ a b (-ᴿ c))

  factor-r : ∀ a b c → (a *ᴿ c) −ᴿ (b *ᴿ c) ≡ (a −ᴿ b) *ᴿ c
  factor-r a b c =
      ap₂ _−ᴿ_ (*ᴿ-comm a c) (*ᴿ-comm b c)
    ∙ factor-l c a b
    ∙ *ᴿ-comm c (a −ᴿ b)

  pull : ∀ s a b → a *ᴿ (s *ᴿ b) ≡ s *ᴿ (a *ᴿ b)
  pull s a b =
      sym (*ᴿ-assoc a s b)
    ∙ ap (_*ᴿ b) (*ᴿ-comm a s)
    ∙ *ᴿ-assoc s a b

  σᵢ : ∀ {n} → Fin n → Fin n → Fin (suc n)
  σᵢ i j with Discrete-Fin .decide i j
  ... | yes _ = fzero
  ... | no  _ = fsuc j

  σᵢ-inj
    : ∀ {n} (i : Fin n) (a b : Fin n) → σᵢ i a ≡ σᵢ i b → a ≡ b
  σᵢ-inj i a b e with Discrete-Fin .decide i a | Discrete-Fin .decide i b
  ... | yes p | yes q = sym p ∙ q
  ... | yes p | no  _ = absurd (fzero≠fsuc e)
  ... | no  _ | yes q = absurd (fsuc≠fzero e)
  ... | no  _ | no  _ = fsuc-inj e

  σᵢ-set
    : ∀ {n} (i : Fin n) (x : Fin n → ℝ) (t : ℝ)
    → (λ j → cons t x (σᵢ i j)) ≡ set x i t
  σᵢ-set i x t = funext λ j → go j where
    go : ∀ j → cons t x (σᵢ i j) ≡ set x i t j
    go j with Discrete-Fin .decide i j
    ... | yes _ = refl
    ... | no  _ = refl
```
-->

```agda
tower-trunc
  : ∀ k {n} {f : Fun n} → TowerTo (suc k) n f → TowerTo k n f
tower-trunc zero _ = lift tt
tower-trunc (suc k) T i =
  let (g , q , T') = T i in g , q , tower-trunc k T'

tower-mul
  : ∀ k n (f g : Fun n)
  → TowerTo k n f → TowerTo k n g
  → TowerTo k n (λ x → f x *ᴿ g x)
tower-mul zero n f g _ _ = lift tt
tower-mul (suc k) n f g T S i =
  let (fq , qf , T') = T i
      (gq , qg , S') = S i
  in
    (λ y → (f (λ j → y (fsuc j)) *ᴿ gq y)
       +ᴿ (g (λ j → y (σᵢ i j)) *ᴿ fq y))
  , (λ x t →
        tele (f x *ᴿ g x) (f x *ᴿ g (set x i t))
          (f (set x i t) *ᴿ g (set x i t))
      ∙ ap₂ _+ᴿ_
          ( factor-l (f x) (g x) (g (set x i t))
          ∙ ap (f x *ᴿ_) (qg x t)
          ∙ pull (x i −ᴿ t) (f x) (gq (cons t x)))
          ( factor-r (f x) (f (set x i t)) (g (set x i t))
          ∙ ap (_*ᴿ g (set x i t)) (qf x t)
          ∙ *ᴿ-assoc (x i −ᴿ t) (fq (cons t x)) (g (set x i t))
          ∙ ap ((x i −ᴿ t) *ᴿ_)
              ( *ᴿ-comm (fq (cons t x)) (g (set x i t))
              ∙ ap (λ w → g w *ᴿ fq (cons t x)) (sym (σᵢ-set i x t))))
      ∙ sym (*ᴿ-distribˡ (x i −ᴿ t)
          (f x *ᴿ gq (cons t x))
          (g (λ j → cons t x (σᵢ i j)) *ᴿ fq (cons t x))))
  , tower-add k (suc n)
      (λ y → f (λ j → y (fsuc j)) *ᴿ gq y)
      (λ y → g (λ j → y (σᵢ i j)) *ᴿ fq y)
      (tower-mul k (suc n) _ gq
        (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)) S')
      (tower-mul k (suc n) _ fq
        (tower-rename k (σᵢ i) (σᵢ-inj i) g (tower-trunc k S)) T')

smooth-mul
  : ∀ {n} {f g : Fun n}
  → Smooth n f → Smooth n g → Smooth n (λ x → f x *ᴿ g x)
smooth-mul S T k = tower-mul k _ _ _ (S k) (T k)
```

## The chain rule

The quotient of a composite telescopes over the coordinates of the
middle tuple: switching one coordinate at a time from the unmoved
point to the moved one, each step picks up one component's quotient
against one quotient of the outer function, evaluated on the mixed
frame.

<!--
```agda
private
  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)

  switch : ∀ {m} → (Fin m → ℝ) → (Fin m → ℝ) → Nat → Fin m → ℝ
  switch u v c j with holds? (suc (j .lower) Nat.≤ c)
  ... | yes _ = v j
  ... | no  _ = u j

  switch-hi
    : ∀ {m} (u v : Fin m → ℝ) (c : Nat) (j : Fin m)
    → ¬ (suc (j .lower) Nat.≤ c) → switch u v c j ≡ u j
  switch-hi u v c j hi with holds? (suc (j .lower) Nat.≤ c)
  ... | yes p = absurd (hi p)
  ... | no  _ = refl

  switch-lo
    : ∀ {m} (u v : Fin m → ℝ) (c : Nat) (j : Fin m)
    → suc (j .lower) Nat.≤ c → switch u v c j ≡ v j
  switch-lo u v c j lo with holds? (suc (j .lower) Nat.≤ c)
  ... | yes _ = refl
  ... | no ¬p = absurd (¬p lo)

  switch-step
    : ∀ {m} (u v : Fin m → ℝ) (c : Nat) (cf : Fin m)
    → cf .lower ≡ c
    → set (switch u v c) cf (v cf) ≡ switch u v (suc c)
  switch-step u v c cf ce = funext λ j → go j where
    go : ∀ j → set (switch u v c) cf (v cf) j ≡ switch u v (suc c) j
    go j with Discrete-Fin .decide cf j
    ... | yes p =
        ap v p
      ∙ sym (switch-lo u v (suc c) j
          (Nat.s≤s (subst (λ z → j .lower Nat.≤ z) ce
            (subst (λ z → j .lower Nat.≤ z .lower) (sym p) Nat.≤-refl))))
    ... | no ¬p with holds? (suc (j .lower) Nat.≤ c)
    ...   | yes lo = sym (switch-lo u v (suc c) j (Nat.≤-sucr lo))
    ...   | no hi = sym (switch-hi u v (suc c) j no-suc)
      where
      no-suc : ¬ (suc (j .lower) Nat.≤ suc c)
      no-suc le with Nat.≤-split (j .lower) c
      ... | inl lt = hi lt
      ... | inr (inl gt) =
        Nat.¬sucx≤x _ (Nat.≤-trans gt (Nat.≤-peel le))
      ... | inr (inr e) =
        ¬p (fin-ap {n = λ _ → _} (ce ∙ sym e))
```
-->

The frame bookkeeping is a fuel-indexed sum, exactly parallel on
values and on towers.

```agda
teleT
  : ∀ {m} (gq : Fin m → Fun (suc m)) (u v : Fin m → ℝ)
  → (fuel c : Nat) → c Nat.+ fuel ≡ m → ℝ
teleT gq u v zero c eq = 0ᴿ
teleT {m} gq u v (suc fuel) c eq =
  ((u cf −ᴿ v cf) *ᴿ gq cf (cons (v cf) (switch u v c)))
    +ᴿ teleT gq u v fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq)
  where
  cf : Fin m
  cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
        (Nat.s≤s (le-plus c fuel)) ⦄

telescope
  : ∀ {m} (g : Fun m) (gq : Fin m → Fun (suc m))
  → (∀ j → Quot m g j (gq j))
  → (u v : Fin m → ℝ)
  → (fuel c : Nat) (eq : c Nat.+ fuel ≡ m)
  → g (switch u v c) −ᴿ g v ≡ teleT gq u v fuel c eq
telescope {m} g gq gis u v zero c eq =
    ap (λ w → g w −ᴿ g v)
      (funext λ j → switch-lo u v c j
        (subst (suc (j .lower) Nat.≤_)
          (sym (sym (Nat.+-zeror c) ∙ eq))
          (j .Fin.bounded)))
  ∙ +ᴿ-invr (g v)
telescope {m} g gq gis u v (suc fuel) c eq =
    tele (g (switch u v c)) (g (switch u v (suc c))) (g v)
  ∙ ap₂ _+ᴿ_
      ( ap (λ w → g (switch u v c) −ᴿ g w)
          (sym (switch-step u v c cf refl))
      ∙ gis cf (switch u v c) (v cf)
      ∙ ap (λ a → (a −ᴿ v cf) *ᴿ gq cf (cons (v cf) (switch u v c)))
          (switch-hi u v c cf (λ le → Nat.¬sucx≤x c le)))
      (telescope g gq gis u v fuel (suc c)
        (sym (Nat.+-sucr c fuel) ∙ eq))
  where
  cf : Fin m
  cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
        (Nat.s≤s (le-plus c fuel)) ⦄
```

The composite's quotient is the telescope with each coordinate
difference factored through that component's quotient; the frames
are renamings of the components, so the whole tower recurses.

<!--
```agda
private
  Frame
    : ∀ {n m} (F : Fin m → Fun n) (i : Fin n) (c : Nat) (cf : Fin m)
    → Fin (suc m) → Fun (suc n)
  Frame F i c cf l with fin-view l
  ... | zero = λ y → F cf (λ j → y (σᵢ i j))
  ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
  ...   | yes _ = λ y → F l' (λ j → y (σᵢ i j))
  ...   | no  _ = λ y → F l' (λ j → y (fsuc j))
```
-->

```agda
tower-comp
  : ∀ k {n m} (F : Fin m → Fun n) (g : Fun m)
  → (∀ j → TowerTo k n (F j))
  → TowerTo k m g
  → TowerTo k n (λ x → g (λ j → F j x))
tower-comp zero F g _ _ = lift tt
tower-comp (suc k) {n} {m} F g TF Tg i =
  Qs m 0 refl , (λ x t → qproof x t) , Qs-tower m 0 refl
  where
  gq : (j : Fin m) → Fun (suc m)
  gq j = Tg j .fst

  gis : ∀ j → Quot m g j (gq j)
  gis j = Tg j .snd .fst

  gdeep : ∀ j → TowerTo k (suc m) (gq j)
  gdeep j = Tg j .snd .snd

  Fq : (j : Fin m) → Fun (suc n)
  Fq j = TF j i .fst

  Fis : ∀ j → Quot n (F j) i (Fq j)
  Fis j = TF j i .snd .fst

  Fdeep : ∀ j → TowerTo k (suc n) (Fq j)
  Fdeep j = TF j i .snd .snd

  Qs : (fuel c : Nat) → c Nat.+ fuel ≡ m → Fun (suc n)
  Qs zero c eq = λ _ → 0ᴿ
  Qs (suc fuel) c eq = λ y →
      (Fq cf y *ᴿ gq cf (λ l → Frame F i c cf l y))
    +ᴿ Qs fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq) y
    where
    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

  Frame-tower
    : (c : Nat) (cf : Fin m) (l : Fin (suc m))
    → TowerTo k (suc n) (Frame F i c cf l)
  Frame-tower c cf l with fin-view l
  ... | zero = tower-rename k (σᵢ i) (σᵢ-inj i) (F cf)
    (tower-trunc k (TF cf))
  ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
  ...   | yes _ = tower-rename k (σᵢ i) (σᵢ-inj i) (F l')
    (tower-trunc k (TF l'))
  ...   | no  _ = tower-rename k fsuc (λ a b → fsuc-inj) (F l')
    (tower-trunc k (TF l'))

  Qs-tower
    : (fuel c : Nat) (eq : c Nat.+ fuel ≡ m)
    → TowerTo k (suc n) (Qs fuel c eq)
  Qs-tower zero c eq = tower-const k (suc n) 0ᴿ
  Qs-tower (suc fuel) c eq = tower-add k (suc n) _ _
    (tower-mul k (suc n) _ _
      (Fdeep cf)
      (tower-comp k (Frame F i c cf) (gq cf)
        (Frame-tower c cf) (gdeep cf)))
    (Qs-tower fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    where
    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

  qproof
    : (x : Fin n → ℝ) (t : ℝ)
    → g (λ j → F j x) −ᴿ g (λ j → F j (set x i t))
    ≡ (x i −ᴿ t) *ᴿ Qs m 0 refl (cons t x)
  qproof x t =
      ap (λ w → g w −ᴿ g v)
        (funext λ j → sym (switch-hi u v 0 j (λ le → Nat.¬suc≤0 le)))
    ∙ telescope g gq gis u v m 0 refl
    ∙ factor m 0 refl
    where
    u v : Fin m → ℝ
    u = λ j → F j x
    v = λ j → F j (set x i t)

    frame-path
      : (c : Nat) (cf : Fin m)
      → cons (v cf) (switch u v c)
      ≡ (λ l → Frame F i c cf l (cons t x))
    frame-path c cf = funext λ l → go l where
      go : ∀ l → cons (v cf) (switch u v c) l
             ≡ Frame F i c cf l (cons t x)
      go l with fin-view l
      ... | zero = ap (F cf) (sym (σᵢ-set i x t))
      ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
      ...   | yes _ = ap (F l') (sym (σᵢ-set i x t))
      ...   | no  _ = refl

    factor
      : (fuel c : Nat) (eq : c Nat.+ fuel ≡ m)
      → teleT gq u v fuel c eq
      ≡ (x i −ᴿ t) *ᴿ Qs fuel c eq (cons t x)
    factor zero c eq = sym (*ᴿ-absorbr (x i −ᴿ t))
    factor (suc fuel) c eq =
        ap₂ _+ᴿ_
          ( ap₂ (λ a w → a *ᴿ gq cf w)
              (Fis cf x t)
              (frame-path c cf)
          ∙ *ᴿ-assoc (x i −ᴿ t) (Fq cf (cons t x))
              (gq cf (λ l → Frame F i c cf l (cons t x))))
          (factor fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
      ∙ sym (*ᴿ-distribˡ (x i −ᴿ t)
          (Fq cf (cons t x) *ᴿ gq cf (λ l → Frame F i c cf l (cons t x)))
          (Qs fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq) (cons t x)))
      where
      cf : Fin m
      cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
            (Nat.s≤s (le-plus c fuel)) ⦄

smooth-comp
  : ∀ {n m} {F : Fin m → Fun n} {g : Fun m}
  → (∀ j → Smooth n (F j)) → Smooth m g
  → Smooth n (λ x → g (λ j → F j x))
smooth-comp SF Sg k = tower-comp k _ _ (λ j → SF j k) (Sg k)
```

## The ring of smooth functions

Smooth functions form a commutative ring — the closure combinators
are exactly the ring operations — and this is the object that the
paper's algebraic constructions consume: the infinitesimally
thickened probes have function algebras $C^\infty(\bR^n) \otimes W$,
built from this ring by the generic dual-number construction.

<!--
```agda
open import Algebra.Ring.Commutative
open import Algebra.Ring
```
-->

```agda
C∞ : Nat → Type
C∞ n = Σ[ f ∈ Fun n ] ∥ Smooth n f ∥

private
  C∞-is-set : ∀ {n} → is-set (C∞ n)
  C∞-is-set = Σ-is-hlevel 2
    (Π-is-hlevel 2 λ _ → ℝ-is-set)
    (λ _ → is-prop→is-set squash)

C∞Ring : Nat → CRing lzero
C∞Ring n = record
  { fst = el (C∞ n) C∞-is-set
  ; snd = record
    { has-ring-on = ring .snd
    ; *-commutes = λ {x y} → Σ-prop-path (λ _ → squash)
        (funext λ v → *ᴿ-comm (x .fst v) (y .fst v))
    }
  }
  where
  ring : Ring lzero
  ring = to-ring {R = C∞ n} λ where
    .make-ring.ring-is-set → C∞-is-set
    .make-ring.0R → (λ _ → 0ᴿ) , inc (smooth-const 0ᴿ)
    .make-ring._+_ (f , sf) (g , sg) →
      (λ v → f v +ᴿ g v) , ∥-∥-map₂ smooth-add sf sg
    .make-ring.-_ (f , sf) →
      (λ v → -ᴿ f v) , ∥-∥-map smooth-neg sf
    .make-ring.+-idl f → Σ-prop-path (λ _ → squash)
      (funext λ v → +ᴿ-comm 0ᴿ (f .fst v) ∙ +ᴿ-idr (f .fst v))
    .make-ring.+-invr f → Σ-prop-path (λ _ → squash)
      (funext λ v → +ᴿ-invr (f .fst v))
    .make-ring.+-assoc f g h → Σ-prop-path (λ _ → squash)
      (funext λ v → +ᴿ-assoc (f .fst v) (g .fst v) (h .fst v))
    .make-ring.+-comm f g → Σ-prop-path (λ _ → squash)
      (funext λ v → +ᴿ-comm (f .fst v) (g .fst v))
    .make-ring.1R → (λ _ → 1ᴿ) , inc (smooth-const 1ᴿ)
    .make-ring._*_ (f , sf) (g , sg) →
      (λ v → f v *ᴿ g v) , ∥-∥-map₂ smooth-mul sf sg
    .make-ring.*-idl f → Σ-prop-path (λ _ → squash)
      (funext λ v → *ᴿ-idl (f .fst v))
    .make-ring.*-idr f → Σ-prop-path (λ _ → squash)
      (funext λ v → *ᴿ-idr (f .fst v))
    .make-ring.*-assoc f g h → Σ-prop-path (λ _ → squash)
      (funext λ v → sym (*ᴿ-assoc (f .fst v) (g .fst v) (h .fst v)))
    .make-ring.*-distribl f g h → Σ-prop-path (λ _ → squash)
      (funext λ v → *ᴿ-distribˡ (f .fst v) (g .fst v) (h .fst v))
    .make-ring.*-distribr f g h → Σ-prop-path (λ _ → squash)
      (funext λ v → *ᴿ-distribʳ (f .fst v) (g .fst v) (h .fst v))
```
