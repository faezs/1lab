<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Instances.Functor
open import Cat.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth hiding (C∞)
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative
open import Data.Real.Smooth.Calculus

open import Cat.Instances.CartSp

open import Data.Fin.Properties using (finite-choice)
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec

import Data.Nat as Nat

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.CartSp.Forms where
```

# Differential forms on the Cartesian site {defines="cartesian-one-forms honest-de-rham honest-gauge-groupoid"}

The polynomial-site story of differential forms — the de Rham
classifier, the differential as a map of smooth sets, and the gauge
groupoid — was told over formal duals of finitely presented
algebras, where "smooth function" meant *polynomial*. This module
re-instantiates that layer **honestly**, over the [[Cartesian
site|cartesian-site]] whose morphisms are genuinely
[[bounded-smooth|bounded-smooth-function]] functions of [[Dedekind
reals|dedekind-reals]]: the coefficients of a $1$-form are
bounded-smooth scalars, the pullback of a form is weighted by the
honest Jacobian extracted from the Hadamard towers, and the de Rham
differential is the [[extracted derivative|real-derivative]]
itself. Every equation below — functoriality of the pullback,
naturality of $\mathrm{d}$, the gauge groupoid laws — is a theorem
of the [[derivative calculus|derivative-calculus]]: the Kronecker
collapse of the identity's Jacobian, the chain rule for composites,
and the additivity of the derivative.

## The presheaf of smooth scalars

A **smooth scalar** on $\bR^n$ is a function of tuples of reals
that merely carries a bounded Hadamard tower. Since the tower is
property-like, the scalars form a set, and precomposition with a
site morphism is smooth by the composite combinator — so the
scalars assemble into a [[smooth set|smooth-set]], the honest
structure sheaf $\mathcal{O}$.

```agda
𝒞 : Nat → Type
𝒞 n = Σ[ f ∈ Fun n ] ∥ Smooth⁺ n f ∥

𝒞-is-set : ∀ n → is-set (𝒞 n)
𝒞-is-set n = Σ-is-hlevel 2
  (Π-is-hlevel 2 λ _ → ℝ-is-set)
  (λ _ → is-prop→is-set squash)

O-psh : ⌞ SmoothSet ⌟
O-psh .F₀ n = el (𝒞 n) (𝒞-is-set n)
O-psh .F₁ (φ , s) (f , sf) =
    (λ x → f (φ x))
  , ∥-∥-map₂ (λ Sφ Sf → smooth⁺-comp Sφ Sf) s sf
O-psh .F-id  = funext λ _ → Σ-prop-path (λ _ → squash) refl
O-psh .F-∘ _ _ = funext λ _ → Σ-prop-path (λ _ → squash) refl
```

## Finite sums are bounded-smooth

The chain rule of the derivative calculus produces the
fuel-indexed sum `Σ-fuel`{.Agda}; to build the Jacobian pullback we
must know that such sums of bounded-smooth summands are again
bounded-smooth. The recursion mirrors `Σ-fuel`{.Agda} clause for
clause — in particular the coordinate `fin c`{.Agda} is
constructed by the *same* term, so each recursive layer matches
definitionally.

```agda
smooth⁺-Σ-fuel
  : ∀ {n m} (h : Fin m → Fun n) (H : ∀ j → Smooth⁺ n (h j))
  → ∀ fuel c (eq : c Nat.+ fuel ≡ m)
  → Smooth⁺ n (λ x → Σ-fuel (λ j → h j x) fuel c eq)
smooth⁺-Σ-fuel h H zero c eq = smooth⁺-const 0ᴿ
smooth⁺-Σ-fuel {n} {m} h H (suc fuel) c eq =
  smooth⁺-add (H cf)
    (smooth⁺-Σ-fuel h H fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
  where
  cf : Fin m
  cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
        (Nat.s≤s (le-plus c fuel)) ⦄

smooth⁺-Σᴰ
  : ∀ {n m} (h : Fin m → Fun n) (H : ∀ j → Smooth⁺ n (h j))
  → Smooth⁺ n (λ x → Σᴰ (λ j → h j x))
smooth⁺-Σᴰ {n} {m} h H = smooth⁺-Σ-fuel h H m 0 refl
```

## Sum algebra

The functor laws for the pullback are, once the chain rule has
fired, pure algebra of finite sums: a Kronecker-delta collapse (for
the identity), and distributivity plus a finite Fubini interchange
(for composites). We prove them by fuel induction against a handful
of commutative-ring identities.

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  mul-zeror : ∀ a → a R.* R.0r ≡ R.0r
  mul-zeror a = cring! S

  interchange
    : ∀ a b c d
    → (a R.+ b) R.+ (c R.+ d) ≡ (a R.+ c) R.+ (b R.+ d)
  interchange a b c d = cring! S

  rot-right : ∀ a b c → a R.* (c R.* b) ≡ (a R.* b) R.* c
  rot-right a b c = cring! S

private module RI = Identities ℝ-comm
```
-->

The δ-collapse: summing $h_j \cdot e_j$ against a family $e$ that
is $1$ at the index $i$ and $0$ elsewhere yields $h_i$. The
induction tracks the enumeration position $c$: while the sum has
not yet passed $i$ it will produce $h_i$; once past, it vanishes.

```agda
private
  Σ-fuel-δ
    : ∀ {m} (h e : Fin m → ℝ) (i : Fin m)
    → (∀ j → i ≡ j → e j ≡ 1ᴿ)
    → (∀ j → ¬ i ≡ j → e j ≡ 0ᴿ)
    → ∀ fuel c (eq : c Nat.+ fuel ≡ m)
    → ((c Nat.≤ i .lower) → Σ-fuel (λ j → h j *ᴿ e j) fuel c eq ≡ h i)
    × ((suc (i .lower) Nat.≤ c) → Σ-fuel (λ j → h j *ᴿ e j) fuel c eq ≡ 0ᴿ)
  Σ-fuel-δ {m} h e i E1 E0 zero c eq =
      (λ c≤i → absurd (Nat.<-irrefl refl
        (Nat.≤-trans (Fin.bounded i) (subst (Nat._≤ i .lower) c≡m c≤i))))
    , (λ _ → refl)
    where
    c≡m : c ≡ m
    c≡m = sym (Nat.+-zeror c) ∙ eq
  Σ-fuel-δ {m} h e i E1 E0 (suc fuel) c eq = in-range , past
    where
    eq' : suc c Nat.+ fuel ≡ m
    eq' = sym (Nat.+-sucr c fuel) ∙ eq

    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

    rec = Σ-fuel-δ h e i E1 E0 fuel (suc c) eq'

    head-zero : ¬ i ≡ cf → h cf *ᴿ e cf ≡ 0ᴿ
    head-zero i≢cf = ap (h cf *ᴿ_) (E0 cf i≢cf) ∙ RI.mul-zeror (h cf)

    in-range
      : c Nat.≤ i .lower
      → Σ-fuel (λ j → h j *ᴿ e j) (suc fuel) c eq ≡ h i
    in-range c≤i with holds? (suc c Nat.≤ i .lower)
    ... | yes c<i =
        ap₂ _+ᴿ_
          (head-zero (λ q → Nat.<-irrefl (sym (ap lower q)) c<i))
          (rec .fst c<i)
      ∙ +ᴿ-comm 0ᴿ (h i) ∙ +ᴿ-idr (h i)
    ... | no ¬c<i =
        ap₂ _+ᴿ_
          (ap₂ _*ᴿ_ (ap h (sym i≡cf)) (E1 cf i≡cf) ∙ *ᴿ-idr (h i))
          (rec .snd (Nat.s≤s i≤c))
      ∙ +ᴿ-idr (h i)
      where
      i≤c : i .lower Nat.≤ c
      i≤c = Nat.≤-from-not-< c (i .lower) ¬c<i

      i≡cf : i ≡ cf
      i≡cf = fin-ap (Nat.≤-antisym i≤c c≤i)

    past
      : suc (i .lower) Nat.≤ c
      → Σ-fuel (λ j → h j *ᴿ e j) (suc fuel) c eq ≡ 0ᴿ
    past i<c =
        ap₂ _+ᴿ_
          (head-zero (λ q → Nat.<-irrefl (ap lower q) i<c))
          (rec .snd (Nat.≤-sucr i<c))
      ∙ +ᴿ-idr 0ᴿ

Σᴰ-δ
  : ∀ {m} (h e : Fin m → ℝ) (i : Fin m)
  → (∀ j → i ≡ j → e j ≡ 1ᴿ)
  → (∀ j → ¬ i ≡ j → e j ≡ 0ᴿ)
  → Σᴰ (λ j → h j *ᴿ e j) ≡ h i
Σᴰ-δ {m} h e i E1 E0 = Σ-fuel-δ h e i E1 E0 m 0 refl .fst Nat.0≤x
```

Linearity of the fuel-indexed sum: a sum of zeros vanishes, sums
add pointwise, and a fixed factor distributes in and out.

```agda
private
  Σ-fuel-0
    : ∀ {m} fuel c (eq : c Nat.+ fuel ≡ m)
    → Σ-fuel {m} (λ _ → 0ᴿ) fuel c eq ≡ 0ᴿ
  Σ-fuel-0 zero c eq = refl
  Σ-fuel-0 (suc fuel) c eq =
      ap (0ᴿ +ᴿ_) (Σ-fuel-0 fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    ∙ +ᴿ-idr 0ᴿ

  Σ-fuel-+
    : ∀ {m} (f g : Fin m → ℝ) fuel c (eq : c Nat.+ fuel ≡ m)
    → Σ-fuel f fuel c eq +ᴿ Σ-fuel g fuel c eq
    ≡ Σ-fuel (λ j → f j +ᴿ g j) fuel c eq
  Σ-fuel-+ f g zero c eq = +ᴿ-idr 0ᴿ
  Σ-fuel-+ {m} f g (suc fuel) c eq =
      RI.interchange (f cf) (Σ-fuel f fuel (suc c) eq')
        (g cf) (Σ-fuel g fuel (suc c) eq')
    ∙ ap ((f cf +ᴿ g cf) +ᴿ_) (Σ-fuel-+ f g fuel (suc c) eq')
    where
    eq' : suc c Nat.+ fuel ≡ m
    eq' = sym (Nat.+-sucr c fuel) ∙ eq

    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

  Σ-fuel-·l
    : ∀ {m} (a : ℝ) (h : Fin m → ℝ) fuel c (eq : c Nat.+ fuel ≡ m)
    → a *ᴿ Σ-fuel h fuel c eq ≡ Σ-fuel (λ j → a *ᴿ h j) fuel c eq
  Σ-fuel-·l a h zero c eq = RI.mul-zeror a
  Σ-fuel-·l {m} a h (suc fuel) c eq =
      *ᴿ-distribˡ a (h cf) (Σ-fuel h fuel (suc c) eq')
    ∙ ap ((a *ᴿ h cf) +ᴿ_) (Σ-fuel-·l a h fuel (suc c) eq')
    where
    eq' : suc c Nat.+ fuel ≡ m
    eq' = sym (Nat.+-sucr c fuel) ∙ eq

    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

Σᴰ-·l : ∀ {m} (a : ℝ) (h : Fin m → ℝ) → a *ᴿ Σᴰ h ≡ Σᴰ (λ j → a *ᴿ h j)
Σᴰ-·l {m} a h = Σ-fuel-·l a h m 0 refl

Σᴰ-·r : ∀ {m} (a : ℝ) (h : Fin m → ℝ) → Σᴰ (λ j → h j *ᴿ a) ≡ Σᴰ h *ᴿ a
Σᴰ-·r {m} a h =
    ap Σᴰ (funext λ j → *ᴿ-comm (h j) a)
  ∙ sym (Σᴰ-·l a h)
  ∙ *ᴿ-comm a (Σᴰ h)
```

The finite Fubini interchange: a double fuel-indexed sum can be
summed in either order. The outer induction peels one summand and
folds it back in with pointwise additivity.

```agda
private
  Σ-fuel-swap
    : ∀ {m₁ m₂} (A : Fin m₁ → Fin m₂ → ℝ)
    → ∀ fuel₁ c₁ (eq₁ : c₁ Nat.+ fuel₁ ≡ m₁)
    → ∀ fuel₂ c₂ (eq₂ : c₂ Nat.+ fuel₂ ≡ m₂)
    → Σ-fuel (λ j → Σ-fuel (A j) fuel₂ c₂ eq₂) fuel₁ c₁ eq₁
    ≡ Σ-fuel (λ p → Σ-fuel (λ j → A j p) fuel₁ c₁ eq₁) fuel₂ c₂ eq₂
  Σ-fuel-swap A zero c₁ eq₁ fuel₂ c₂ eq₂ = sym (Σ-fuel-0 fuel₂ c₂ eq₂)
  Σ-fuel-swap {m₁} {m₂} A (suc fuel₁) c₁ eq₁ fuel₂ c₂ eq₂ =
      ap (Σ-fuel (A cf) fuel₂ c₂ eq₂ +ᴿ_)
        (Σ-fuel-swap A fuel₁ (suc c₁) eq₁' fuel₂ c₂ eq₂)
    ∙ Σ-fuel-+ (A cf) (λ p → Σ-fuel (λ j → A j p) fuel₁ (suc c₁) eq₁')
        fuel₂ c₂ eq₂
    where
    eq₁' : suc c₁ Nat.+ fuel₁ ≡ m₁
    eq₁' = sym (Nat.+-sucr c₁ fuel₁) ∙ eq₁

    cf : Fin m₁
    cf = fin c₁ ⦃ subst (suc c₁ Nat.≤_) (sym (Nat.+-sucr c₁ fuel₁) ∙ eq₁)
          (Nat.s≤s (le-plus c₁ fuel₁)) ⦄

Σᴰ-swap
  : ∀ {m₁ m₂} (A : Fin m₁ → Fin m₂ → ℝ)
  → Σᴰ (λ j → Σᴰ (A j)) ≡ Σᴰ (λ p → Σᴰ (λ j → A j p))
Σᴰ-swap {m₁} {m₂} A = Σ-fuel-swap A m₁ 0 refl m₂ 0 refl
```

## One-forms and the Jacobian pullback

A **differential $1$-form** on $\bR^n$ is a tuple of smooth
scalars — the coefficients $\omega_j$ of $\sum_j \omega_j\,
\mathrm{d}x^j$. The pullback along a site morphism $\varphi :
\bR^m \to \bR^n$ is the classical formula
$$(\varphi^*\omega)_i = \sum_j (\omega_j \circ \varphi)\cdot
\partial_i \varphi^j,$$
where $\partial_i \varphi^j$ is the honest [[extracted
derivative|real-derivative]] of the $j$-th component — well
defined directly on the propositionally truncated smoothness
witness carried by the site.

```agda
Ω¹-carrier : Nat → Type
Ω¹-carrier n = Fin n → 𝒞 n

Ω¹-is-set : ∀ n → is-set (Ω¹-carrier n)
Ω¹-is-set n = Π-is-hlevel 2 λ _ → 𝒞-is-set n

∂C∞ : ∀ {m n} (φ : C∞ m n) (j : Fin n) (i : Fin m) → Fun m
∂C∞ (φ₀ , s) j i = ∂ᴿ (λ v → φ₀ v j) i (∥-∥-map (λ S → S j) s)

pullΩ : ∀ {m n} (φ : C∞ m n) → Ω¹-carrier n → Ω¹-carrier m
pullΩ {m} {n} (φ₀ , s) ω i = coeff , coeff-smooth
  where
  coeff : Fun m
  coeff x = Σᴰ (λ j → ω j .fst (φ₀ x) *ᴿ ∂C∞ (φ₀ , s) j i x)

  summand : Fin n → Fun m
  summand j x = ω j .fst (φ₀ x) *ᴿ ∂C∞ (φ₀ , s) j i x

  summand-smooth : ∀ j → ∥ Smooth⁺ m (summand j) ∥
  summand-smooth j =
    ∥-∥-rec squash (λ Sφ →
    ∥-∥-rec squash (λ Sω →
    ∥-∥-map (λ Sd →
      smooth⁺-mul {f = λ x → ω j .fst (φ₀ x)} {g = ∂C∞ (φ₀ , s) j i}
        (smooth⁺-comp {F = λ j' x → φ₀ x j'} {g = ω j .fst} Sφ Sω) Sd)
      (∂ᴿ-smooth⁺ (λ v → φ₀ v j) i (∥-∥-map (λ S → S j) s)))
      (ω j .snd))
      s

  coeff-smooth : ∥ Smooth⁺ m coeff ∥
  coeff-smooth =
    ∥-∥-map (smooth⁺-Σᴰ summand) (finite-choice n summand-smooth)
```

The identity law is the δ-collapse: the Jacobian of the identity
evaluates, coordinate by coordinate, to the Kronecker delta
(`∂-proj-same`{.Agda}, `∂-proj-diff`{.Agda}), and the sum against
a delta returns the $i$-th coefficient.

```agda
private
  pull-id
    : ∀ {n} (ω : Ω¹-carrier n) (i : Fin n) (x : Fin n → ℝ)
    → pullΩ (CartSp .id) ω i .fst x ≡ ω i .fst x
  pull-id {n} ω i x = Σᴰ-δ
    (λ j → ω j .fst x)
    (λ j → ∂-of (λ v → v j) i (smooth⁺-proj j) x)
    i
    (λ j p → ∂-proj-same j i x p)
    (λ j np → ∂-proj-diff j i x np)
```

The composition law is the chain rule followed by sum algebra.
Since the derivative descends through the truncation, the
composite's smoothness witness — built by the site's composition
— can be exchanged for the chain rule's canonical witness along a
`squash`{.Agda} path; then `∂ᴿ-chain`{.Agda} expands the Jacobian
of the composite into a sum, the fixed coefficient distributes in,
Fubini reorders the double sum, and the inner factor comes back
out.

```agda
private
  pull-comp
    : ∀ {l m n} (φ : C∞ m n) (ψ : C∞ l m) (ω : Ω¹-carrier n)
    → (i : Fin l) (x : Fin l → ℝ)
    → pullΩ (CartSp ._∘_ φ ψ) ω i .fst x
    ≡ pullΩ ψ (pullΩ φ ω) i .fst x
  pull-comp {l} {m} {n} (φ₀ , sφ) (ψ₀ , sψ) ω i x =
      ap Σᴰ (funext λ j →
          ap (A j *ᴿ_) (step1 j)
        ∙ Σᴰ-·l (A j) (λ p → C p *ᴿ B j p))
    ∙ Σᴰ-swap (λ j p → A j *ᴿ (C p *ᴿ B j p))
    ∙ ap Σᴰ (funext λ p →
          ap Σᴰ (funext λ j → RI.rot-right (A j) (B j p) (C p))
        ∙ Σᴰ-·r (C p) (λ j → A j *ᴿ B j p))
    where
    A : Fin n → ℝ
    A j = ω j .fst (φ₀ (ψ₀ x))

    B : Fin n → Fin m → ℝ
    B j p = ∂C∞ (φ₀ , sφ) j p (ψ₀ x)

    C : Fin m → ℝ
    C p = ∂C∞ (ψ₀ , sψ) p i x

    w : (j : Fin n) → ∥ Smooth⁺ l (λ v → φ₀ (ψ₀ v) j) ∥
    w j = ∥-∥-map (λ S → S j)
      (∥-∥-map₂ (λ Sf Sg j' → smooth⁺-comp Sg (Sf j')) sφ sψ)

    chainwit : (j : Fin n) → ∥ Smooth⁺ l (λ v → φ₀ (ψ₀ v) j) ∥
    chainwit j = ∥-∥-map₂ smooth⁺-comp
      (finite-choice m (λ p → ∥-∥-map (λ S → S p) sψ))
      (∥-∥-map (λ S → S j) sφ)

    step1
      : ∀ j → ∂ᴿ (λ v → φ₀ (ψ₀ v) j) i (w j) x
      ≡ Σᴰ (λ p → C p *ᴿ B j p)
    step1 j =
        ap (λ s → ∂ᴿ (λ v → φ₀ (ψ₀ v) j) i s x)
          (squash (w j) (chainwit j))
      ∙ ∂ᴿ-chain (λ p v → ψ₀ v p) (λ u → φ₀ u j)
          (λ p → ∥-∥-map (λ S → S p) sψ) (∥-∥-map (λ S → S j) sφ) i x
```

With both laws in hand, the $1$-forms are a smooth set.

```agda
Ω¹-psh : ⌞ SmoothSet ⌟
Ω¹-psh .F₀ n = el (Ω¹-carrier n) (Ω¹-is-set n)
Ω¹-psh .F₁ φ = pullΩ φ
Ω¹-psh .F-id = funext λ ω → funext λ i →
  Σ-prop-path (λ _ → squash) (funext λ x → pull-id ω i x)
Ω¹-psh .F-∘ f g = funext λ ω → funext λ i →
  Σ-prop-path (λ _ → squash) (funext λ x → pull-comp g f ω i x)
```

## The de Rham differential

The de Rham differential sends a smooth scalar to the $1$-form
whose coefficients are its extracted partial derivatives. That it
is a *morphism of smooth sets* — natural in the probe — is
precisely the chain rule again: differentiating a precomposition
$f \circ \varphi$ produces the pulled-back differential, summand
by summand.

```agda
private
  d-nat
    : ∀ {m n} (φ : C∞ m n) (f : Fun n) (sf : ∥ Smooth⁺ n f ∥)
    → (i : Fin m) (x : Fin m → ℝ)
    → ∂ᴿ (λ v → f (φ .fst v)) i
        (∥-∥-map₂ (λ Sφ Sf → smooth⁺-comp Sφ Sf) (φ .snd) sf) x
    ≡ Σᴰ (λ j → ∂ᴿ f j sf (φ .fst x) *ᴿ ∂C∞ φ j i x)
  d-nat {m} {n} (φ₀ , s) f sf i x =
      ap (λ u → ∂ᴿ (λ v → f (φ₀ v)) i u x)
        (squash (∥-∥-map₂ (λ Sφ Sf → smooth⁺-comp Sφ Sf) s sf) chainwit)
    ∙ ∂ᴿ-chain (λ j v → φ₀ v j) f (λ j → ∥-∥-map (λ S → S j) s) sf i x
    ∙ ap Σᴰ (funext λ j →
        *ᴿ-comm (∂C∞ (φ₀ , s) j i x) (∂ᴿ f j sf (φ₀ x)))
    where
    chainwit : ∥ Smooth⁺ m (λ v → f (φ₀ v)) ∥
    chainwit = ∥-∥-map₂ smooth⁺-comp
      (finite-choice n (λ j → ∥-∥-map (λ S → S j) s)) sf

d⁰ : O-psh => Ω¹-psh
d⁰ .η n (f , sf) i = ∂ᴿ f i sf , ∂ᴿ-smooth⁺ f i sf
d⁰ .is-natural n m φ = funext λ fs → funext λ i →
  Σ-prop-path (λ _ → squash)
    (funext λ x → d-nat φ (fs .fst) (fs .snd) i x)
```

Regarded as a two-term complex of presheaves concentrated in
degrees $1$ and $0$, the morphism $\mathrm{d}^0 : \mathcal{O} \to
\Omega^1$ *is* the honest degree-$2$ Deligne complex — the same
shape as the polynomial-site version, but with bounded-smooth
coefficients and the Hadamard derivative as differential.

```agda
Deligne² : O-psh => Ω¹-psh
Deligne² = d⁰
```

## The gauge groupoid

The two-term complex presents, one probe at a time, the groupoid
of gauge fields: objects are $1$-forms (gauge potentials), and a
morphism $\omega \to \omega'$ is a smooth scalar $g$ — a gauge
transformation — witnessing $\omega' = \omega + \mathrm{d}g$.
Identity is the zero scalar (whose differential vanishes by
`∂-const`{.Agda}), and composition is scalar addition, which the
additivity of the derivative turns into composition of gauge
witnesses.

```agda
0𝒞 : ∀ {n} → 𝒞 n
0𝒞 = (λ _ → 0ᴿ) , inc (smooth⁺-const 0ᴿ)

_+𝒞_ : ∀ {n} → 𝒞 n → 𝒞 n → 𝒞 n
(f , sf) +𝒞 (g , sg) =
  (λ x → f x +ᴿ g x) , ∥-∥-map₂ smooth⁺-add sf sg

_+Ω_ : ∀ {n} → Ω¹-carrier n → Ω¹-carrier n → Ω¹-carrier n
(ω +Ω τ) i = ω i +𝒞 τ i

dscalar : ∀ {n} → 𝒞 n → Ω¹-carrier n
dscalar (g , sg) i = ∂ᴿ g i sg , ∂ᴿ-smooth⁺ g i sg
```

The three lemmas the groupoid laws need: the differential of the
zero scalar is absorbed by addition, the differential is additive,
and addition of forms is associative.

```agda
gauge-id : ∀ {n} (ω : Ω¹-carrier n) → ω ≡ ω +Ω dscalar 0𝒞
gauge-id ω = funext λ i → Σ-prop-path (λ _ → squash)
  (funext λ x → sym (+ᴿ-idr (ω i .fst x)))

d-+𝒞 : ∀ {n} (g h : 𝒞 n) → dscalar (g +𝒞 h) ≡ dscalar g +Ω dscalar h
d-+𝒞 (g , sg) (h , sh) = funext λ i → Σ-prop-path (λ _ → squash)
  (funext λ x → ∂ᴿ-add sg sh i x)

+Ω-assoc
  : ∀ {n} (a b c : Ω¹-carrier n)
  → a +Ω (b +Ω c) ≡ (a +Ω b) +Ω c
+Ω-assoc a b c = funext λ i → Σ-prop-path (λ _ → squash)
  (funext λ x → +ᴿ-assoc (a i .fst x) (b i .fst x) (c i .fst x))
```

The gauge groupoid at stage $n$, as a precategory. Because the
witnessing path lives in a set, morphism equality reduces to
equality of the underlying scalars, and the category laws are the
abelian-group laws of pointwise addition.

```agda
Gauge : Nat → Precategory lzero lzero
Gauge n .Ob = Ω¹-carrier n
Gauge n .Hom ω τ = Σ[ g ∈ 𝒞 n ] (τ ≡ ω +Ω dscalar g)
Gauge n .Hom-set ω τ = Σ-is-hlevel 2 (𝒞-is-set n)
  (λ _ → is-prop→is-set (Ω¹-is-set n _ _))
Gauge n .id = 0𝒞 , gauge-id _
Gauge n ._∘_ {ω} {τ} {υ} (g₂ , p₂) (g₁ , p₁) =
    (g₁ +𝒞 g₂)
  , ( p₂
    ∙ ap (_+Ω dscalar g₂) p₁
    ∙ sym (+Ω-assoc ω (dscalar g₁) (dscalar g₂))
    ∙ ap (ω +Ω_) (sym (d-+𝒞 g₁ g₂)))
Gauge n .idr (g , p) = Σ-prop-path (λ _ → Ω¹-is-set n _ _)
  (Σ-prop-path (λ _ → squash)
    (funext λ x → +ᴿ-comm 0ᴿ (g .fst x) ∙ +ᴿ-idr (g .fst x)))
Gauge n .idl (g , p) = Σ-prop-path (λ _ → Ω¹-is-set n _ _)
  (Σ-prop-path (λ _ → squash)
    (funext λ x → +ᴿ-idr (g .fst x)))
Gauge n .assoc (a , _) (b , _) (c , _) =
  Σ-prop-path (λ _ → Ω¹-is-set n _ _)
    (Σ-prop-path (λ _ → squash)
      (funext λ x → sym (+ᴿ-assoc (c .fst x) (b .fst x) (a .fst x))))
```

What is *not* delivered here: the pullback's action on the gauge
groupoids (a presheaf of precategories, requiring the naturality
of `dscalar`{.Agda} — that is `d⁰`{.Agda}'s naturality — woven
through the morphism spaces), higher forms $\Omega^{\geq 2}$ over
the honest site, and the simplicial Dold–Kan presentation that the
polynomial site enjoys. The two-term layer above is the complete
degree-$\leq 1$ story.
