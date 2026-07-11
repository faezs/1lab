<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Data.Real.Smooth
open import Data.Real.Base

open import Data.Fin using (Fin ; Fin-absurd ; fzero ; fsuc)

import Cat.Instances.Presheaf.Cohesive

open Precategory
open Terminal
```
-->

```agda
module Cat.Instances.CartSp where
```

# The site of Cartesian spaces {defines="cartesian-site smooth-set"}

The paper's site: objects are the Cartesian spaces $\bR^n$ — so the
object part is a natural number, recording the dimension — and
morphisms are the [[smooth maps|smooth-function]] between them,
carried by honest functions of [[Dedekind reals|dedekind-reals]].
Smoothness is a property (the truncation of the Hadamard tower
structure), so the category laws are exactly those of function
composition.

```agda
C∞ : Nat → Nat → Type
C∞ n m =
  Σ[ f ∈ ((Fin n → ℝ) → (Fin m → ℝ)) ]
    ∥ ((j : Fin m) → Smooth n (λ x → f x j)) ∥

CartSp : Precategory lzero lzero
CartSp .Ob = Nat
CartSp .Hom = C∞
CartSp .Hom-set n m = Σ-is-hlevel 2
  (Π-is-hlevel 2 λ _ → Π-is-hlevel 2 λ _ → ℝ-is-set)
  (λ _ → is-prop→is-set squash)
CartSp .id = (λ x → x) , inc (λ j → smooth-proj j)
CartSp ._∘_ (f , sf) (g , sg) =
    (λ x → f (g x))
  , ∥-∥-map₂ (λ Sf Sg j → smooth-comp Sg (Sf j)) sf sg
CartSp .idr f = Σ-prop-path (λ _ → squash) refl
CartSp .idl f = Σ-prop-path (λ _ → squash) refl
CartSp .assoc f g h = Σ-prop-path (λ _ → squash) refl
```

The point $\bR^0$ is terminal, and with it the topos of presheaves
— the paper's **smooth sets**, now with genuinely smooth plots — is
[[cohesive|cohesive-topos]].

```agda
pt-terminal : Terminal CartSp
pt-terminal .top = 0
pt-terminal .has⊤ n .centre =
    (λ _ j → absurd (Fin-absurd j))
  , inc (λ j → absurd (Fin-absurd j))
pt-terminal .has⊤ n .paths h = Σ-prop-path (λ _ → squash)
  (funext λ x → funext λ j → absurd (Fin-absurd j))

SmoothSet : Precategory (lsuc lzero) lzero
SmoothSet = PSh lzero CartSp

module SmoothSet-cohesion =
  Cat.Instances.Presheaf.Cohesive CartSp pt-terminal
```
