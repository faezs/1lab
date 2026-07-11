<!--
```agda
open import Cat.Instances.Simplex
open import Cat.Prelude

open import Data.Fin.Finite
open import Data.Fin
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat

open Δ-map
```
-->

```agda
module Cat.Instances.Simplex.Classify where
```

# Classifying the generators of the simplex category

For the normalization theorem we must decide, for a monotone map
$\alpha : [j] \to [k]$, which of four shapes it has: it misses a
positive value, it has an adjacent collision, it is the identity,
or it is the bottom coface $\delta_0$. The characterizations are
arithmetic on the underlying indices: a *strictly* monotone map
grows at least as fast as the identity, and the preimage function
of an injective monotone surjection is itself strictly monotone, so
both bounds squeeze.

## Bounds for strictly monotone maps

<!--
```agda
private
  le-ne-lt : ∀ {a b} → a Nat.≤ b → ¬ (a ≡ b) → a Nat.< b
  le-ne-lt {a} {b} le ne with Nat.≤-split a b
  ... | inl lt = lt
  ... | inr (inl gt) = absurd (Nat.¬sucx≤x _ (Nat.≤-trans gt le))
  ... | inr (inr eq) = absurd (ne eq)

  weaken-lower : ∀ {n} (x : Fin n) → weaken x .lower ≡ x .lower
  weaken-lower x with fin-view x
  ... | zero  = refl
  ... | suc i = ap suc (weaken-lower i)
```
-->

```agda
module _ {j k : Nat} (f : Fin (suc j) → Fin (suc k))
         (strict : ∀ x y → x .lower Nat.< y .lower
                 → f x .lower Nat.< f y .lower)
  where

  private
    grow : (t : Nat) (x : Fin (suc j)) → x .lower ≡ t
         → t Nat.≤ f x .lower
    grow zero x p = Nat.0≤x
    grow (suc t') x p = Nat.≤-trans
      (Nat.s≤s (grow t' x' refl))
      (strict x' x (subst (t' Nat.<_) (sym p) Nat.≤-refl))
      where
      bx' : suc (suc t') Nat.≤ suc j
      bx' = subst (λ z → suc z Nat.≤ suc j) p (x .Fin.bounded)
      x' : Fin (suc j)
      x' = fin t' ⦃ Nat.≤-trans Nat.≤-ascend bx' ⦄

  strict-grow : ∀ x → x .lower Nat.≤ f x .lower
  strict-grow x = grow (x .lower) x refl

  strict-grow-1
    : (∀ x → 1 Nat.≤ f x .lower)
    → ∀ x → suc (x .lower) Nat.≤ f x .lower
  strict-grow-1 pos x = go (x .lower) x refl
    where
    go : (t : Nat) (x : Fin (suc j)) → x .lower ≡ t
       → suc t Nat.≤ f x .lower
    go zero x p = pos x
    go (suc t') x p = Nat.≤-trans
      (Nat.s≤s (go t' x' refl))
      (strict x' x (subst (t' Nat.<_) (sym p) Nat.≤-refl))
      where
      bx' : suc (suc t') Nat.≤ suc j
      bx' = subst (λ z → suc z Nat.≤ suc j) p (x .Fin.bounded)
      x' : Fin (suc j)
      x' = fin t' ⦃ Nat.≤-trans Nat.≤-ascend bx' ⦄
```

## Injective monotone maps

Monotonicity turns injectivity into strictness, and the absence of
adjacent collisions into injectivity.

```agda
module _ {j k : Nat} (α : Δ-map j k) where
  private
    inj-type : Type
    inj-type = ∀ x y → α .map x ≡ α .map y → x ≡ y

  mono-inj→strict
    : inj-type
    → ∀ x y → x .lower Nat.< y .lower
    → α .map x .lower Nat.< α .map y .lower
  mono-inj→strict inj x y lt = le-ne-lt
    (α .ascending x y (Nat.<-weaken lt))
    (λ e → Nat.¬sucx≤x _
      (subst (λ (z : Fin _) → z .lower Nat.< y .lower)
        (inj x y (fin-ap {n = λ _ → suc k} e)) lt))

  no-collision→inj
    : (∀ (t : Fin j) → ¬ (α .map (weaken t) ≡ α .map (fsuc t)))
    → inj-type
  no-collision→inj nc x y p with Nat.≤-split (x .lower) (y .lower)
  ... | inr (inr eq) = fin-ap {n = λ _ → suc j} eq
  ... | inl lt = absurd (nc t coll)
    where
    bt : suc (x .lower) Nat.≤ j
    bt = Nat.≤-trans lt (Nat.≤-peel (y .Fin.bounded))
    t : Fin j
    t = fin (x .lower) ⦃ bt ⦄

    wt-x : α .map (weaken t) ≡ α .map x
    wt-x = ap (α .map)
      (fin-ap {n = λ _ → suc j} (weaken-lower t))

    sandwich : α .map (fsuc t) .lower ≡ α .map x .lower
    sandwich = Nat.≤-antisym
      (subst (λ z → α .map (fsuc t) .lower Nat.≤ z)
        (ap Fin.lower (sym p))
        (α .ascending (fsuc t) y lt))
      (subst (λ z → z Nat.≤ α .map (fsuc t) .lower)
        (ap Fin.lower wt-x)
        (α .ascending (weaken t) (fsuc t)
          (subst (Nat._≤ suc (t .lower)) (sym (weaken-lower t))
            (Nat.≤-sucr Nat.≤-refl))))

    coll : α .map (weaken t) ≡ α .map (fsuc t)
    coll = wt-x ∙ fin-ap {n = λ _ → suc k} (sym sandwich)
  ... | inr (inl gt) = absurd (nc t coll)
    where
    bt : suc (y .lower) Nat.≤ j
    bt = Nat.≤-trans gt (Nat.≤-peel (x .Fin.bounded))
    t : Fin j
    t = fin (y .lower) ⦃ bt ⦄

    wt-y : α .map (weaken t) ≡ α .map y
    wt-y = ap (α .map)
      (fin-ap {n = λ _ → suc j} (weaken-lower t))

    sandwich : α .map (fsuc t) .lower ≡ α .map y .lower
    sandwich = Nat.≤-antisym
      (subst (λ z → α .map (fsuc t) .lower Nat.≤ z)
        (ap Fin.lower p)
        (α .ascending (fsuc t) x gt))
      (subst (λ z → z Nat.≤ α .map (fsuc t) .lower)
        (ap Fin.lower wt-y)
        (α .ascending (weaken t) (fsuc t)
          (subst (Nat._≤ suc (t .lower)) (sym (weaken-lower t))
            (Nat.≤-sucr Nat.≤-refl))))

    coll : α .map (weaken t) ≡ α .map (fsuc t)
    coll = wt-y ∙ fin-ap {n = λ _ → suc k} (sym sandwich)
```
