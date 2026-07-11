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

## The two rigid cases

An injective monotone map equipped with preimages for every value
is forced to be the identity, degree included; missing only the
bottom value forces the bottom coface.

```agda
module _ {j k : Nat} (α : Δ-map j k)
         (inj : ∀ x y → α .map x ≡ α .map y → x ≡ y)
  where
  private
    α-strict : ∀ x y → x .lower Nat.< y .lower
             → α .map x .lower Nat.< α .map y .lower
    α-strict = mono-inj→strict α inj

    topJ : Fin (suc j)
    topJ = fin j ⦃ Nat.≤-refl ⦄

    topK : Fin (suc k)
    topK = fin k ⦃ Nat.≤-refl ⦄

  module _ (pre : ∀ (v : Fin (suc k)) → Σ[ x ∈ Fin (suc j) ] (α .map x ≡ v)) where
    private
      p : Fin (suc k) → Fin (suc j)
      p v = pre v .fst

      p-strict : ∀ v w → v .lower Nat.< w .lower
               → p v .lower Nat.< p w .lower
      p-strict v w lt with Nat.≤-split (p v .lower) (p w .lower)
      ... | inl lt' = lt'
      ... | inr (inl gt) = absurd (Nat.¬sucx≤x _ (Nat.≤-trans lt
        (subst₂ (λ a b → a .lower Nat.≤ b .lower)
          (pre w .snd) (pre v .snd)
          (α .ascending (p w) (p v) (Nat.<-weaken gt)))))
      ... | inr (inr eq) = absurd (Nat.¬sucx≤x _
        (subst (λ z → v .lower Nat.< z .lower)
          ( sym (pre w .snd)
          ∙ ap (α .map) (fin-ap {n = λ _ → suc j} (sym eq))
          ∙ pre v .snd)
          lt))

      p-section : ∀ x → p (α .map x) ≡ x
      p-section x = inj _ _ (pre (α .map x) .snd)

    rigid-degree : j ≡ k
    rigid-degree = Nat.≤-antisym
      (Nat.≤-trans (strict-grow (α .map) α-strict topJ)
        (Nat.≤-peel (α .map topJ .Fin.bounded)))
      (Nat.≤-trans (strict-grow p p-strict topK)
        (Nat.≤-peel (p topK .Fin.bounded)))

    rigid-id : ∀ x → α .map x .lower ≡ x .lower
    rigid-id x = Nat.≤-antisym
      (subst (λ z → α .map x .lower Nat.≤ z .lower) (p-section x)
        (strict-grow p p-strict (α .map x)))
      (strict-grow (α .map) α-strict x)
```

For the coface case we pin the codomain to be positive.

```agda
module _ {j k' : Nat} (α : Δ-map j (suc k'))
         (inj : ∀ x y → α .map x ≡ α .map y → x ≡ y)
         (miss0 : ∀ x → ¬ (α .map x ≡ fzero))
         (pre₁ : ∀ (v : Fin (suc k')) → Σ[ x ∈ Fin (suc j) ] (α .map x ≡ fsuc v))
  where
  private
    α-strict : ∀ x y → x .lower Nat.< y .lower
             → α .map x .lower Nat.< α .map y .lower
    α-strict = mono-inj→strict α inj

    α-pos : ∀ x → 1 Nat.≤ α .map x .lower
    α-pos x with Nat.≤-split 1 (α .map x .lower)
    ... | inl lt = Nat.<-weaken lt
    ... | inr (inr eq) = subst (1 Nat.≤_) eq Nat.≤-refl
    ... | inr (inl lt) = absurd (miss0 x
      (fin-ap {n = λ _ → suc (suc k')}
        (Nat.≤-antisym (Nat.≤-peel lt) Nat.0≤x)))

    p : Fin (suc k') → Fin (suc j)
    p v = pre₁ v .fst

    p-strict : ∀ v w → v .lower Nat.< w .lower
             → p v .lower Nat.< p w .lower
    p-strict v w lt with Nat.≤-split (p v .lower) (p w .lower)
    ... | inl lt' = lt'
    ... | inr (inl gt) = absurd (Nat.¬sucx≤x _ (Nat.≤-trans (Nat.s≤s lt)
      (subst₂ (λ a b → a .lower Nat.≤ b .lower)
        (pre₁ w .snd) (pre₁ v .snd)
        (α .ascending (p w) (p v) (Nat.<-weaken gt)))))
    ... | inr (inr eq) = absurd (Nat.¬sucx≤x _
      (Nat.s≤s (Nat.≤-peel (subst (λ z → suc (v .lower) Nat.< z .lower)
        ( sym (pre₁ w .snd)
        ∙ ap (α .map) (fin-ap {n = λ _ → suc j} (sym eq))
        ∙ pre₁ v .snd)
        (Nat.s≤s lt)))))

    topJ : Fin (suc j)
    topJ = fin j ⦃ Nat.≤-refl ⦄

    topK : Fin (suc k')
    topK = fin k' ⦃ Nat.≤-refl ⦄

  coface-degree : suc k' ≡ suc j
  coface-degree = Nat.≤-antisym
    (Nat.s≤s (Nat.≤-trans (strict-grow p p-strict topK)
      (Nat.≤-peel (p topK .Fin.bounded))))
    (Nat.≤-trans (strict-grow-1 (α .map) α-strict α-pos topJ)
      (Nat.≤-peel (α .map topJ .Fin.bounded)))

  coface-id : ∀ x → α .map x .lower ≡ suc (x .lower)
  coface-id x = Nat.≤-antisym upper (strict-grow-1 (α .map) α-strict α-pos x)
    where
    t : Nat
    t = Nat.pred (α .map x .lower)

    t-eq : α .map x .lower ≡ suc t
    t-eq with α .map x .lower | α-pos x
    ... | zero  | ge = absurd (Nat.¬suc≤0 ge)
    ... | suc n | ge = refl

    bt : suc t Nat.≤ suc k'
    bt = Nat.≤-peel (subst (λ z → z Nat.≤ suc (suc k')) (ap suc t-eq)
      (α .map x .Fin.bounded))

    tf : Fin (suc k')
    tf = fin t ⦃ bt ⦄

    ptf-x : p tf ≡ x
    ptf-x = inj _ _ (pre₁ tf .snd ∙ fin-ap {n = λ _ → suc (suc k')} (sym t-eq))

    upper : α .map x .lower Nat.≤ suc (x .lower)
    upper = subst₂ (λ a b → a Nat.≤ suc b)
      (sym t-eq)
      (ap Fin.lower ptf-x)
      (Nat.s≤s (strict-grow p p-strict tf))
```

## The classification

Every monotone map into a positive ordinal is of one of four
shapes, decidably: it misses a positive value, it has an adjacent
collision, it is the identity, or it is the bottom coface.

```agda
data Δ-class {j k' : Nat} (α : Δ-map j (suc k')) : Type where
  cls-miss : (i' : Fin (suc k')) → (∀ x → ¬ (α .map x ≡ fsuc i'))
           → Δ-class α
  cls-coll : (t : Fin j) → α .map (weaken t) ≡ α .map (fsuc t)
           → Δ-class α
  cls-id   : j ≡ suc k' → (∀ x → α .map x .lower ≡ x .lower)
           → Δ-class α
  cls-δ⁰   : suc k' ≡ suc j → (∀ x → α .map x .lower ≡ suc (x .lower))
           → Δ-class α

classify : ∀ {j k'} (α : Δ-map j (suc k')) → Δ-class α
classify {j} {k'} α with
  holds? (Σ[ i' ∈ Fin (suc k') ] (∀ x → ¬ (α .map x ≡ fsuc i')))
... | yes (i' , m) = cls-miss i' m
... | no ¬m with
  holds? (Σ[ t ∈ Fin j ] (α .map (weaken t) ≡ α .map (fsuc t)))
...   | yes (t , c) = cls-coll t c
...   | no ¬c = rest
  where
  inj : ∀ x y → α .map x ≡ α .map y → x ≡ y
  inj = no-collision→inj α (λ t c → ¬c (t , c))

  hits-pos : ∀ (v : Fin (suc k')) → Σ[ x ∈ Fin (suc j) ] (α .map x ≡ fsuc v)
  hits-pos v with holds? (Σ[ x ∈ Fin (suc j) ] (α .map x ≡ fsuc v))
  ... | yes it = it
  ... | no ¬p = absurd (¬m (v , λ x e → ¬p (x , e)))

  rest : Δ-class α
  rest with holds? (Σ[ x ∈ Fin (suc j) ] (α .map x ≡ fzero))
  ... | yes h0 = cls-id
      (rigid-degree α inj pre) (rigid-id α inj pre)
    where
    pre : ∀ (v : Fin (suc (suc k'))) → Σ[ x ∈ Fin (suc j) ] (α .map x ≡ v)
    pre v with fin-view v
    ... | zero = h0
    ... | suc v' = hits-pos v'
  ... | no ¬h0 = cls-δ⁰
      (coface-degree α inj (λ x e → ¬h0 (x , e)) hits-pos)
      (coface-id α inj (λ x e → ¬h0 (x , e)) hits-pos)
```
