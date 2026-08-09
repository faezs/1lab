<!--
```agda
open import Cat.Instances.Simplex
open import Cat.Prelude

open import Data.Fin
open import Data.Sum

import Data.Nat as Nat

open Δ-map
```
-->

```agda
module Cat.Instances.Simplex.Factorisation where
```

# Factoring simplicial operators

Two elementary factorization facts about monotone maps drive the
normalization theorem: a map that *misses* a value factors through
the coface skipping it, and a map with an *adjacent collision*
factors through the codegeneracy collapsing it. Both are
constructive, with the witness computed by structural recursion.

## Removing a missed value

```agda
unskip
  : ∀ {n} (i y : Fin (suc n)) → ¬ (y ≡ i) → Fin n
unskip {zero} i y ne with fin-view i | fin-view y
... | zero | zero = absurd (ne refl)
... | zero | suc y' = absurd (Fin-absurd y')
... | suc i' | _ = absurd (Fin-absurd i')
unskip {suc n} i y ne with fin-view i | fin-view y
... | zero   | zero   = absurd (ne refl)
... | zero   | suc y' = y'
... | suc i' | zero   = fzero
... | suc i' | suc y' = fsuc (unskip i' y' (λ p → ne (ap fsuc p)))

unskip-skip
  : ∀ {n} (i y : Fin (suc n)) (ne : ¬ (y ≡ i))
  → skip i (unskip i y ne) ≡ y
unskip-skip {zero} i y ne with fin-view i | fin-view y
... | zero | zero = absurd (ne refl)
... | zero | suc y' = absurd (Fin-absurd y')
... | suc i' | _ = absurd (Fin-absurd i')
unskip-skip {suc n} i y ne with fin-view i | fin-view y
... | zero   | zero   = absurd (ne refl)
... | zero   | suc y' = refl
... | suc i' | zero   = refl
... | suc i' | suc y' = ap fsuc (unskip-skip i' y' (λ p → ne (ap fsuc p)))

unskip-mono
  : ∀ {n} (i x y : Fin (suc n))
    (nex : ¬ (x ≡ i)) (ney : ¬ (y ≡ i))
  → x ≤ y → unskip i x nex ≤ unskip i y ney
unskip-mono {zero} i x y nex ney le with fin-view i | fin-view x
... | zero | zero = absurd (nex refl)
... | zero | suc x' = absurd (Fin-absurd x')
... | suc i' | _ = absurd (Fin-absurd i')
unskip-mono {suc n} i x y nex ney le
  with fin-view i | fin-view x | fin-view y
... | zero   | zero   | _      = absurd (nex refl)
... | zero   | suc x' | zero   = absurd (Nat.¬suc≤0 le)
... | zero   | suc x' | suc y' = Nat.≤-peel le
... | suc i' | zero   | zero   = Nat.0≤x
... | suc i' | zero   | suc y' = Nat.0≤x
... | suc i' | suc x' | zero   = absurd (Nat.¬suc≤0 le)
... | suc i' | suc x' | suc y' = Nat.s≤s
  (unskip-mono i' x' y'
    (λ p → nex (ap fsuc p)) (λ p → ney (ap fsuc p))
    (Nat.≤-peel le))
```

A monotone map into $[k+1]$ that misses the value $i$ factors
through the coface $\delta_i$.

```agda
miss-factor
  : ∀ {j k} (α : Δ-map j (suc k)) (i : Fin (suc (suc k)))
  → (miss : ∀ x → ¬ (α .map x ≡ i))
  → Σ[ β ∈ Δ-map j k ] (δ i ∘Δ β ≡ α)
miss-factor α i miss = β ,
  Δ-map-path (λ x → unskip-skip i (α .map x) (miss x))
  where
  β : Δ-map _ _
  β .map x = unskip i (α .map x) (miss x)
  β .ascending x y le =
    unskip-mono i (α .map x) (α .map y) (miss x) (miss y)
      (α .ascending x y le)
```

## Collapsing an adjacent collision

The composite $\mathrm{skip}\,(t{+}1) \circ \mathrm{squish}\,t$ is
the identity away from $t{+}1$, which it sends to $t$.

```agda
skip-squish-adj
  : ∀ {n} (t : Fin (suc n)) (x : Fin (suc (suc n)))
  → (skip (fsuc t) (squish t x) ≡ x)
  ⊎ ((x ≡ fsuc t) × (skip (fsuc t) (squish t x) ≡ weaken t))
skip-squish-adj {n} t x with fin-view t | fin-view x
... | zero   | zero = inl refl
... | zero   | suc x' with fin-view x'
...   | zero = inr (refl , refl)
...   | suc x'' = inl refl
skip-squish-adj {n} t x | suc t' | zero = inl refl
skip-squish-adj {suc n'} t x | suc t' | suc x'
  with skip-squish-adj t' x'
... | inl p = inl (ap fsuc p)
... | inr (q , r) = inr (ap fsuc q , ap fsuc r)
```

A monotone map with an adjacent collision at $t$ factors through
the codegeneracy $\sigma_t$.

```agda
collision-factor
  : ∀ {j' k} (α : Δ-map (suc j') k) (t : Fin (suc j'))
  → α .map (weaken t) ≡ α .map (fsuc t)
  → Σ[ γ ∈ Δ-map j' k ] (γ ∘Δ σ t ≡ α)
collision-factor α t coll = γ , Δ-map-path pointwise
  where
  γ : Δ-map _ _
  γ = α ∘Δ δ (fsuc t)

  pointwise : ∀ x → α .map (skip (fsuc t) (squish t x)) ≡ α .map x
  pointwise x with skip-squish-adj t x
  ... | inl p = ap (α .map) p
  ... | inr (q , r) = ap (α .map) r ∙ coll ∙ ap (α .map) (sym q)
```
