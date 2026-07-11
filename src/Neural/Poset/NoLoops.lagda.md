---
description: |
  Loop-freeness of the forked site: exit lemmas for stars and tangs,
  the translation of single-input chains back to network paths, the
  route classification of arrows into a tang, and the absence of
  nonempty endomorphisms.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_ ; ∷-head-inj)
open import Data.Fin.Base
open import Data.Sum.Base

open import Neural.Graph.Fork

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Poset.NoLoops where
```

# Loop-freeness of the forked site {defines="fork-no-loops"}

This module proves that the forked site of a [[network|network-graph]]
has no nonempty endomorphisms — the combinatorial backbone of the
antisymmetry half of Belfiore–Bennequin's Proposition 1.1, and of the
thinness proof that follows in [`Neural.Poset.Thin`]. Everything here
is unconditional: no spacelike hypothesis is needed yet.

[`Neural.Poset.Thin`]: Neural.Poset.Thin.html

<!--
```agda
module _ (N : Network) where
  private
    Γ  = fork-graph N
    Γ₀ = network-graph N

  vtx-name : F-vtx N → Fin (N .size)
  vtx-name (orig c)   = c
  vtx-name (star c f) = c
  vtx-name (tang c f) = c

  is-orig-vtx is-star-vtx is-tang-vtx : F-vtx N → Type
  is-orig-vtx (orig _)   = ⊤
  is-orig-vtx (star _ _) = ⊥
  is-orig-vtx (tang _ _) = ⊥
  is-star-vtx (orig _)   = ⊥
  is-star-vtx (star _ _) = ⊤
  is-star-vtx (tang _ _) = ⊥
  is-tang-vtx (orig _)   = ⊥
  is-tang-vtx (star _ _) = ⊥
  is-tang-vtx (tang _ _) = ⊤
```
-->

The only edge out of a star is its socket, and nothing leaves a tang;
consequently no path can leave a star and return to an ordinary or
star vertex. These are the *exit lemmas*.

```agda
  edge-out-of-star
    : ∀ {c f v} → F-edge N (star c f) v
    → Σ[ f' ∈ is-fork N c ] (v ≡ tang c f')
  edge-out-of-star (socket {f' = f'}) = f' , refl

  star-to-orig : ∀ {c f b} → Path-in Γ (star c f) (orig b) → ⊥
  star-to-orig (cons socket p) =
    subst is-tang-vtx (path-out-of-tang-is-nil N p .fst) tt

  star-to-star
    : ∀ {c f c' f'} (p : Path-in Γ (star c f) (star c' f'))
    → ∣ nonempty N p ∣ → ⊥
  star-to-star nil             ne = ne
  star-to-star (cons socket p) _  =
    subst is-tang-vtx (path-out-of-tang-is-nil N p .fst) tt
```

A path between ordinary vertices can never pass through a star or a
tang, so it consists of single-input transmissions only; reversing
it, edge by edge, produces a path of the *network* graph. Note the
reversal: site transmissions run from deeper to shallower vertices,
network edges from inputs to consumers.

```agda
  edge-of-single
    : ∀ {u b} → N .inputs u ≡ b ∷ []
    → network-graph N .Graph.Edge b u
  edge-of-single {u} {b} q =
    subst (λ l → Σ[ i ∈ Fin (length l) ] (l ! i ≡ b)) (sym q) (fzero , refl)

  singles→network'
    : ∀ {u v' w} → Path-in Γ (orig u) v' → v' ≡ orig w
    → Path-in Γ₀ w u
  singles→network' {u} nil eq' =
    subst (λ m → Path-in Γ₀ m u) (ap vtx-name eq') nil
  singles→network' (cons (single q) p) eq' =
    singles→network' p eq' ++ cons (edge-of-single q) nil
  singles→network' (cons (tine i q) p) eq' =
    absurd (star-to-orig (subst (Path-in Γ _) eq' p))
  singles→network' (cons handle p) eq' = absurd
    (subst is-tang-vtx (path-out-of-tang-is-nil N p .fst ∙ eq') tt)

  singles→network
    : ∀ {u w} → Path-in Γ (orig u) (orig w)
    → Path-in Γ₀ w u
  singles→network p = singles→network' p refl
```

**Route classification.** An arrow from an ordinary vertex into the
tang $A_c$ arrives in one of exactly two ways: down a single-input
chain to $c$ itself and in through the handle, or down a chain to
one of $c$'s tips and in through that tine and the socket. The
classification returns the network-path evidence in either case —
this is the datum on which both the spacelike argument and the
depth arguments operate.

```agda
  Route : Fin (N .size) → Fin (N .size) → Type
  Route v c
    = Path-in Γ₀ c v
    ⊎ (Σ[ j ∈ Fin (length (N .inputs c)) ]
        Path-in Γ₀ (N .inputs c ! j) v)

  reach
    : ∀ {v c fc} → Path-in Γ (orig v) (tang c fc)
    → Route v c
  reach (cons (single q) p) with reach p
  ... | inl γ       = inl (γ ++ cons (edge-of-single q) nil)
  ... | inr (j , γ) = inr (j , γ ++ cons (edge-of-single q) nil)
  reach {v} {c} {fc} (cons (handle {f = f}) p) =
    inl (subst (λ m → Path-in Γ₀ m v) veq nil)
    where
      veq : v ≡ c
      veq = ap vtx-name (path-out-of-tang-is-nil N p .fst)
  reach {v} {c} {fc} (cons (tine {c = c'} {f = f'} j q) (cons socket p')) =
    inr (subst
      (λ m → Σ[ j' ∈ Fin (length (N .inputs m)) ]
              Path-in Γ₀ (N .inputs m ! j') v)
      (ap vtx-name (path-out-of-tang-is-nil N p' .fst))
      (j , subst (λ m → Path-in Γ₀ m v) (sym q) nil))
```

The star-directed analogue of `reach`{.Agda}: an arrow from an
ordinary vertex into a star arrives through exactly one tine, at the
end of a single-input chain. And a variant of `reach`{.Agda} for
paths known to begin with a single-input transmission, which
additionally records that the resulting network path is nonempty —
the datum the spacelike contradiction of [`Neural.Poset.Thin`]
consumes.

```agda
  net-nonempty : ∀ {v u} → Path-in Γ₀ v u → Type
  net-nonempty nil        = ⊥
  net-nonempty (cons _ _) = ⊤

  snoc-nonempty
    : ∀ {v m u} (γ : Path-in Γ₀ v m) {e : Γ₀ .Graph.Edge m u}
    → net-nonempty (γ ++ cons e nil)
  snoc-nonempty nil        = tt
  snoc-nonempty (cons _ _) = tt

  network-loop
    : ∀ {a a'} (γ : Path-in Γ₀ a a') → a ≡ a' → net-nonempty γ → ⊥
  network-loop nil        eq ne = ne
  network-loop (cons e γ) eq ne =
    network-no-loop N e (subst (λ m → Path-in Γ₀ _ m) (sym eq) γ)

  reach-star
    : ∀ {v c fc} → Path-in Γ (orig v) (star c fc)
    → Σ[ j ∈ Fin (length (N .inputs c)) ]
        Path-in Γ₀ (N .inputs c ! j) v
  reach-star (cons (single q) p) with reach-star p
  ... | (j , γ) = j , γ ++ cons (edge-of-single q) nil
  reach-star {v} (cons (tine {c = c'} {f = f'} j q) p) with p
  ... | nil = j , subst (λ m → Path-in Γ₀ m v) (sym q) nil
  ... | cons socket p' = absurd
    (subst is-tang-vtx (path-out-of-tang-is-nil N p' .fst) tt)
  reach-star (cons handle p) = absurd
    (subst is-tang-vtx (path-out-of-tang-is-nil N p .fst) tt)

  reach-from-single
    : ∀ {a b c fc} → N .inputs a ≡ b ∷ []
    → Path-in Γ (orig b) (tang c fc)
    → (Σ[ γ ∈ Path-in Γ₀ c a ] net-nonempty γ)
    ⊎ (Σ[ j ∈ Fin (length (N .inputs c)) ]
        Σ[ γ ∈ Path-in Γ₀ (N .inputs c ! j) a ] net-nonempty γ)
  reach-from-single q p with reach p
  ... | inl γ       = inl (γ ++ cons (edge-of-single q) nil , snoc-nonempty γ)
  ... | inr (j , γ) =
    inr (j , γ ++ cons (edge-of-single q) nil , snoc-nonempty γ)

  reach-star-from-single
    : ∀ {a b c fc} → N .inputs a ≡ b ∷ []
    → Path-in Γ (orig b) (star c fc)
    → Σ[ j ∈ Fin (length (N .inputs c)) ]
        Σ[ γ ∈ Path-in Γ₀ (N .inputs c ! j) a ] net-nonempty γ
  reach-star-from-single q p with reach-star p
  ... | (j , γ) = j , γ ++ cons (edge-of-single q) nil , snoc-nonempty γ
```

[`Neural.Poset.Thin`]: Neural.Poset.Thin.html

## No nonempty loops

A nonempty loop is impossible at every vertex type: a loop of
single-input transmissions at an ordinary vertex reverses to a
nonempty cycle of the network graph, contradicting directedness;
leaving an ordinary vertex through a tine or a handle strands the
path at a star or a tang; and stars and tangs have no exits at all.

```agda

  no-loop : ∀ {v} (p : Path-in Γ v v) → ∣ nonempty N p ∣ → ⊥
  no-loop p ne = go p refl ne where
    go : ∀ {v v'} (p : Path-in Γ v v') → v ≡ v' → ∣ nonempty N p ∣ → ⊥
    go nil eq ne = ne
    go (cons (single q) p) eq ne =
      network-loop (singles→network' (cons (single q) p) (sym eq)) refl
        (snoc-nonempty (singles→network' p (sym eq)))
    go (cons (tine i q) p) eq ne =
      star-to-orig (subst (Path-in Γ _) (sym eq) p)
    go (cons handle p) eq ne = subst is-tang-vtx
      (path-out-of-tang-is-nil N p .fst ∙ sym eq) tt
    go (cons socket p) eq ne = subst is-tang-vtx
      (path-out-of-tang-is-nil N p .fst ∙ sym eq) tt
```
