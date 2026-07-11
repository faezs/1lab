---
description: |
  The dynamical object of a general network: activities at each
  layer, joint states at the auxiliary vertices, and transmission
  along the site's arrows, presented as a presheaf on the forked
  site.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_)
open import Data.Fin.Base

open import Neural.Graph.Fork

import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Network.Activities where
```

# The dynamical object of a network {defines="network-activities"}

Fix, for each vertex of a [[network|network-graph]], a set of
possible *activities* of its neuron population, and for each vertex a
*transmission map* computing its activity from the joint activities
of its inputs. The paper's presheaf $X^w$ (§1.3) assigns to each
ordinary vertex its activity set, to each star **and** tang the
product of the input activities — the joint state a fork consumes —
and restricts along the site's arrows by projecting (tines), doing
nothing (the socket), and transmitting (handles and single-input
edges). This module is parametric in the transmission data; fixing a
weight assignment (chapter 1's $w_0$) is fixing this parameter.

```agda
module Network-dynamics
  {ℓ} (N : Network)
  (X₀ : Fin (N .size) → Set ℓ)
  (d : ∀ c → (∀ i → ∣ X₀ (N .inputs c ! i) ∣) → ∣ X₀ c ∣)
  where
```

<!--
```agda
  private
    Γ = fork-graph N

  joint : Fin (N .size) → Type ℓ
  joint c = ∀ i → ∣ X₀ (N .inputs c ! i) ∣
```
-->

```agda
  Act : F-vtx N → Type ℓ
  Act (orig c)   = ∣ X₀ c ∣
  Act (star c f) = joint c
  Act (tang c f) = joint c

  private
    Act-is-set : ∀ v → is-set (Act v)
    Act-is-set (orig c)   = X₀ c .is-tr
    Act-is-set (star c f) = Π-is-hlevel 2 λ i → X₀ _ .is-tr
    Act-is-set (tang c f) = Π-is-hlevel 2 λ i → X₀ _ .is-tr

  one-tuple
    : ∀ {b} → ∣ X₀ b ∣
    → (i : Fin (length (b ∷ []))) → ∣ X₀ ((b ∷ []) ! i) ∣
  one-tuple x (fin zero) = x
  one-tuple x (fin (suc k) ⦃ b ⦄) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel b))

  αₑ : ∀ {v u} (e : F-edge N v u) → Act u → Act v
  αₑ {orig c} {orig b} (single q) x =
    d c (subst (λ l → (i : Fin (length l)) → ∣ X₀ (l ! i) ∣)
          (sym q) (one-tuple x))
  αₑ (tine {b = b} i q) s = subst (λ m → ∣ X₀ m ∣) q (s i)
  αₑ (socket)           s = s
  αₑ {orig c} {tang c' f'} handle s = d c s

  α : ∀ {v u} → Path-in Γ v u → Act u → Act v
  α nil        x = x
  α (cons e p) x = αₑ e (α p x)

  private
    α-++
      : ∀ {v m u} (p : Path-in Γ v m) (q : Path-in Γ m u) (x : Act u)
      → α (p ++ q) x ≡ α p (α q x)
    α-++ nil        q x = refl
    α-++ (cons e p) q x = ap (αₑ e) (α-++ p q x)

  X^ : Functor ((fork-site N) ^op) (Sets ℓ)
  X^ .Functor.F₀ v = el (Act v) (Act-is-set v)
  X^ .Functor.F₁ = α
  X^ .Functor.F-id = refl
  X^ .Functor.F-∘ f g = funext (α-++ f g)
```

Two remarks, recorded here and used by the successors of this module.
First, the value of `X^`{.Agda} at a star is *definitionally* the
product of the tip values with the tines acting by (transported)
projections, so `X^`{.Agda} restricts along the reduced category to a
presheaf on the paper's poset $\mathbf X$ — the avatar that lives in
the topos $\mathrm{PSh}(C_{\mathbf X})$ through the
[[equivalence|dnn-topos-equivalence]]. Second, the *unique-section*
theorem — a choice of activities at the input layers extends to a
unique global section of `X^`{.Agda}, which is what it means for the
network to *compute* — is the content of the input–output module,
proved by induction along the depth of the network.

Note the handle and the socket: the joint state at $A_c$ transmits
into $c$ by the transmission map, and restricts to the star
unchanged; the sheaf condition at the tine cover then identifies the
star's value with the product it already is.
