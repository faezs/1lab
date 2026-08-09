---
description: |
  The input–output relation as zeroth cohomology: global sections of
  the dynamical object are exactly the input assignments, packaged
  as H⁰ of the network topos.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_)
open import Data.Fin.Base

open import Neural.Network.Sections
open import Neural.Graph.Fork
```
-->

```agda
module Neural.Semantics.InputOutput where
```

# The input–output relation as H⁰ {defines="network-h0"}

The zeroth cohomology of a topos with coefficients in a presheaf is
its set of *global sections* — natural transformations from the
terminal presheaf. For the dynamical object of a network, the
[[unique-section theorem]] already identifies sections with input
assignments; this module supplies the missing packaging: global
sections in the categorical sense coincide with the vertexwise
sections of the theorem, so
$$
H^0(\cE_N, X^w) \;\simeq\; \text{Inputs},
$$
the paper's statement that *the network topos computes the
input–output relation in degree zero*.

```agda
module Network-H⁰
  {ℓ} (N : Network)
  (X₀ : Fin (N .Network.size) → Set ℓ)
  (d : ∀ c → (∀ i → ∣ X₀ (N .Network.inputs c ! i) ∣) → ∣ X₀ c ∣)
  where

  open Network-sections N X₀ d public
```

<!--
```agda
  private
    Γn = fork-graph N

  open Functor
  open _=>_
```
-->

Global sections, concretely: the terminal presheaf on the fork site,
and maps out of it.

```agda
  ⊤psh : Functor ((fork-site N) ^op) (Sets ℓ)
  ⊤psh .F₀ _ = el! (Lift ℓ ⊤)
  ⊤psh .F₁ _ x = x
  ⊤psh .F-id = refl
  ⊤psh .F-∘ _ _ = refl

  H⁰ : Functor ((fork-site N) ^op) (Sets ℓ) → Type ℓ
  H⁰ X = ⊤psh => X
```

A global section of `X^`{.Agda ident=X^} restricts to a vertexwise
section along the single-edge paths; conversely a vertexwise section
extends to all paths by folding its edge equations, which is exactly
naturality over the free site.

```agda
  global→section : (⊤psh => X^) → NSection
  global→section h .fst v = h .η v (lift tt)
  global→section h .snd v u e =
    sym (happly (h .is-natural u v (cons e nil)) (lift tt))

  section→global : NSection → (⊤psh => X^)
  section→global (at , resp) .η v _ = at v
  section→global (at , resp) .is-natural u v p = funext λ _ → sym (go p)
    where
      go : ∀ {v u} (p : Path-in Γn v u) → α p (at u) ≡ at v
      go nil        = refl
      go (cons e q) = ap (αₑ e) (go q) ∙ resp _ _ e

  H⁰≃section : H⁰ X^ ≃ NSection
  H⁰≃section = Iso→Equiv
    ( global→section
    , iso section→global
        (λ s → Σ-prop-path
          (λ at → Π-is-hlevel 1 λ v → Π-is-hlevel 1 λ u → Π-is-hlevel 1
            λ e → Act-is-set v (αₑ e (at u)) (at v))
          refl)
        (λ h → Nat-path λ v → funext λ x → refl))

  H⁰≃inputs : H⁰ X^ ≃ Inputs
  H⁰≃inputs = H⁰≃section ∙e section≃inputs
```

What is honestly *not* here: higher cohomology — the network sites
are free and finite, so the interesting degrees for the paper only
appear with the braid tower of chapter 4 — and the sheaf-level
statement, which via the [[topos equivalence|dnn-topos-equivalence]]
adds nothing over the presheaf one.
