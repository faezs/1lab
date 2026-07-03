<!--
```agda
open import Cat.Instances.SimplicialSets.Nerve
open import Cat.Instances.SimplicialSets
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Action
open import Algebra.Group

open import Data.Nat.Base using (s≤s)
open import Data.Fin

import Data.Nat.Base as Nat
import Cat.Reasoning

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.SimplicialSets.ActionGroupoid
  (G : Group lzero) (X : Set lzero)
  (A : Action (Sets lzero) G X)
  where
```

<!--
```agda
private
  module Grp = Group-on (G .snd)
  module Sl = Cat.Reasoning (Sets lzero)

  infixl 30 _·ₓ_
  _·ₓ_ : ⌞ G ⌟ → ⌞ X ⌟ → ⌞ X ⌟
  g ·ₓ x = (A · g) .Sl.to x
```
-->

# The action groupoid {defines="action-groupoid homotopy-quotient"}

For a [[group]] $G$ acting on a set $X$ of field configurations, the
**action groupoid** $X /\!\!/ G$ — the *homotopy quotient* — is the
category whose objects are the configurations and whose morphisms $x
\to y$ are the gauge transformations carrying one to the other:
elements $g$ with $g \cdot x = y$. Unlike the naive quotient set, it
*remembers* how two configurations are identified, which is exactly
the information that gauge theory forbids discarding.

```agda
Action-groupoid : Precategory lzero lzero
Action-groupoid .Ob = ⌞ X ⌟
Action-groupoid .Hom x y = Σ ⌞ G ⌟ (λ g → g ·ₓ x ≡ y)
Action-groupoid .Hom-set x y = Σ-is-hlevel 2 (G .fst .is-tr) λ g →
  is-prop→is-set (X .is-tr _ _)
Action-groupoid .id {x} = Grp.unit ,
  ap (λ e → e .Sl.to x) (is-group-hom.pres-id (A .snd))
Action-groupoid ._∘_ {x} {y} {z} (h , q) (g , p) = g Grp.⋆ h ,
     ap (λ e → e .Sl.to x) (is-group-hom.pres-⋆ (A .snd) g h)
  ∙∙ ap (h ·ₓ_) p
  ∙∙ q
Action-groupoid .idr f = Σ-prop-path (λ g → X .is-tr _ _) Grp.idl
Action-groupoid .idl f = Σ-prop-path (λ g → X .is-tr _ _) Grp.idr
Action-groupoid .assoc f g h =
  Σ-prop-path (λ g → X .is-tr _ _) (sym Grp.associative)
```

Its simplicial incarnation is the [[nerve]]: the **homotopy
quotient** as a simplicial set, the paper's gauge groupoid of
fields. Its structure in low dimensions is exactly as the physics
demands, and we verify this in the manner of the [[delooping
computations|simplicial-delooping]].

```agda
homotopy-quotient : ⌞ sSet ⌟
homotopy-quotient = nerve Action-groupoid (X .is-tr)
```

A vertex is a single field configuration.

```agda
quotient-vertices : ⌞ homotopy-quotient .F₀ 0 ⌟ ≃ ⌞ X ⌟
quotient-vertices = Iso→Equiv (to , iso from (λ _ → refl) from-to) where
  to : Functor (ordinal 0) Action-groupoid → ⌞ X ⌟
  to F = F .F₀ fzero

  from : ⌞ X ⌟ → Functor (ordinal 0) Action-groupoid
  from x .F₀ _ = x
  from x .F₁ _ = Action-groupoid .id
  from x .F-id = refl
  from x .F-∘ _ _ = sym (Action-groupoid .idl _)

  from-to : ∀ F → from (to F) ≡ F
  from-to F = Functor-path ob λ {x} {y} p → hom x y p where
    ob : ∀ u → F .F₀ fzero ≡ F .F₀ u
    ob (fin 0) = refl
    ob (fin (suc k) ⦃ b ⦄) = absurd (Nat.¬suc≤0 (Nat.≤-peel b))

    hom : ∀ x y (p : x ≤ y) → PathP
      (λ i → Action-groupoid .Hom (ob x i) (ob y i))
      (Action-groupoid .id) (F .F₁ p)
    hom (fin 0) (fin 0) p =
      sym (ap (F .F₁) (Nat.≤-is-prop p _) ∙ F .F-id)
    hom (fin (suc k) ⦃ b ⦄) y p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel b))
    hom x (fin (suc k) ⦃ b ⦄) p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel b))
```

An edge is a configuration together with a gauge transformation
*acting on it* — the target vertex is determined, being the acted-on
configuration. This is the simplicial shadow of the projection $X
\times G \to X /\!\!/ G$.

```agda
quotient-edges : ⌞ homotopy-quotient .F₀ 1 ⌟ ≃ (⌞ X ⌟ × ⌞ G ⌟)
quotient-edges = Iso→Equiv (to , iso from (λ _ → refl) from-to) where
  to : Functor (ordinal 1) Action-groupoid → ⌞ X ⌟ × ⌞ G ⌟
  to F = F .F₀ fzero , F .F₁ {fzero} {fsuc fzero} Nat.0≤x .fst

  module _ ((x , g) : ⌞ X ⌟ × ⌞ G ⌟) where
    ob : Fin 2 → ⌞ X ⌟
    ob (fin 0) = x
    ob (fin 1) = g ·ₓ x
    ob (fin (suc (suc k)) ⦃ b ⦄) =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))

    edge : ∀ u v → u ≤ v → Action-groupoid .Hom (ob u) (ob v)
    edge (fin 0) (fin 0) p = Action-groupoid .id
    edge (fin 0) (fin 1) p = g , refl
    edge (fin 1) (fin 1) p = Action-groupoid .id
    edge (fin 1) (fin 0) p = absurd (Nat.¬suc≤0 p)
    edge (fin (suc (suc k)) ⦃ b ⦄) v p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
    edge u (fin (suc (suc k)) ⦃ b ⦄) p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))

    edge-id : ∀ u → edge u u _ ≡ Action-groupoid .id
    edge-id (fin 0) = refl
    edge-id (fin 1) = refl
    edge-id (fin (suc (suc k)) ⦃ b ⦄) =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))

    edge-∘
      : ∀ u v w (p : v ≤ w) (q : u ≤ v)
      → edge u w (Nat.≤-trans q p)
      ≡ Action-groupoid ._∘_ (edge v w p) (edge u v q)
    edge-∘ (fin 0) (fin 0) (fin 0) p q = sym (Action-groupoid .idl _)
    edge-∘ (fin 0) (fin 0) (fin 1) p q = sym (Action-groupoid .idr _)
    edge-∘ (fin 0) (fin 1) (fin 1) p q = sym (Action-groupoid .idl _)
    edge-∘ (fin 1) (fin 1) (fin 1) p q = sym (Action-groupoid .idl _)
    edge-∘ (fin 0) (fin 1) (fin 0) p q = absurd (Nat.¬suc≤0 p)
    edge-∘ (fin 1) (fin 0) w p q = absurd (Nat.¬suc≤0 q)
    edge-∘ (fin (suc (suc k)) ⦃ b ⦄) v w p q =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
    edge-∘ u (fin (suc (suc k)) ⦃ b ⦄) w p q =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
    edge-∘ u v (fin (suc (suc k)) ⦃ b ⦄) p q =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))

  from : ⌞ X ⌟ × ⌞ G ⌟ → Functor (ordinal 1) Action-groupoid
  from xg .F₀ = ob xg
  from xg .F₁ {u} {v} p = edge xg u v p
  from xg .F-id {u} = edge-id xg u
  from xg .F-∘ {u} {v} {w} p q =
      ap (edge xg u w) (Nat.≤-is-prop _ _)
    ∙ edge-∘ xg u v w p q

  from-to : ∀ F → from (to F) ≡ F
  from-to F = Functor-path obs λ {x} {y} p → hom x y p where
    gᶠ : ⌞ G ⌟
    gᶠ = F .F₁ {fzero} {fsuc fzero} Nat.0≤x .fst

    obs : ∀ u → ob (to F) u ≡ F .F₀ u
    obs (fin 0) = refl
    obs (fin 1) = F .F₁ {fzero} {fsuc fzero} Nat.0≤x .snd
    obs (fin (suc (suc k)) ⦃ b ⦄) =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))

    hom : ∀ x y (p : x ≤ y) → PathP
      (λ i → Action-groupoid .Hom (obs x i) (obs y i))
      (edge (to F) x y p) (F .F₁ p)
    hom (fin 0) (fin 0) p = Σ-pathp
      (ap fst (sym (ap (F .F₁) (Nat.≤-is-prop p _) ∙ F .F-id)))
      (is-prop→pathp (λ i → X .is-tr _ _) _ _)
    hom (fin 1) (fin 1) p = Σ-pathp
      (ap fst (sym (ap (F .F₁) (Nat.≤-is-prop p _) ∙ F .F-id)))
      (is-prop→pathp (λ i → X .is-tr _ _) _ _)
    hom (fin 0) (fin 1) p = Σ-pathp
      (ap fst (ap (F .F₁) (Nat.≤-is-prop Nat.0≤x p)))
      (is-prop→pathp (λ i → X .is-tr _ _) _ _)
    hom (fin 1) (fin 0) p = absurd (Nat.¬suc≤0 p)
    hom (fin (suc (suc k)) ⦃ b ⦄) y p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
    hom x (fin (suc (suc k)) ⦃ b ⦄) p =
      absurd (Nat.¬suc≤0 (Nat.≤-peel (Nat.≤-peel b)))
```

Higher simplices are strings of gauge transformations, as for any
nerve; the horn-filling exhibiting the homotopy quotient as a [[Kan
complex]], and its identification with the quotient *stack* over a
geometric site, are future work.
