---
description: |
  The golden thread: the chain network (multilayer perceptron), its
  site, the presheaves of activities and unconsumed weights, the
  crossed dynamical object, and the fiber theorem identifying a fixed
  functioning as the fiber of the weight projection over its section.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.Bool.Base
open import Data.Fin.Base

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Chain where
```

# The chain network {defines="chain-network"}

The simplest deep neural network is a **chain**: layers $L_0, \dots,
L_n$ with one bundle of connections from each layer to the next — a
multilayer perceptron. Following [`Neural.Base`], the *site* of the
network is the opposite of the free category on the chain graph, so
that presheaves on the site transport activities forward, from the
input layer $L_0$ toward the output layer $L_n$. This module is the
**golden thread** of the topos-of-DNNs development: every later
construction on general architectures is instantiated here first,
where everything computes.

[`Neural.Base`]: Neural.Base.html

The chain graph has node set $\{0, \dots, n\}$ and exactly one edge
$k \to k+1$ for each $k < n$; we encode an edge from $k$ to $l$ as the
(propositional, decidable) constraint $k + 1 = l$, wrapped in a record
so that an edge determines its endpoints during unification.

```agda
record Chain-edge (n : Nat) (k l : Fin (suc n)) : Type where
  constructor chain-edge
  field lowers : suc (k .lower) ≡ l .lower

open Chain-edge public

unquoteDecl H-Level-Chain-edge =
  declare-record-hlevel 1 H-Level-Chain-edge (quote Chain-edge)

module _ (n : Nat) where
  chain-graph : Graph lzero lzero
  chain-graph .Graph.Node = Fin (suc n)
  chain-graph .Graph.Edge = Chain-edge n
  chain-graph .Graph.Node-set = hlevel 2
  chain-graph .Graph.Edge-set = hlevel 2

  chain-site : Precategory lzero lzero
  chain-site = Path-category chain-graph ^op
```

Because every edge strictly increases the layer index, paths only run
upward, and in particular the chain has no oriented cycles: a
nonempty path can never return to its starting layer. This is the
first instance of the *directedness* required of every network
architecture in chapter 1 of Belfiore–Bennequin.

```agda
  path-≤
    : ∀ {k l} → Path-in chain-graph k l
    → k .lower Nat.≤ l .lower
  path-≤ nil        = Nat.≤-refl
  path-≤ (cons e p) =
    Nat.<-weaken (subst (Nat._≤ _) (sym (e .lowers)) (path-≤ p))

  private
    suc≰self : ∀ x → Nat.suc x Nat.≤ x → ⊥
    suc≰self zero    p = Nat.¬suc≤0 p
    suc≰self (suc x) p = suc≰self x (Nat.≤-peel p)

  chain-no-loop
    : ∀ {k b} (e : chain-graph .Graph.Edge k b)
    → Path-in chain-graph b k → ⊥
  chain-no-loop {k} {b} e p = suc≰self (k .lower)
    (subst (Nat._≤ _) (sym (e .lowers)) (path-≤ p))
```

## The dynamical objects

Fix, for every layer, a set of possible *activities* of its neuron
population; for every edge, a set of *weights*; and for every edge a
*transmission map* sending a weight and an activity of the source
layer to an activity of the target layer. Everything below is
parametric in this data.

```agda
module Chain-dynamics
  (n : Nat)
  (X : Fin (suc n) → Set lzero)
  (W : ∀ {k l} (e : chain-graph n .Graph.Edge k l) → Set lzero)
  (d : ∀ {k l} (e : chain-graph n .Graph.Edge k l)
     → ∣ W e ∣ → ∣ X k ∣ → ∣ X l ∣)
  where
```

<!--
```agda
  private
    Γ = chain-graph n
    module Γ = Graph Γ

  open Functor
  open _=>_
```
-->

**The functioning at fixed weights.** Given a total assignment of
weights $w_0$, transmission along a path is the fold of the edge
maps. This is the paper's presheaf $X^w$ on the site — recorded here,
per our convention, as the equivalent *covariant* functor on the path
category.

```agda
  module _ (w₀ : ∀ {k l} (e : Γ.Edge k l) → ∣ W e ∣) where
    transmit : ∀ {k l} → Path-in Γ k l → ∣ X k ∣ → ∣ X l ∣
    transmit nil        x = x
    transmit (cons e p) x = transmit p (d e (w₀ e) x)

    transmit-++
      : ∀ {a b c} (p : Path-in Γ a b) (q : Path-in Γ b c) (x : ∣ X a ∣)
      → transmit (p ++ q) x ≡ transmit q (transmit p x)
    transmit-++ nil        q x = refl
    transmit-++ (cons e p) q x = transmit-++ p q (d e (w₀ e) x)

    X^ : Functor (Path-category Γ) (Sets lzero)
    X^ .F₀ = X
    X^ .F₁ = transmit
    X^ .F-id = refl
    X^ .F-∘ f g = funext (transmit-++ g f)
```

**The presheaf of unconsumed weights.** At layer $k$, the network
still owns the weights of every edge whose source lies at or beyond
$k$; passing along a path only *forgets* weights. A pleasant
technical point: 1lab's ordering on natural numbers is definitionally
proof-irrelevant, so the restriction maps compose *strictly*, and the
functor laws below are `refl`{.Agda}.

```agda
  Wleft : Fin (suc n) → Type
  Wleft k =
    ∀ (a b : Fin (suc n)) (e : Γ.Edge a b)
    → k .lower Nat.≤ a .lower → ∣ W e ∣

  𝕎 : Functor (Path-category Γ) (Sets lzero)
  𝕎 .F₀ k = el! (Wleft k)
  𝕎 .F₁ p w a b e q = w a b e (Nat.≤-trans (path-≤ n p) q)
  𝕎 .F-id = refl
  𝕎 .F-∘ f g = refl
```

**The crossed dynamical object.** The total functioning $\XX$ carries
an activity *and* the unconsumed weights; along the edge $k \to k+1$
it applies the first weight to the activity and forgets it
(equation (1.1) of the paper).

```agda
  Xtot : Fin (suc n) → Type
  Xtot k = ∣ X k ∣ × Wleft k

  private
    step
      : ∀ {a b} (e : Γ.Edge a b)
      → Xtot a → Xtot b
    step {a} {b} e (x , w) =
      d e (w a b e Nat.≤-refl) x ,
      λ s t e' q → w s t e'
        (Nat.<-weaken (subst (Nat._≤ _) (sym (e .lowers)) q))

    evolve : ∀ {k l} → Path-in Γ k l → Xtot k → Xtot l
    evolve nil        s = s
    evolve (cons e p) s = evolve p (step e s)

    evolve-++
      : ∀ {a b c} (p : Path-in Γ a b) (q : Path-in Γ b c) (s : Xtot a)
      → evolve (p ++ q) s ≡ evolve q (evolve p s)
    evolve-++ nil        q s = refl
    evolve-++ (cons e p) q s = evolve-++ p q (step e s)

  𝕏 : Functor (Path-category Γ) (Sets lzero)
  𝕏 .F₀ k = el! (Xtot k)
  𝕏 .F₁ = evolve
  𝕏 .F-id = refl
  𝕏 .F-∘ f g = funext (evolve-++ g f)
```

The projection onto the weights is natural: evolving and then
forgetting the activity is the same as only forgetting weights.
Definitional proof irrelevance strikes again — the square commutes
by induction with every step `refl`{.Agda}.

```agda
  private
    evolve-snd
      : ∀ {k l} (p : Path-in Γ k l) (s : Xtot k)
      → evolve p s .snd ≡ 𝕎 .F₁ p (s .snd)
    evolve-snd nil        s = refl
    evolve-snd (cons e p) s = evolve-snd p (step e s)

  pr₂ : 𝕏 => 𝕎
  pr₂ .η k = snd
  pr₂ .is-natural k l p = funext (evolve-snd p)
```

## The fiber theorem

A total weight assignment $w_0$ determines a *global section* of
$\WW$ — the constant family — and the functioning $X^{w_0}$ sits
inside the total object $\XX$ as exactly the fiber of the projection
over that section. This is the chain case of the paper's
identification of $X^w$ with the fiber of $\mathrm{pr}_2$ over
$w : 1 \to \WW$.

```agda
  module _ (w₀ : ∀ {k l} (e : Γ.Edge k l) → ∣ W e ∣) where
    σ : ∀ k → Wleft k
    σ k a b e q = w₀ e

    σ-natural : ∀ {k l} (p : Path-in Γ k l) → 𝕎 .F₁ p (σ k) ≡ σ l
    σ-natural p = refl

    private
      ι-nat
        : ∀ {k l} (p : Path-in Γ k l) (x : ∣ X k ∣)
        → (transmit w₀ p x , σ l) ≡ evolve p (x , σ k)
      ι-nat nil        x = refl
      ι-nat (cons e p) x = ι-nat p (d e (w₀ e) x)

    ι : X^ w₀ => 𝕏
    ι .η k x = x , σ k
    ι .is-natural k l p = funext (ι-nat p)

    fiber-over-σ
      : ∀ k → ∣ X k ∣ ≃ fibre (pr₂ .η k) (σ k)
    fiber-over-σ k = Iso→Equiv
      ( (λ x → (x , σ k) , refl)
      , iso (λ ((x , w) , p) → x)
            (λ ((x , w) , p) → Σ-prop-path! (ap (x ,_) (sym p)))
            (λ x → refl))
```

## A network that runs

The two-layer chain with Boolean activities and Boolean weights,
where the weight decides whether the connection negates: the total
dynamical object literally computes.

```agda
private module Example where
  open Chain-dynamics 1
    (λ _ → el! Bool)
    (λ _ → el! Bool)
    (λ e w x → if w then not x else x)

  e01 : chain-graph 1 .Graph.Edge fzero (fsuc fzero)
  e01 = chain-edge refl

  step : Xtot fzero → Xtot (fsuc fzero)
  step = 𝕏 .Functor.F₁ (cons e01 nil)

  _ : step (true , λ _ _ _ _ → true) .fst ≡ false
  _ = refl

  _ : step (true , λ _ _ _ _ → false) .fst ≡ true
  _ = refl
```
