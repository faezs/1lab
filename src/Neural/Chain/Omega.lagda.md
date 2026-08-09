---
description: |
  The chain site is thin — the free category on a chain graph is the
  finite linear order — and its sieves are exactly the up-closed
  families of propositions on the deeper layers, the honest
  constructive form of Belfiore–Bennequin's threshold description of
  the subobject classifier.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Diagram.Sieve
open import Cat.Prelude

open import Data.Fin.Base
open import Data.Nat.Properties

open import Neural.Chain

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Chain.Omega where
```

# The chain site is thin {defines="chain-thin"}

For the [[chain network|chain-network]], the paper's Proposition 1.1
specialises to: the free category on the chain graph *is* the finite
linear order $\{0 \le 1 \le \dots \le n\}$. We prove this by showing
that paths between two layers form a proposition, equivalent to the
ordering of the layer indices. Together with the computation of
sieves below, this justifies the paper's picture of the subobject
classifier of a chain topos, in its honest constructive form.

<!--
```agda
module _ (n : Nat) where
  private
    Γ = chain-graph n
    module Γ = Graph Γ
```
-->

First, existence: from an inequality of layer indices we manufacture a
path, one edge at a time, recursing on the *difference* of the
indices.

```agda
  private
    ≤-+l : ∀ d x → x Nat.≤ d Nat.+ x
    ≤-+l zero    x = Nat.≤-refl
    ≤-+l (suc d) x = Nat.≤-sucr (≤-+l d x)

    difference : ∀ a b → a Nat.≤ b → Σ[ d ∈ Nat ] (d Nat.+ a ≡ b)
    difference zero    b       p = b , +-zeror b
    difference (suc a) zero    p = absurd (Nat.¬suc≤0 p)
    difference (suc a) (suc b) p =
      let (d , eq) = difference a b (Nat.≤-peel p)
      in d , +-sucr d a ∙ ap suc eq

    fin-suc
      : {k l : Fin (suc n)} → suc (k .lower) Nat.≤ l .lower
      → Fin (suc n)
    fin-suc {k} {l} le = fin (suc (k .lower))
      ⦃ Nat.s≤s (Nat.≤-trans le (Nat.≤-peel (Fin.bounded l))) ⦄

    build
      : ∀ d {k l : Fin (suc n)}
      → d Nat.+ k .lower ≡ l .lower → Path-in Γ k l
    build zero    {k} {l} eq = subst (Path-in Γ k) (fin-ap eq) nil
    build (suc d) {k} {l} eq =
      let
        le : suc (k .lower) Nat.≤ l .lower
        le = subst (suc (k .lower) Nat.≤_) eq (Nat.s≤s (≤-+l d (k .lower)))
      in cons (chain-edge refl) (build d {fin-suc {k} {l} le} {l}
           (+-sucr d (k .lower) ∙ eq))

  chain-path
    : {k l : Fin (suc n)} → k .lower Nat.≤ l .lower
    → Path-in Γ k l
  chain-path {k} {l} le =
    let (d , eq) = difference (k .lower) (l .lower) le
    in build d eq
```

Uniqueness is by simultaneous induction on a pair of paths whose
start points are joined by an identification (working over such an
identification is what lets the induction go through without axiom
K). A nonempty path can not be parallel to an empty one, by
`chain-no-loop`{.Agda}; and two nonempty paths must take the *same*
first edge — the intermediate layers agree because both are the
successor of the source — after which we recurse. We phrase the
induction as the construction of a *code* in the sense of
`path-codep`{.Agda}, which `path-encode`{.Agda} then turns into an
identification.

```agda
  private
    chain-code
      : ∀ {k k' l} (kk : k ≡ k')
      → (p : Path-in Γ k l) (q : Path-in Γ k' l)
      → path-codep Γ (λ i → kk i) p q
    chain-code kk nil nil = lift tt
    chain-code kk nil (cons f q) = absurd
      (chain-no-loop n f (subst (λ m → Path-in Γ _ m) kk q))
    chain-code kk (cons e p) nil = absurd
      (chain-no-loop n (subst (λ m → Chain-edge n m _) kk e) p)
    chain-code {k} {k'} kk (cons {b = b} e p) (cons {b = b'} f q) =
      bs , is-prop→pathp (λ i → hlevel 1) e f , chain-code bs p q
      where
        bs : b ≡ b'
        bs = fin-ap
          (sym (e .lowers) ∙ ap (λ m → suc (m .lower)) kk ∙ f .lowers)

  chain-path-is-prop
    : {k l : Fin (suc n)} → is-prop (Path-in Γ k l)
  chain-path-is-prop p q =
    path-encode Γ _ p q (chain-code refl p q)
```

The chain site is therefore *thin*: its hom-sets are equivalent to
the propositional ordering of layers. This is the chain instance of
the paper's Proposition 1.1 — the site reduces to a poset.

```agda
  chain-thin
    : {k l : Fin (suc n)}
    → Path-in Γ k l ≃ (k .lower Nat.≤ l .lower)
  chain-thin = prop-ext chain-path-is-prop Nat.≤-is-prop
    (path-≤ n) chain-path
```

# Sieves on a chain {defines="chain-sieve"}

The subobject classifier of the presheaf topos on the chain site has,
at layer $k$, the set of [[sieves]] on $k$. The paper describes these
as increasing sequences $(\emptyset, \dots, \emptyset, \star, \dots,
\star)$ — thresholds along the deeper layers. Constructively, the
honest statement is: a sieve on $k$ is exactly an *up-closed family
of propositions* on the layers at or beyond $k$. The paper's
threshold picture is the special case where every proposition in the
family is decidable; over a one-layer chain, for instance, sieves
form $\Omega$ itself, not the two-element set.

Both directions of the translation below are essentially definitional
thanks to two facts: paths in the chain are propositional
(`chain-path-is-prop`{.Agda}), and 1lab's ordering on naturals is
definitionally proof-irrelevant, so up-closure re-indexed along any
two proofs of the same inequality agrees on the nose.

```agda
  UpSet : Fin (suc n) → Type
  UpSet k =
    Σ[ S ∈ ((v : Fin (suc n)) → k .lower Nat.≤ v .lower → Ω) ]
      (∀ v w (kv : k .lower Nat.≤ v .lower) (vw : v .lower Nat.≤ w .lower)
       → ∣ S v kv ∣ → ∣ S w (Nat.≤-trans kv vw) ∣)

  to-upset : ∀ {k} → Sieve (chain-site n) k → UpSet k
  to-upset {k} S .fst v kv = S .arrows (chain-path {k} {v} kv)
  to-upset {k} S .snd v w kv vw hv = subst (λ h → ∣ S .arrows h ∣)
    (chain-path-is-prop (chain-path {k} {v} kv ++ chain-path {v} {w} vw)
      (chain-path {k} {w} (Nat.≤-trans kv vw)))
    (S .closed hv (chain-path {v} {w} vw))

  from-upset : ∀ {k} → UpSet k → Sieve (chain-site n) k
  from-upset (S , up) .arrows {v} p = S v (path-≤ n p)
  from-upset (S , up) .closed {y} {z} {f} hf g =
    up z y (path-≤ n f) (path-≤ n g) hf

  chain-sieve≃upset : ∀ {k} → Sieve (chain-site n) k ≃ UpSet k
  chain-sieve≃upset {k} = Iso→Equiv
    ( to-upset
    , iso from-upset
        (λ (S , up) → Σ-prop-path
          (λ S' → Π-is-hlevel 1 λ v → Π-is-hlevel 1 λ w →
                  Π-is-hlevel 1 λ kv → Π-is-hlevel 1 λ vw →
                  fun-is-hlevel 1 (S' w (Nat.≤-trans kv vw) .is-tr))
          refl)
        (λ S → ext λ {v} p →
          ap (λ h → S .arrows h)
            (chain-path-is-prop (chain-path {k} {v} (path-≤ n p)) p)))
```
