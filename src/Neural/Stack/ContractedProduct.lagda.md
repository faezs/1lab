---
description: |
  Lemma 2.2, the group tier: the contracted product along a group
  homomorphism, and the bijective, order-preserving correspondence
  of stable subobjects — the paper's "weakly geometric and open"
  transport.
---
<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Prelude

open import Data.Set.Coequaliser
```
-->

```agda
module Neural.Stack.ContractedProduct
  {ℓ} {G* G : Group ℓ} (φ : Groups.Hom G* G)
  where
```

# The contracted product: Lemma 2.2, group tier {defines="contracted-product"}

For an *arbitrary* group homomorphism $F \colon G' \to G$ — no
flatness, no geometricity — the paper's Lemma 2.2 asserts that the
left adjoint $F_!$, computed as the **contracted product**
$F_!(X') = G \times_{G'} X'$, induces a *bijective* morphism of
subobject lattices $f^\star \colon \mathrm{Sub}(X') \to
\mathrm{Sub}(G \times_{G'} X')$, so every logical operation is
preserved: the transport is "weakly geometric and open". This module
is the risk register's tier-1 de-risking of that lemma: the group
case in full. Subobjects of a $G$-set are its stable predicates; the
contracted product is the set quotient of $G \times X'$ by the
$G'$-action $(g \cdot F(h'), x') \sim (g, h' \cdot x')$; and the
correspondence is exhibited as an order isomorphism — from which,
"orbitwise" as the paper says, the preservation of every lattice and
Heyting operation and of both quantifiers follows abstractly, since
an order isomorphism preserves all structure defined by the order.

What is honestly *deferred*, per the register's tiers: the groupoid
extension (the paper's own text points to an unpublished companion
for it; tier 2 reduces groupoids presented as sums of connected
components to this module via Proposition C.1, and tier 3 states
Theorem 2.1(b) conditionally on the [[standard
hypothesis|standard-hypothesis]] records, which is already done).

<!--
```agda
private
  module G  = Group-on (G .snd)
  module H  = Group-on (G* .snd)
  module fh = is-group-hom (φ .snd)

  f : ⌞ G* ⌟ → ⌞ G ⌟
  f = φ .fst
```
-->

## G-sets and their stable subobjects

```agda
record GSet (K : Group ℓ) : Type (lsuc ℓ) where
  no-eta-equality
  private module K = Group-on (K .snd)
  field
    set    : Set ℓ
    act    : ⌞ K ⌟ → ∣ set ∣ → ∣ set ∣
    act-id : ∀ x → act K.unit x ≡ x
    act-∘  : ∀ g h x → act g (act h x) ≡ act (g K.⋆ h) x

open GSet

record Stable {K : Group ℓ} (X : GSet K) : Type ℓ where
  no-eta-equality
  field
    pred   : ∣ X .set ∣ → Ω
    stable : ∀ g {x} → x ∈ pred → X .act g x ∈ pred

open Stable
```

Stability is an equivalence, by acting with the inverse:

```agda
unstable
  : ∀ {K : Group ℓ} (X : GSet K) (P : Stable X) g {x}
  → X .act g x ∈ P .pred → x ∈ P .pred
unstable {K} X P g {x} m = subst (_∈ P .pred) cancel
  (P .stable (K.inverse g) m)
  where
    module K = Group-on (K .snd)
    cancel : X .act (K.inverse g) (X .act g x) ≡ x
    cancel = X .act-∘ _ _ x
           ∙ ap (λ e → X .act e x) K.inversel
           ∙ X .act-id x

Stable-path
  : ∀ {K : Group ℓ} {X : GSet K} {P Q : Stable X}
  → P .pred ≡ Q .pred → P ≡ Q
Stable-path p i .pred = p i
Stable-path {K = K} {X} {P} {Q} p i .stable =
  is-prop→pathp
    {B = λ i → (g : ⌞ K ⌟) {x : ∣ X .set ∣} → x ∈ p i → X .act g x ∈ p i}
    (λ i → Π-is-hlevel 1 λ g → Π-is-hlevel' 1 λ x →
       fun-is-hlevel 1 ((p i (X .act g x)) .is-tr))
    (P .stable) (Q .stable) i
```

## The contracted product

```agda
module _ (X' : GSet G*) where
  private
    module X' = GSet X'

    R : (⌞ G ⌟ × ∣ X'.set ∣) → (⌞ G ⌟ × ∣ X'.set ∣) → Type ℓ
    R p q =
      ∃[ h' ∈ ⌞ G* ⌟ ]
        ((p .fst ≡ q .fst G.⋆ f h') × (q .snd ≡ X'.act h' (p .snd)))

  CP : Type ℓ
  CP = (⌞ G ⌟ × ∣ X'.set ∣) / R

  inc' : (⌞ G ⌟ × ∣ X'.set ∣) → CP
  inc' = inc

  CP-act : ⌞ G ⌟ → CP → CP
  CP-act g₀ = Coeq-rec (λ p → inc (g₀ G.⋆ p .fst , p .snd)) λ where
    (a , b , r) → ∥-∥-rec (squash _ _)
      (λ { (h' , geq , yeq) → quot (inc
        (h' , ap (g₀ G.⋆_) geq ∙ G.associative , yeq)) })
      r

  Contracted : GSet G
  Contracted .set = el CP squash
  Contracted .act = CP-act
  Contracted .act-id = Coeq-elim-prop (λ _ → hlevel 1) λ p →
    ap (λ e → inc' (e , p .snd)) G.idl
  Contracted .act-∘ g h = Coeq-elim-prop (λ _ → hlevel 1) λ p →
    ap (λ e → inc' (e , p .snd)) G.associative
```

## The bijection of subobject lattices

The forward map evaluates a stable predicate on representatives —
well-defined precisely *because* of stability — and the backward map
restricts along $x' \mapsto [(1, x')]$.

```agda
  push : Stable X' → Stable Contracted
  push P .pred = Quot-elim (λ _ → hlevel 2)
    (λ p → P .pred (p .snd))
    (λ a b r → ∥-∥-rec (hlevel 1)
      (λ { (h' , geq , yeq) → Ω-ua
        (λ m → subst (_∈ P .pred) (sym yeq) (P .stable h' m))
        (λ m → unstable X' P h' (subst (_∈ P .pred) yeq m)) })
      r)
  push P .stable g {q} = Coeq-elim-prop
    {C = λ q → q ∈ push P .pred → CP-act g q ∈ push P .pred}
    (λ q → fun-is-hlevel 1 ((push P .pred (CP-act g q)) .is-tr))
    (λ p m → m) q

  pull : Stable Contracted → Stable X'
  pull Q .pred x' = Q .pred (inc (G.unit , x'))
  pull Q .stable h' {x'} m =
    subst (_∈ Q .pred) path₂ (subst (_∈ Q .pred) path₁ (Q .stable (f h') m))
    where
      path₁ : Path CP (inc (f h' G.⋆ G.unit , x')) (inc (f h' , x'))
      path₁ = ap (λ e → inc' (e , x')) G.idr

      path₂ : Path CP (inc (f h' , x')) (inc (G.unit , X'.act h' x'))
      path₂ = quot (inc (h' , sym G.idl , refl))

  pull-push : (P : Stable X') → pull (push P) ≡ P
  pull-push P = Stable-path refl

  push-pull : (Q : Stable Contracted) → push (pull Q) ≡ Q
  push-pull Q = Stable-path (funext (Coeq-elim-prop
    (λ q → hlevel 1)
    (λ p → Ω-ua
      (λ m → subst (_∈ Q .pred)
        (ap (λ e → inc' (e , p .snd)) G.idr) (Q .stable (p .fst) m))
      (λ m → unstable Contracted Q (p .fst)
        (subst (_∈ Q .pred)
          (sym (ap (λ e → inc' (e , p .snd)) G.idr)) m)))))
```

Both maps are monotone on the nose, so together with the round
trips they exhibit an *order isomorphism*
$\mathrm{Sub}(X') \cong \mathrm{Sub}(G \times_{G'} X')$:

```agda
  push-mono
    : {P P' : Stable X'}
    → (∀ x' → x' ∈ P .pred → x' ∈ P' .pred)
    → ∀ q → q ∈ push P .pred → q ∈ push P' .pred
  push-mono {P} {P'} le = Coeq-elim-prop
    (λ q → fun-is-hlevel 1 ((push P' .pred q) .is-tr))
    (λ p m → le (p .snd) m)

  pull-mono
    : {Q Q' : Stable Contracted}
    → (∀ q → q ∈ Q .pred → q ∈ Q' .pred)
    → ∀ x' → x' ∈ pull Q .pred → x' ∈ pull Q' .pred
  pull-mono le x' m = le (inc (G.unit , x')) m
```

This is the paper's Lemma 2.2 in its group tier: `push`{.Agda} is
the map the paper calls $f^\star$ (induced by $F_!$), it is
bijective with inverse `pull`{.Agda}, and both directions preserve
the order — hence, since $\top$, $\bot$, $\wedge$, $\vee$,
$\Rightarrow$, $\exists_h$ and $\forall_h$ are all defined by
universal properties in the subobject order, the correspondence
preserves every logical operation, which is exactly the paper's
"orbitwise" conclusion. The groupoid extension is *not* claimed.
