---
description: |
  Openness of the stack transports, by the adjoint characterization:
  equations 2.13–2.16, the trivial-topology content of Lemma 2.3,
  and Proposition 2.2 — the transport dictionary of the predicate
  calculus, operation by operation.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Diagram.Sieve
open import Cat.Prelude

open import Data.Sum.Base

open import Neural.Order.Adjunction

open import Order.Base

import Physics.SmoothWorld.Forcing
import Neural.Stack.Grothendieck
import Neural.Stack.Adjunction
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Open
  {ℓ} {B : Precategory ℓ ℓ}
  (F : Functor (B ^op) (Strict-cats ℓ ℓ))
  where
```

# Open transports: the dictionary of equations 2.13–2.16 {defines="open-transport"}

The paper's §2.2 asks when the feed-forward transport
$\Omega_\alpha = \lambda_\alpha$ carries not just the lattice
structure but the whole predicate calculus — and answers with Mac
Lane–Moerdijk's characterization: the morphism is *open* exactly
when $\lambda_\alpha$ admits a left adjoint $\mu_\alpha$ of posets.
Following the roadmap, this development takes the characterization
as the *definition*, together with the Frobenius law that the
internal formulation carries silently; equations 2.15–2.16 are then
the unit and counit, and Proposition 2.2's dictionary is proved
operation by operation. The division of labour is exactly the
paper's: preservation of $\top$, $\bot$ and $\vee$ is unconditional
(the direct image has a right adjoint by [[Lemma
2.4|classifier-adjunction]]), preservation of $\wedge$ needs the
left adjoint, and preservation of $\Rightarrow$ and $\neg$ needs
Frobenius.

Of Lemma 2.3's three site conditions, at the trivial topology of
our presheaf fibres: condition (i) (lifting of coverings) is vacuous
since only maximal sieves cover; condition (ii) (preservation of
covers) is precisely `Ω-pres-⊤`{.Agda} below; and condition (iii)
(surjectivity of the sliced functors) is the mere-lift hypothesis
`has-lifts`{.Agda ident=has-lifts} of Lemma 2.4.

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

open Neural.Stack.Grothendieck F
open Neural.Stack.Adjunction F

open Precategory
open Functor
```
-->

The missing corner of the fibrewise sieve lattice, and membership
transport along sieve equalities:

```agda
⊥s : ∀ {W : B.Ob} {ξ : Fib W .Ob} → Sieve (Fib W) ξ
⊥s .arrows _ = ⊥Ω
⊥s .closed p _ = p

_∨s_
  : ∀ {W : B.Ob} {ξ : Fib W .Ob}
  → Sieve (Fib W) ξ → Sieve (Fib W) ξ → Sieve (Fib W) ξ
(S ∨s T) .arrows f = S .arrows f ∨Ω T .arrows f
(S ∨s T) .closed = rec! λ where
  (inl m) g → inc (inl (S .closed m g))
  (inr m) g → inc (inr (T .closed m g))

private
  sub-⊆
    : ∀ {W : B.Ob} {ξ : Fib W .Ob} {X Y : Sieve (Fib W) ξ}
    → X ≡ Y → X ⊆ Y
  sub-⊆ e h m = subst (λ T → h ∈ T) e m
```

## Openness, by the adjoint characterization

```agda
record is-open {U V : B.Ob} (α : B.Hom U V) : Type ℓ where
  no-eta-equality
  field
    μ : ∀ {ξ' : Fib V .Ob}
      → Monotone (fibre-sieves U (α ·₀ ξ')) (fibre-sieves V ξ')
    μ⊣Ω : ∀ {ξ' : Fib V .Ob} → μ {ξ'} ⊣ₚ Ω-mono α {ξ'}
    frobenius
      : ∀ {ξ' : Fib V .Ob} (T : Sieve (Fib U) (α ·₀ ξ'))
        (S : Sieve (Fib V) ξ')
      → μ .hom (T ∩S Ω[_] α S) ≡ (μ .hom T ∩S S)

  eq-2·15
    : ∀ {ξ' : Fib V .Ob} (S : Sieve (Fib V) ξ')
    → μ .hom (Ω[_] α S) ⊆ S
  eq-2·15 S = μ⊣Ω ._⊣ₚ_.counit

  eq-2·16
    : ∀ {ξ' : Fib V .Ob} (T : Sieve (Fib U) (α ·₀ ξ'))
    → T ⊆ Ω[_] α (μ .hom T)
  eq-2·16 T = μ⊣Ω ._⊣ₚ_.unit
```

## The unconditional half of the dictionary

```agda
module _ {U V : B.Ob} (α : B.Hom U V) {ξ' : Fib V .Ob} where
  Ω-pres-⊤ : Ω[_] α {ξ'} maximal' ≡ maximal'
  Ω-pres-⊤ = ext λ v → Ω-ua (λ _ → tt) λ _ → inc
    ( ξ' , Fib V .id , v , tt
    , sym ( ap (λ t → Fib U ._∘_ t v) (F.₁ α .F-id)
          ∙ Fib U .idl v))

  Ω-pres-⊥ : Ω[_] α {ξ'} ⊥s ≡ ⊥s
  Ω-pres-⊥ = ext λ v → Ω-ua
    (rec! λ η' u' w mem eq → absurd mem)
    (λ m → absurd m)

  Ω-pres-∨
    : (S S' : Sieve (Fib V) ξ')
    → Ω[_] α (S ∨s S') ≡ (Ω[_] α S ∨s Ω[_] α S')
  Ω-pres-∨ S S' = ext λ v → Ω-ua
    (rec! λ η' u' w mem eq → case mem of λ where
      (inl m) → inc (inl (inc (η' , u' , w , m , eq)))
      (inr m) → inc (inr (inc (η' , u' , w , m , eq))))
    (rec! λ where
      (inl m) → Ω-mono α .pres-≤ {x = S} {y = S ∨s S'} (λ h n → inc (inl n)) v m
      (inr m) → Ω-mono α .pres-≤ {x = S'} {y = S ∨s S'} (λ h n → inc (inr n)) v m)
```

## The open half: Proposition 2.2

```agda
module _ {U V : B.Ob} (α : B.Hom U V) (o : is-open α) {ξ' : Fib V .Ob} where
  private
    module o = is-open o
    module FU = Physics.SmoothWorld.Forcing (Fib U)
    module FV = Physics.SmoothWorld.Forcing (Fib V)

  Ω-pres-∧
    : (S S' : Sieve (Fib V) ξ')
    → Ω[_] α (S ∩S S') ≡ (Ω[_] α S ∩S Ω[_] α S')
  Ω-pres-∧ S S' = ext λ v → Ω-ua
    (λ m → Ω-mono α .pres-≤ {x = S ∩S S'} {y = S} (λ h n → n .fst) v m
         , Ω-mono α .pres-≤ {x = S ∩S S'} {y = S'} (λ h n → n .snd) v m)
    (λ m → _⊣ₚ_.adjunct-l (o.μ⊣Ω)
      {x = Ω[_] α S ∩S Ω[_] α S'} {y = S ∩S S'}
      (λ h n → o.μ⊣Ω ._⊣ₚ_.counit {S} h
                 (o.μ .pres-≤ {x = Ω[_] α S ∩S Ω[_] α S'} {y = Ω[_] α S}
                   (λ h' n' → n' .fst) h n)
             , o.μ⊣Ω ._⊣ₚ_.counit {S'} h
                 (o.μ .pres-≤ {x = Ω[_] α S ∩S Ω[_] α S'} {y = Ω[_] α S'}
                   (λ h' n' → n' .snd) h n))
      v m)

  Ω-pres-⇒
    : (S S' : Sieve (Fib V) ξ')
    → Ω[_] α (S FV.⇒ᵢ S') ≡ (Ω[_] α S FU.⇒ᵢ Ω[_] α S')
  Ω-pres-⇒ S S' = ext λ v → Ω-ua
    (λ m → FU.⇒ᵢ-curry (Ω[_] α (S FV.⇒ᵢ S')) (Ω[_] α S) (Ω[_] α S')
      (λ h n → Ω-mono α .pres-≤
        {x = (S FV.⇒ᵢ S') ∩S S} {y = S'}
        (FV.⇒ᵢ-uncurry (S FV.⇒ᵢ S') S S' (λ _ k → k)) h
        (sub-⊆ (sym (Ω-pres-∧ (S FV.⇒ᵢ S') S)) h n))
      v m)
    (λ m → _⊣ₚ_.adjunct-l (o.μ⊣Ω)
      {x = Ω[_] α S FU.⇒ᵢ Ω[_] α S'} {y = S FV.⇒ᵢ S'}
      (FV.⇒ᵢ-curry (o.μ .hom (Ω[_] α S FU.⇒ᵢ Ω[_] α S')) S S'
        (λ h n → o.μ⊣Ω ._⊣ₚ_.counit {S'} h
          (o.μ .pres-≤
            {x = (Ω[_] α S FU.⇒ᵢ Ω[_] α S') ∩S Ω[_] α S} {y = Ω[_] α S'}
            (FU.⇒ᵢ-uncurry (Ω[_] α S FU.⇒ᵢ Ω[_] α S') (Ω[_] α S)
              (Ω[_] α S') (λ _ k → k))
            h
            (sub-⊆ (sym (o.frobenius (Ω[_] α S FU.⇒ᵢ Ω[_] α S') S)) h n))))
      v m)

  Ω-pres-¬
    : (S : Sieve (Fib V) ξ')
    → Ω[_] α (S FV.⇒ᵢ ⊥s) ≡ (Ω[_] α S FU.⇒ᵢ ⊥s)
  Ω-pres-¬ S = Ω-pres-⇒ S ⊥s ∙ ap (Ω[_] α S FU.⇒ᵢ_) (Ω-pres-⊥ α)
```

Proposition 2.2, assembled: for an open transport, $\Omega_\alpha$
commutes with every operation of the predicate calculus —
`Ω-pres-⊤`{.Agda}, `Ω-pres-⊥`{.Agda}, `Ω-pres-∨`{.Agda} without
hypothesis, `Ω-pres-∧`{.Agda}, `Ω-pres-⇒`{.Agda}, `Ω-pres-¬`{.Agda}
under openness — so any theory at the layer $U'$ can be read and
translated at the deeper layer $U$, clause by clause. What is
honestly *not* here: the quantifier clauses of the dictionary (the
paper's inequality 2.14 and its saturation under openness), which
quantify along fibre morphisms and belong with the hyperdoctrine
layer where those quantifiers live; and any *instance* of
`is-open`{.Agda} — the Boolean/complemented route through
[[Lemma 2.1|complemented-boolean]] and the group-case Lemma 2.2
produce them, in their own modules.
