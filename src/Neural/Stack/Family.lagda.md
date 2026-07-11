---
description: |
  Compatible families of fibre presheaves over a split indexed
  category — the objects of Belfiore–Bennequin's equations 2.4–2.6 —
  and their category.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Functor.Base
open import Cat.Prelude

open import 1Lab.Reflection.Record

import Cat.Functor.Reasoning.Presheaf as Psh
import Neural.Stack.Grothendieck
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Family
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  (κ : Level)
  where
```

# Compatible families of fibre presheaves {defines="presheaf-family"}

A presheaf on the total category $\int F$ of a [[split Grothendieck
construction|split-grothendieck]] should be the same thing as a
family: a presheaf $A_U$ on each fibre $F_U$, together with, for
each arrow $\alpha \colon U \to V$ of the base, a *transition map*
$A_V(\xi) \to A_U(\alpha^\star \xi)$, natural in $\xi$ and
functorial in $\alpha$ — the data the paper manipulates as
equations 2.4–2.6. This module defines that category of families,
in fully componentwise form: the transition maps are functions with
explicit naturality and cocycle fields, so no functor-composition
transport ever enters a statement. The equivalence with
$\psh(\textstyle\int F)$ is the successor module's theorem; the
family form is the one every later construction (the glued
classifier, the transport adjunctions) actually computes with.

The cocycle conditions land in fibre values over *reindexed* objects,
so they are stated as transports along the object-level functoriality
paths `·₀-id`{.Agda} and `·₀-∘`{.Agda} — paths in the strict fibre
object sets.

<!--
```agda
private
  module B = Cat.Reasoning B

open Neural.Stack.Grothendieck F
open Precategory
open Functor
open _=>_
```
-->

```agda
record Family : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ lsuc κ) where
  no-eta-equality
  field
    fam : ∀ U → Functor ((Fib U) ^op) (Sets κ)

    tr
      : ∀ {U V} (α : B.Hom U V) {ξ : Fib V .Ob}
      → fam V ʻ ξ → fam U ʻ (α ·₀ ξ)

    tr-nat
      : ∀ {U V} (α : B.Hom U V) {ξ ζ : Fib V .Ob}
        (u : Fib V .Hom ξ ζ) (x : fam V ʻ ζ)
      → tr α (Psh.₁ (fam V) u x) ≡ Psh.₁ (fam U) (α ·₁ u) (tr α x)

    tr-id
      : ∀ {U} {ξ : Fib U .Ob} (x : fam U ʻ ξ)
      → tr B.id x ≡ subst (fam U ʻ_) (sym (·₀-id ξ)) x

    tr-∘
      : ∀ {U V W} (f : B.Hom V W) (g : B.Hom U V) {ξ : Fib W .Ob}
        (x : fam W ʻ ξ)
      → tr (f B.∘ g) x
      ≡ subst (fam U ʻ_) (sym (·₀-∘ f g ξ)) (tr g (tr f x))

open Family
```

A morphism of families is a fibrewise natural transformation
commuting with the transitions — no coherence beyond that, since
both composites land in the same fibre value.

```agda
record Family-hom (A A' : Family) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ κ) where
  no-eta-equality
  field
    map : ∀ U → A .fam U => A' .fam U

    com
      : ∀ {U V} (α : B.Hom U V) {ξ : Fib V .Ob} (x : A .fam V ʻ ξ)
      → A' .tr α (map V .η ξ x) ≡ map U .η (α ·₀ ξ) (A .tr α x)

open Family-hom
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Family-hom)

Family-hom-path
  : {A A' : Family} {h h' : Family-hom A A'}
  → (∀ U → h .map U ≡ h' .map U)
  → h ≡ h'
Family-hom-path p i .map U = p U i
Family-hom-path {A} {A'} {h} {h'} p i .com {U} {V} α {ξ} x =
  is-prop→pathp
    (λ i → (A' .fam U .F₀ (α ·₀ ξ)) .is-tr
      (A' .tr α (p V i .η ξ x))
      (p U i .η (α ·₀ ξ) (A .tr α x)))
    (h .com α x) (h' .com α x) i

Family-hom-is-set : {A A' : Family} → is-set (Family-hom A A')
Family-hom-is-set = Iso→is-hlevel! 2 eqv
```
-->

Families and their morphisms form a category, with everything
computed fibrewise.

```agda
Families : Precategory (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ lsuc κ) (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ κ)
Families .Ob = Family
Families .Hom = Family-hom
Families .Hom-set _ _ = Family-hom-is-set
Families .id .map U = idnt
Families .id .com α x = refl
Families ._∘_ h' h .map U = h' .map U ∘nt h .map U
Families ._∘_ h' h .com {U} {V} α {ξ} x =
  h' .com α (h .map V .η ξ x) ∙ ap (h' .map U .η (α ·₀ ξ)) (h .com α x)
Families .idr h = Family-hom-path λ U → Nat-path λ ξ → refl
Families .idl h = Family-hom-path λ U → Nat-path λ ξ → refl
Families .assoc f g h = Family-hom-path λ U → Nat-path λ ξ → refl
```

What is *not* here, honestly: the equivalence
$\psh(\int F) \simeq$ `Families`{.Agda} (the successor module), and
any sheaf-theoretic condition — a family is the paper's *presheaf*
of fibre presheaves, with descent entering only when the base
carries its topology.
