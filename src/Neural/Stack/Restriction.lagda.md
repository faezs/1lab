---
description: |
  The fibrewise restriction of a presheaf on the total category to a
  compatible family — the quasi-inverse direction of equations
  2.4–2.6.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Neural.Stack.Transport

import Cat.Functor.Reasoning.Presheaf as Psh
import Neural.Stack.Grothendieck
import Neural.Stack.Family
import Neural.Stack.Fibre
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Restriction
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  (κ : Level)
  where
```

# Restricting a total presheaf to its fibres {defines="presheaf-to-family"}

A presheaf $X$ on the total category $\int F$ restricts along the
[[fibre inclusions|fibre-inclusion]] to a presheaf on each fibre,
and along the cartesian arrows $(\alpha, \mathrm{id})$ to the
transition maps of a [[compatible family|presheaf-family]] — the
quasi-inverse direction of the paper's equations 2.4–2.6. The
cocycle proofs have one genuinely cubical subtlety: the cartesian
arrow over the identity and the identity of $\int F$ have *different
domains* ($(U, \mathrm{id}^\star\xi)$ versus $(U,\xi)$), so they are
compared not by an equation but by a `PathP`{.Agda} over the
strictness path of fibre objects, converted by `from-pathp`{.Agda}
into the substitution equation the presheaf can eat.

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

open Neural.Stack.Grothendieck F
open Neural.Stack.Family F κ
open Neural.Stack.Fibre F

open Precategory
open Family-hom
open Functor
open Family
open ∫Hom
open _=>_
```
-->

```agda
private
  lemX-dom
    : (X : Functor ((∫F) ^op) (Sets κ)) {U V : B.Ob}
      {ζ ζ' : Fib U .Ob} {ξ : Fib V .Ob}
      (p : ζ ≡ ζ') (m : ∫F .Hom (U , ζ) (V , ξ)) (x : X ʻ (V , ξ))
    → X .F₁ (subst (λ z → ∫F .Hom (U , z) (V , ξ)) p m) x
    ≡ subst (λ z → X ʻ (U , z)) p (X .F₁ m x)
  lemX-dom X {U} {V} {ζ} {ζ'} {ξ} p m x = J
    (λ ζ' p → X .F₁ (subst (λ z → ∫F .Hom (U , z) (V , ξ)) p m) x
            ≡ subst (λ z → X ʻ (U , z)) p (X .F₁ m x))
    (ap (λ m' → X .F₁ m' x) (transport-refl m) ∙ sym (transport-refl _))
    p

  subst-dom-cod-id
    : ∀ {oc ℓc} (C : Precategory oc ℓc) {x y : C .Ob} (p : x ≡ y)
    → subst (λ z → C .Hom z y) p (subst (C .Hom x) p (C .id)) ≡ C .id
  subst-dom-cod-id C {x} p = J
    (λ y p → subst (λ z → C .Hom z y) p (subst (C .Hom x) p (C .id))
           ≡ C .id)
    (transport-refl _ ∙ transport-refl _)
    p

  dom-sub-id
    : ∀ {oc ℓc} (C : Precategory oc ℓc) {x y : C .Ob} (p : x ≡ y)
    → subst (λ z → C .Hom z x) p (C .id)
    ≡ subst (C .Hom y) (sym p) (C .id)
  dom-sub-id C {x} p = J
    (λ y p → subst (λ z → C .Hom z x) p (C .id)
           ≡ subst (C .Hom y) (sym p) (C .id))
    (transport-refl _ ∙ sym (transport-refl _))
    p
```

## The restriction

```agda
Res₀ : Functor ((∫F) ^op) (Sets κ) → Family
Res₀ X .fam U = X F∘ Functor.op (ι U)
Res₀ X .tr {U} {V} α {ξ} x = X .F₁ (∫hom α (Fib U .id)) x
Res₀ X .tr-nat {U} {V} α {ξ} {ζ} u x =
     sym (Psh.F-∘ X (∫hom α (Fib U .id)) (ι V .F₁ u))
  ∙  ap (λ m → X .F₁ m x) keynat
  ∙  Psh.F-∘ X (ι U .F₁ (α ·₁ u)) (∫hom α (Fib U .id))
  where
    S₀  = sym (·₀-∘ B.id α ζ)
    S₆ₐ = ap (F.₁ α .F₀) (sym (·₀-id ζ))
    AP  = ap (_·₀ ζ) (B.idl α ∙ sym (B.idr α))
    PL  = S₆ₐ ∙ (S₀ ∙ AP)
    PR  = sym (·₀-id (α ·₀ ζ)) ∙ sym (·₀-∘ α B.id ζ)

    inner
      : Fib U ._∘_ (α ·₁ subst (Fib V .Hom ξ) (sym (·₀-id ζ)) u) (Fib U .id)
      ≡ subst (Fib U .Hom (α ·₀ ξ)) S₆ₐ (α ·₁ u)
    inner =
         ap (λ t → Fib U ._∘_ t (Fib U .id))
           (F₁-sub (F.₁ α) (sym (·₀-id ζ)) u)
      ∙  sub-∘ˡ (Fib U) S₆ₐ (α ·₁ u) (Fib U .id)
      ∙  ap (subst (Fib U .Hom (α ·₀ ξ)) S₆ₐ) (Fib U .idr (α ·₁ u))

    keynat : ∫F ._∘_ (ι V .F₁ u) (∫hom α (Fib U .id))
           ≡ ∫F ._∘_ (∫hom α (Fib U .id)) (ι U .F₁ (α ·₁ u))
    keynat = ∫Hom-path Grothendieck (B.idl α ∙ sym (B.idr α)) $ to-pathp $
         sym (subst-∙ (Fib U .Hom (α ·₀ ξ)) S₀ AP _)
      ∙  ap (subst (Fib U .Hom (α ·₀ ξ)) (S₀ ∙ AP)) inner
      ∙  sym (subst-∙ (Fib U .Hom (α ·₀ ξ)) S₆ₐ (S₀ ∙ AP) (α ·₁ u))
      ∙  sub-parallel (Fib U) (Fib-set U) PL PR (α ·₁ u)
      ∙  sym
           ( ap (subst (Fib U .Hom (α ·₀ ξ)) (sym (·₀-∘ α B.id ζ)))
               ( comp-key F.F-id (Fib U .id) (α ·₁ u)
               ∙ ap (subst (Fib U .Hom (α ·₀ ξ)) (sym (·₀-id (α ·₀ ζ))))
                   (Fib U .idl (α ·₁ u)))
           ∙ sym (subst-∙ (Fib U .Hom (α ·₀ ξ))
               (sym (·₀-id (α ·₀ ζ))) (sym (·₀-∘ α B.id ζ)) (α ·₁ u)))
Res₀ X .tr-id {U} {ξ} x =
     ap (λ m → X .F₁ m x) (sym (from-pathp keyid))
  ∙  lemX-dom X (sym (·₀-id ξ)) (∫F .id) x
  ∙  ap (subst (λ z → X ʻ (U , z)) (sym (·₀-id ξ))) (Psh.F-id X)
  where
    keyid : PathP (λ i → ∫F .Hom (U , sym (·₀-id ξ) i) (U , ξ))
              (∫F .id) (∫hom B.id (Fib U .id))
    keyid = ∫Hom-pathp Grothendieck (ap (U ,_) (sym (·₀-id ξ))) refl refl
              (to-pathp (subst-dom-cod-id (Fib U) (sym (·₀-id ξ))))
Res₀ X .tr-∘ {U} {V} {W} f g {ξ} x = sym $
     ap (subst (λ z → X ʻ (U , z)) (sym p∘))
       (sym (Psh.F-∘ X (∫hom g (Fib U .id)) (∫hom f (Fib V .id))))
  ∙  ap (subst (λ z → X ʻ (U , z)) (sym p∘))
       ( ap (λ m → X .F₁ m x) (sym (from-pathp key∘))
       ∙ lemX-dom X p∘ (∫hom (f B.∘ g) (Fib U .id)) x)
  ∙  sym (subst-∙ (λ z → X ʻ (U , z)) p∘ (sym p∘)
       (X .F₁ (∫hom (f B.∘ g) (Fib U .id)) x))
  ∙  ap (λ e → subst (λ z → X ʻ (U , z)) e
       (X .F₁ (∫hom (f B.∘ g) (Fib U .id)) x)) (∙-invr p∘)
  ∙  transport-refl _
  where
    p∘ = ·₀-∘ f g ξ

    key∘ : PathP (λ i → ∫F .Hom (U , p∘ i) (W , ξ))
             (∫hom (f B.∘ g) (Fib U .id))
             (∫F ._∘_ (∫hom f (Fib V .id)) (∫hom g (Fib U .id)))
    key∘ = ∫Hom-pathp Grothendieck (ap (U ,_) p∘) refl refl $ to-pathp $
         dom-sub-id (Fib U) p∘
      ∙  sym (ap (subst (Fib U .Hom (g ·₀ (f ·₀ ξ))) (sym p∘))
           ( ap (λ t → Fib U ._∘_ t (Fib U .id)) (F.₁ g .F-id)
           ∙ Fib U .idl (Fib U .id)))
```

The morphism part is pure naturality: a map of presheaves on
$\int F$ restricts to fibrewise maps, and its naturality at the
cartesian arrows *is* the compatibility square.

```agda
Res₁
  : {X Y : Functor ((∫F) ^op) (Sets κ)}
  → X => Y → Family-hom (Res₀ X) (Res₀ Y)
Res₁ h .map U .η ξ = h .η (U , ξ)
Res₁ h .map U .is-natural ξ ζ u = h .is-natural (U , ξ) (U , ζ) (ι U .F₁ u)
Res₁ h .com {U} {V} α {ξ} x =
  sym (happly (h .is-natural (V , ξ) (U , α ·₀ ξ) (∫hom α (Fib U .id))) x)

Res : Functor (PSh κ ∫F) Families
Res .F₀ = Res₀
Res .F₁ = Res₁
Res .F-id = Family-hom-path λ U → Nat-path λ ξ → refl
Res .F-∘ h' h = Family-hom-path λ U → Nat-path λ ξ → refl
```

What is *not* here: the unit and counit exhibiting `Res`{.Agda} and
`Tot`{.Agda ident=Tot} as a quasi-inverse pair — the equivalence
itself is the successor milestone, split into its own files per the
memory discipline.
