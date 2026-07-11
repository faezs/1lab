---
description: |
  The transport toolkit for split indexed categories: five path
  lemmas that push substitutions to the outside of categorical
  terms, plus the parallel-path collapse over strict object sets.
---
<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Neural.Stack.Transport where
```

# The transport toolkit {defines="stack-transport-toolkit"}

Every construction on a [[split indexed category|split-grothendieck]]
transports fibre morphisms along the object-level functoriality paths
of the indexing functor. These five lemmas — each a one-line path
induction — normalize any such term to a single outer substitution,
which the strictness of the fibres then collapses. They are stated
for arbitrary precategories, with the category arguments *explicit*:
`C .Hom` is not an injective head, so implicit versions never infer.

<!--
```agda
open Precategory
open Functor
```
-->

```agda
sub-∘ˡ
  : ∀ {oc ℓc} (C : Precategory oc ℓc) {w x y z : C .Ob}
  → (p : y ≡ z) (h : C .Hom x y) (g : C .Hom w x)
  → C ._∘_ (subst (C .Hom x) p h) g
  ≡ subst (C .Hom w) p (C ._∘_ h g)
sub-∘ˡ C {w} {x} p h g = J
  (λ z p → C ._∘_ (subst (C .Hom x) p h) g
         ≡ subst (C .Hom w) p (C ._∘_ h g))
  (ap (λ t → C ._∘_ t g) (transport-refl h) ∙ sym (transport-refl _))
  p

F₁-sub
  : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  → (K : Functor C D) {x y y' : C .Ob} (p : y ≡ y') (h : C .Hom x y)
  → K .F₁ (subst (C .Hom x) p h)
  ≡ subst (D .Hom (K .F₀ x)) (ap (K .F₀) p) (K .F₁ h)
F₁-sub {C = C} {D} K {x} p h = J
  (λ y' p → K .F₁ (subst (C .Hom x) p h)
          ≡ subst (D .Hom (K .F₀ x)) (ap (K .F₀) p) (K .F₁ h))
  (ap (K .F₁) (transport-refl h) ∙ sym (transport-refl _))
  p

comp-key
  : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    {G H : Functor C D} (q : G ≡ H) {a b : C .Ob} (h : C .Hom a b)
    {w : D .Ob} (k : D .Hom w (H .F₀ a))
  → D ._∘_ (G .F₁ h) (subst (D .Hom w) (sym (ap (λ K → K .F₀ a) q)) k)
  ≡ subst (D .Hom w) (sym (ap (λ K → K .F₀ b) q)) (D ._∘_ (H .F₁ h) k)
comp-key {D = D} {G = G} q {a} {b} h {w} k = J
  (λ H q → (k : D .Hom w (H .F₀ a))
         → D ._∘_ (G .F₁ h) (subst (D .Hom w) (sym (ap (λ K → K .F₀ a) q)) k)
         ≡ subst (D .Hom w) (sym (ap (λ K → K .F₀ b) q)) (D ._∘_ (H .F₁ h) k))
  (λ k → ap (D ._∘_ (G .F₁ h)) (transport-refl k) ∙ sym (transport-refl _))
  q k

sub-parallel
  : ∀ {oc ℓc} (C : Precategory oc ℓc) (st : is-set (C .Ob))
    {x y z : C .Ob} (p q : y ≡ z) (h : C .Hom x y)
  → subst (C .Hom x) p h ≡ subst (C .Hom x) q h
sub-parallel C st {x} p q h =
  ap (λ e → subst (C .Hom x) e h) (st _ _ p q)

sub-set
  : ∀ {oc ℓc} (C : Precategory oc ℓc) (st : is-set (C .Ob))
    {x y : C .Ob} (p : y ≡ y) (h : C .Hom x y)
  → subst (C .Hom x) p h ≡ h
sub-set C st p h = sub-parallel C st p refl h ∙ transport-refl h
```
