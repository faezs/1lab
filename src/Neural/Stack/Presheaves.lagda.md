---
description: |
  From compatible families to presheaves on the total category: the
  forward half of Belfiore–Bennequin's equations 2.4–2.6, as a
  functor.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
import Neural.Stack.Grothendieck
import Neural.Stack.Family
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Presheaves
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  (κ : Level)
  where
```

# Families are presheaves on the total category {defines="family-to-presheaf"}

A [[compatible family|presheaf-family]] $\{A_U, a_\alpha\}$ over a
[[split indexed category|split-grothendieck]] determines a presheaf
on the total category $\int F$: the value at $(U, \xi)$ is
$A_U(\xi)$, and a morphism $(\alpha, u) \colon (U,\xi) \to (V,\xi')$
acts by the transition followed by the fibre restriction,
$$
A_V(\xi') \xrightarrow{\;a_\alpha\;} A_U(\alpha^\star \xi')
\xrightarrow{\;A_U(u)\;} A_U(\xi).
$$
This module packages that assignment as a functor from the category
of families; it is the forward half of the paper's equivalence
between the two presentations of a stack's presheaves (equations
2.4–2.6), and the direction every later construction uses to *build*
presheaves on $\int F$ from fibrewise data. The quasi-inverse — the
fibrewise restriction of a presheaf on $\int F$, and the equivalence
itself — is the successor module.

<!--
```agda
private
  module B = Cat.Reasoning B

open Neural.Stack.Grothendieck F
open Neural.Stack.Family F κ

open Precategory
open Family-hom
open Functor
open Family
open ∫Hom
open _=>_
```
-->

The two transport lemmas: a presheaf eats a substituted morphism by
substituting the argument backwards, and simultaneous substitution
of morphism and argument cancels.

```agda
private
  P-sub-hom
    : ∀ {oc ℓc} (C : Precategory oc ℓc) (P : Functor (C ^op) (Sets κ))
      {x y y' : C .Ob} (p : y ≡ y') (u : C .Hom x y) (v : P ʻ y')
    → Psh.₁ P (subst (C .Hom x) p u) v
    ≡ Psh.₁ P u (subst (λ e → P ʻ e) (sym p) v)
  P-sub-hom C P {x} p u = J
    (λ y' p → (v : P ʻ y')
            → Psh.₁ P (subst (C .Hom x) p u) v
            ≡ Psh.₁ P u (subst (λ e → P ʻ e) (sym p) v))
    (λ v → ap₂ (λ m w → Psh.₁ P m w) (transport-refl u) refl
         ∙ ap (Psh.₁ P u) (sym (transport-refl v)))
    p

  P-sub-both
    : ∀ {oc ℓc} (C : Precategory oc ℓc) (P : Functor (C ^op) (Sets κ))
      {x y y' : C .Ob} (p : y ≡ y') (u : C .Hom x y) (v : P ʻ y)
    → Psh.₁ P (subst (C .Hom x) p u) (subst (λ e → P ʻ e) p v)
    ≡ Psh.₁ P u v
  P-sub-both C P {x} p u v = J
    (λ y' p → Psh.₁ P (subst (C .Hom x) p u) (subst (λ e → P ʻ e) p v)
            ≡ Psh.₁ P u v)
    (ap₂ (λ m w → Psh.₁ P m w) (transport-refl u) (transport-refl v))
    p
```

## The functor

```agda
Tot₀ : Family → Functor ((∫F) ^op) (Sets κ)
Tot₀ A = T where
  T : Functor ((∫F) ^op) (Sets κ)
  T .F₀ (U , ξ) = A .fam U .F₀ ξ
  T .F₁ {V , ζ} {U , ξ} (∫hom α u) x = Psh.₁ (A .fam U) u (A .tr α x)
  T .F-id {U , ξ} = funext λ x →
       ap (Psh.₁ (A .fam U) (subst (Fib U .Hom ξ) (sym (·₀-id ξ)) (Fib U .id)))
         (A .tr-id x)
    ∙  P-sub-hom (Fib U) (A .fam U) (sym (·₀-id ξ)) (Fib U .id)
         (subst (λ e → A .fam U ʻ e) (sym (·₀-id ξ)) x)
    ∙  ap (Psh.₁ (A .fam U) (Fib U .id))
         ( sym (subst-∙ (λ e → A .fam U ʻ e) (sym (·₀-id ξ)) (·₀-id ξ) x)
         ∙ ap (λ e → subst (λ e' → A .fam U ʻ e') e x) (∙-invl (·₀-id ξ))
         ∙ transport-refl x)
    ∙  Psh.F-id (A .fam U)
  T .F-∘ {W , θ} {V , ζ} {U , ξ} (∫hom α u) (∫hom β v) = funext λ x →
       ap (Psh.₁ (A .fam U)
            (subst (Fib U .Hom ξ) (sym (·₀-∘ β α θ)) (Fib U ._∘_ (α ·₁ v) u)))
         (A .tr-∘ β α x)
    ∙  P-sub-both (Fib U) (A .fam U) (sym (·₀-∘ β α θ))
         (Fib U ._∘_ (α ·₁ v) u) (A .tr α (A .tr β x))
    ∙  Psh.F-∘ (A .fam U) u (α ·₁ v)
    ∙  ap (Psh.₁ (A .fam U) u) (sym (A .tr-nat α v (A .tr β x)))

Tot₁ : ∀ {A A' : Family} → Family-hom A A' → Tot₀ A => Tot₀ A'
Tot₁ h .η (U , ξ) = h .map U .η ξ
Tot₁ {A} {A'} h .is-natural (V , ζ) (U , ξ) (∫hom α u) = funext λ x →
     happly (h .map U .is-natural (α ·₀ ζ) ξ u) (A .tr α x)
  ∙  ap (Psh.₁ (A' .fam U) u) (sym (h .com α x))

Tot : Functor Families (PSh κ ∫F)
Tot .F₀ = Tot₀
Tot .F₁ = Tot₁
Tot .F-id = Nat-path λ _ → refl
Tot .F-∘ h' h = Nat-path λ _ → refl
```

What is honestly *not* here yet: the fibrewise restriction functor
in the other direction, and the proof that the two are quasi-inverse
— the actual equivalence
$\psh(\int F) \simeq$ `Families`{.Agda ident=Families} — which is
the successor milestone. Nothing downstream is blocked on it: the
paper's constructions produce families, and `Tot`{.Agda} is the
bridge that exhibits them as presheaves on the total site.
