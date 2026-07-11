---
description: |
  The Grothendieck construction of a strictly functorial presheaf of
  strict categories: the displayed category of Belfiore–Bennequin's
  equation 2.2, its total category and projection, the canonical
  split cleaving, and the right-fibration criterion for groupoid
  fibers.
---
<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Groupoid
open import Cat.Prelude

open import Neural.Stack.Transport

import Cat.Displayed.Cartesian.Right as Right
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Grothendieck
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  where
```

# The Grothendieck construction of a split indexed category {defines="split-grothendieck"}

The stacks of Belfiore–Bennequin's chapter 2 are *split*: a strictly
functorial assignment of a (strict) category $F_U$ to each object $U$
of the site and an inverse-image functor $F_\alpha \colon F_V \to
F_U$ to each arrow $\alpha \colon U \to V$ — a functor into the
[[category of strict categories]], no pseudofunctor coherence
anywhere. The library has the *inverse* direction (a [[cartesian
fibration]] yields reindexing functors); this module supplies the
missing forward direction, as a [[displayed category]]: the paper's
equation 2.2, where a morphism over $\alpha$ from $\xi$ to $\xi'$ is
a fibre morphism $\xi \to F_\alpha\,\xi'$.

Strictness is what makes this an honest 1-categorical construction:
the identity and composition transports land in hom-sets over
*object paths in a set*, so all coherence obligations close using
only the functor laws of $F$ and the observation that parallel paths
of fibre objects are equal.

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

open Trivially-graded
open Precategory
open Functor
```
-->

The reindexing dictionary below is exported: every later stack
module speaks it.

```agda
Fib : B.Ob → Precategory o' ℓ'
Fib U = F.₀ U .fst

Fib-set : ∀ U → is-set (Fib U .Ob)
Fib-set U = F.₀ U .snd

_·₀_ : ∀ {U V} (α : B.Hom U V) → Fib V .Ob → Fib U .Ob
α ·₀ x = F.₁ α .F₀ x

_·₁_
  : ∀ {U V} (α : B.Hom U V) {x y : Fib V .Ob}
  → Fib V .Hom x y → Fib U .Hom (α ·₀ x) (α ·₀ y)
α ·₁ h = F.₁ α .F₁ h

·₀-id : ∀ {U} (x : Fib U .Ob) → B.id ·₀ x ≡ x
·₀-id x = ap (λ K → K .F₀ x) F.F-id

·₀-∘
  : ∀ {U V W} (f : B.Hom V W) (g : B.Hom U V) (x : Fib W .Ob)
  → (f B.∘ g) ·₀ x ≡ g ·₀ (f ·₀ x)
·₀-∘ f g x = ap (λ K → K .F₀ x) (F.F-∘ g f)
```

The [[transport toolkit|stack-transport-toolkit]] — the path lemmas
that push every substitution to the outside of a term, and the
parallel-path collapse that strictness then provides — lives in its
own module, shared by all the stack machinery.

## The displayed category

Objects over $U$ are the objects of the fibre $F_U$; a morphism over
$\alpha \colon U \to V$ from $\xi$ to $\xi'$ is a fibre morphism
$\xi \to \alpha^\star \xi'$ — the paper's pairs $(\alpha, u)$ of
equation 2.2, with the base component displayed away. Identity and
composition are the fibre operations transported along the
functoriality of $F$, and the three laws close by the toolkit.

```agda
private
  gr : Trivially-graded B o' ℓ'
  gr .Ob[_] U = Fib U .Ob
  gr .Hom[_] {U} α x y = Fib U .Hom x (α ·₀ y)
  gr .H-Level-Hom[_] {a = U} {f = α} {x} {y} =
    basic-instance 2 (Fib U .Hom-set x (α ·₀ y))
  gr .id' {U} {x} =
    subst (Fib U .Hom x) (sym (·₀-id x)) (Fib U .id)
  gr ._∘'_ {a = a} {x = x} {z = z} {f = f} {g = g} f' g' =
    subst (Fib a .Hom x) (sym (·₀-∘ f g z)) (Fib a ._∘_ (g ·₁ f') g')
  gr .idr' {a = a} {b} {x} {y} {f} f' = to-pathp $
       sym (subst-∙ (Fib a .Hom x) P₁ P₂ _)
    ∙  ap (subst (Fib a .Hom x) (P₁ ∙ P₂)) (comp-key F.F-id f' (Fib a .id))
    ∙  sym (subst-∙ (Fib a .Hom x) P₃ (P₁ ∙ P₂) _)
    ∙  ap (subst (Fib a .Hom x) (P₃ ∙ (P₁ ∙ P₂))) (Fib a .idr f')
    ∙  sub-set (Fib a) (Fib-set a) (P₃ ∙ (P₁ ∙ P₂)) f'
    where
      P₁ = sym (·₀-∘ f B.id y)
      P₂ = ap (_·₀ y) (B.idr f)
      P₃ = sym (·₀-id (f ·₀ y))
  gr .idl' {a = a} {b} {x} {y} {f} f' = to-pathp $
       sym (subst-∙ (Fib a .Hom x) Q₁ Q₂ _)
    ∙  ap (subst (Fib a .Hom x) (Q₁ ∙ Q₂)) step
    ∙  sym (subst-∙ (Fib a .Hom x) Q₃ (Q₁ ∙ Q₂) f')
    ∙  sub-set (Fib a) (Fib-set a) (Q₃ ∙ (Q₁ ∙ Q₂)) f'
    where
      Q₁ = sym (·₀-∘ B.id f y)
      Q₂ = ap (_·₀ y) (B.idl f)
      Q₃ = ap (F.₁ f .F₀) (sym (·₀-id y))

      step : Fib a ._∘_ (f ·₁ subst (Fib b .Hom y) (sym (·₀-id y)) (Fib b .id)) f'
           ≡ subst (Fib a .Hom x) Q₃ f'
      step =
           ap (λ t → Fib a ._∘_ t f')
             ( F₁-sub (F.₁ f) (sym (·₀-id y)) (Fib b .id)
             ∙ ap (subst (Fib a .Hom (f ·₀ y)) Q₃) (F.₁ f .F-id))
        ∙  sub-∘ˡ (Fib a) Q₃ (Fib a .id) f'
        ∙  ap (subst (Fib a .Hom x) Q₃) (Fib a .idl f')
  gr .assoc' {a = a} {b} {c} {d} {w} {x} {y} {z} {f} {g} {h} f' g' h' =
    to-pathp (chainL ∙ sub-parallel (Fib a) (Fib-set a) P-L P-R core ∙ sym chainR)
    where
      S₁ = sym (·₀-∘ f (g B.∘ h) z)
      S₃ = sym (·₀-∘ g h (f ·₀ z))
      S₄ = sym (·₀-∘ (f B.∘ g) h z)
      S₅ = sym (·₀-∘ f g z)
      S₆ = ap (F.₁ h .F₀) S₅
      AP = ap (_·₀ z) (B.assoc f g h)

      K₀ : Fib a .Hom w (h ·₀ (g ·₀ y))
      K₀ = Fib a ._∘_ (h ·₁ g') h'

      core : Fib a .Hom w (h ·₀ (g ·₀ (f ·₀ z)))
      core = Fib a ._∘_ (Fib a ._∘_ (h ·₁ (g ·₁ f')) (h ·₁ g')) h'

      P-L = S₃ ∙ (S₁ ∙ AP)
      P-R = S₆ ∙ S₄

      chainL : transport (λ i → Fib a .Hom w (B.assoc f g h i ·₀ z))
                 (subst (Fib a .Hom w) S₁
                   (Fib a ._∘_ ((g B.∘ h) ·₁ f')
                     (subst (Fib a .Hom w) (sym (·₀-∘ g h y)) K₀)))
             ≡ subst (Fib a .Hom w) P-L core
      chainL =
           sym (subst-∙ (Fib a .Hom w) S₁ AP _)
        ∙  ap (subst (Fib a .Hom w) (S₁ ∙ AP)) (comp-key (F.F-∘ h g) f' K₀)
        ∙  sym (subst-∙ (Fib a .Hom w) S₃ (S₁ ∙ AP) _)
        ∙  ap (subst (Fib a .Hom w) P-L)
             (Fib a .assoc (h ·₁ (g ·₁ f')) (h ·₁ g') h')

      chainR : subst (Fib a .Hom w) S₄
                 (Fib a ._∘_
                   (h ·₁ subst (Fib b .Hom x) S₅ (Fib b ._∘_ (g ·₁ f') g'))
                   h')
             ≡ subst (Fib a .Hom w) P-R core
      chainR =
           ap (λ t → subst (Fib a .Hom w) S₄ (Fib a ._∘_ t h'))
             ( F₁-sub (F.₁ h) S₅ (Fib b ._∘_ (g ·₁ f') g')
             ∙ ap (subst (Fib a .Hom (h ·₀ x)) S₆) (F.₁ h .F-∘ (g ·₁ f') g'))
        ∙  ap (subst (Fib a .Hom w) S₄)
             (sub-∘ˡ (Fib a) S₆ (Fib a ._∘_ (h ·₁ (g ·₁ f')) (h ·₁ g')) h')
        ∙  sym (subst-∙ (Fib a .Hom w) S₆ S₄ core)

Grothendieck : Displayed B o' ℓ'
Grothendieck = with-trivial-grading gr
```

## The total category

The [[total category]] $\int F$ and its projection to the base come
for free from the displayed machinery; this is the paper's fibered
site-in-waiting, whose sheaf theory is the subject of the following
modules.

```agda
∫F : Precategory (o ⊔ o') (ℓ ⊔ ℓ')
∫F = ∫ Grothendieck

πF : Functor ∫F B
πF = πᶠ Grothendieck
```

## The canonical cleaving

The cartesian lift of $\alpha$ at $\xi'$ is the reindexing
$\alpha^\star \xi'$, with the *identity* of the fibre as the lifting
— no transport at all, because the displayed hom-set over $\alpha$
at the reindexing is definitionally an endo-hom-set. The
universality equations are where the toolkit pays off.

```agda
open Cartesian-lift
open is-cartesian

Grothendieck-fibration : Cartesian-fibration Grothendieck
Grothendieck-fibration {x = U} {y = V} α y' .x' = α ·₀ y'
Grothendieck-fibration {x = U} {y = V} α y' .lifting = Fib U .id
Grothendieck-fibration {x = U} {y = V} α y' .cartesian .universal {u} {x''} m h' =
  subst (Fib u .Hom x'') (·₀-∘ α m y') h'
Grothendieck-fibration {x = U} {y = V} α y' .cartesian .commutes {u} {x''} m h' =
     ap (λ t → subst (Fib u .Hom x'') (sym P)
          (Fib u ._∘_ t (subst (Fib u .Hom x'') P h')))
       (F.₁ m .F-id)
  ∙  ap (subst (Fib u .Hom x'') (sym P))
       (Fib u .idl (subst (Fib u .Hom x'') P h'))
  ∙  sym (subst-∙ (Fib u .Hom x'') P (sym P) h')
  ∙  ap (λ e → subst (Fib u .Hom x'') e h') (∙-invr P)
  ∙  transport-refl h'
  where
    P = ·₀-∘ α m y'
Grothendieck-fibration {x = U} {y = V} α y' .cartesian .unique {u} {x''} {m} {h'} m' q =
     sym (transport-refl m')
  ∙  ap (λ e → subst (Fib u .Hom x'') e m') (sym (∙-invl P))
  ∙  subst-∙ (Fib u .Hom x'') (sym P) P m'
  ∙  ap (subst (Fib u .Hom x'') P) (sym inner ∙ q)
  where
    P = ·₀-∘ α m y'

    inner : subst (Fib u .Hom x'') (sym P)
              (Fib u ._∘_ (m ·₁ Fib U .id) m')
          ≡ subst (Fib u .Hom x'') (sym P) m'
    inner = ap (subst (Fib u .Hom x'') (sym P))
      (ap (λ t → Fib u ._∘_ t m') (F.₁ m .F-id) ∙ Fib u .idl m')
```

## Groupoid fibers give a right fibration

When every fibre is a pregroupoid — the situation of the paper's
stacks of groupoids — *every* displayed morphism is cartesian: the
universal factorization inverts the reindexed morphism. This is the
precise sense in which a feed-forward stack is "fibered in
groupoids".

```agda
Grothendieck-right-fibration
  : (gpd : ∀ U → is-pregroupoid (Fib U))
  → Right.Right-fibration Grothendieck
Grothendieck-right-fibration gpd .Right.Right-fibration.is-fibration =
  Grothendieck-fibration
Grothendieck-right-fibration gpd
    .Right.Right-fibration.cartesian {x = U} {y = V} {f = α} {x' = ξ} {y' = υ} f' =
  cart
  where
    cart : is-cartesian Grothendieck α f'
    cart .universal {u} {x''} m h' =
      Fib u ._∘_ (Mu.is-invertible.inv iv)
        (subst (Fib u .Hom x'') (·₀-∘ α m υ) h')
      where
        module Mu = Cat.Reasoning (Fib u)
        iv = gpd u (m ·₁ f')
    cart .commutes {u} {x''} m h' =
         ap (subst (Fib u .Hom x'') (sym P))
           ( Fib u .assoc (m ·₁ f') (Mu.is-invertible.inv iv) (subst (Fib u .Hom x'') P h')
           ∙ ap (λ t → Fib u ._∘_ t (subst (Fib u .Hom x'') P h'))
               (Mu.is-invertible.invl iv)
           ∙ Fib u .idl (subst (Fib u .Hom x'') P h'))
      ∙  sym (subst-∙ (Fib u .Hom x'') P (sym P) h')
      ∙  ap (λ e → subst (Fib u .Hom x'') e h') (∙-invr P)
      ∙  transport-refl h'
      where
        module Mu = Cat.Reasoning (Fib u)
        iv = gpd u (m ·₁ f')
        P = ·₀-∘ α m υ
    cart .unique {u} {x''} {m} {h'} m' q = sym $
         ap (Fib u ._∘_ (Mu.is-invertible.inv iv))
           ( ap (subst (Fib u .Hom x'') P) (sym q)
           ∙ subst-side)
      ∙  Fib u .assoc (Mu.is-invertible.inv iv) (m ·₁ f') m'
      ∙  ap (λ t → Fib u ._∘_ t m') (Mu.is-invertible.invr iv)
      ∙  Fib u .idl m'
      where
        module Mu = Cat.Reasoning (Fib u)
        iv = gpd u (m ·₁ f')
        P = ·₀-∘ α m υ

        subst-side : subst (Fib u .Hom x'') P
              (subst (Fib u .Hom x'') (sym P) (Fib u ._∘_ (m ·₁ f') m'))
          ≡ Fib u ._∘_ (m ·₁ f') m'
        subst-side =
             sym (subst-∙ (Fib u .Hom x'') (sym P) P (Fib u ._∘_ (m ·₁ f') m'))
          ∙  ap (λ e → subst (Fib u .Hom x'') e (Fib u ._∘_ (m ·₁ f') m'))
               (∙-invl P)
          ∙  transport-refl (Fib u ._∘_ (m ·₁ f') m')
```

The paper's naming dictionary, fixed here once for all of Phase 3:
the inverse-image functor written $\lambda_\alpha$ (and, for stacks
of categories, $F_\alpha^\star$) in equation 2.2 is `F.₁ α`; its
action on fibre objects and morphisms is the reindexing pair
`_·₀_`/`_·₁_` above; the adjoint transports $\lambda'_\alpha$ and
$\tau'_\alpha$ of §2.3 will be constructed against this module's
cleaving. What is *not* here: descent — this is the Grothendieck
construction of a split indexed category, not yet a stack condition;
sheaf-theoretic conditions on `∫F`{.Agda} enter with the classifier
and openness modules.
