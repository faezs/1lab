<!--
```agda
open import Cat.Instances.Localisation
open import Cat.Functor.WideSubcategory
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Presheaf.Germs {ℓ} (C : Precategory ℓ ℓ) where
```

<!--
```agda
private
  module C = Cat.Reasoning C
```
-->

# Germs of plots {defines="germ-of-a-plot neighbourhood-structure local-isomorphism"}

A basic result of sheaf theory says that a smooth set is determined
already by the *germs* of its plots: their classes under agreement on
arbitrarily small neighbourhoods of a base point. To speak of germs
over an arbitrary category of probes, all we need is, for a probe
$U$, a *neighbourhood structure*: a directed, inhabited family of
"shrinking" maps into $U$ — for the smooth site, the open
neighbourhoods of $0 \in \bR^n$.

```agda
record Neighbourhoods (U : ⌞ C ⌟) : Type (lsuc ℓ) where
  no-eta-equality
  field
    Nb        : Type ℓ
    dom       : Nb → ⌞ C ⌟
    incl      : ∀ n → C.Hom (dom n) U
    inhabited : ∥ Nb ∥
    directed
      : ∀ n₁ n₂ → ∃[ n₃ ∈ Nb ]
          ( (Σ[ f ∈ C.Hom (dom n₃) (dom n₁) ] (incl n₁ C.∘ f ≡ incl n₃))
          × (Σ[ g ∈ C.Hom (dom n₃) (dom n₂) ] (incl n₂ C.∘ g ≡ incl n₃)))
```

Two plots of a presheaf $X$ by $U$ have the same germ when some
neighbourhood fails to distinguish them; the paper's (5) is the
quotient of the plots by this relation. Directedness makes the
relation transitive and inhabitation makes it reflexive, but the
set-quotient does not even need this: it quotients by the generated
equivalence relation either way.

```agda
module _ {U : ⌞ C ⌟} (N : Neighbourhoods U) where
  open Neighbourhoods N

  germ-rel : (X : ⌞ PSh ℓ C ⌟) → ∣ X .F₀ U ∣ → ∣ X .F₀ U ∣ → Type ℓ
  germ-rel X φ φ' =
    ∃[ n ∈ Nb ] (X .F₁ (incl n) φ ≡ X .F₁ (incl n) φ')

  Germs : ⌞ PSh ℓ C ⌟ → Type ℓ
  Germs X = ∣ X .F₀ U ∣ / germ-rel X
```

Maps of presheaves restrict to germs of plots — the paper's (6) —
because restriction commutes with the components of a natural
transformation.

```agda
  germs-map : ∀ {X Y} → X => Y → Germs X → Germs Y
  germs-map {X} {Y} F = Quot-elim (λ _ → squash)
    (λ φ → inc (F .η U φ))
    λ φ φ' r → quot (case r of λ where
      n p → inc (n ,
          sym (happly (F .is-natural U (dom n) (incl n)) φ)
        ∙ ap (F .η (dom n)) p
        ∙ happly (F .is-natural U (dom n) (incl n)) φ'))
```

<!--
```agda
  germs-map-id
    : ∀ {X} (g : Germs X)
    → germs-map {X} {X} idnt g ≡ g
  germs-map-id {X} = Quot-elim
    (λ g → is-prop→is-set (squash (germs-map {X} {X} idnt g) g))
    (λ _ → refl)
    λ φ φ' r → is-prop→pathp
      (λ i → squash (germs-map {X} {X} idnt (quot r i)) (quot r i)) refl refl

  germs-map-∘
    : ∀ {X Y Z} (F : Y => Z) (G : X => Y)
    → ∀ g → germs-map (F ∘nt G) g ≡ germs-map F (germs-map G g)
  germs-map-∘ F G = Quot-elim
    (λ g → is-prop→is-set
      (squash (germs-map (F ∘nt G) g) (germs-map F (germs-map G g))))
    (λ _ → refl)
    λ φ φ' r → is-prop→pathp
      (λ i → squash (germs-map (F ∘nt G) (quot r i))
                    (germs-map F (germs-map G (quot r i)))) refl refl
```
-->

## Local isomorphisms

Given neighbourhood structures for a family of probes, the **local
isomorphisms** are the maps of presheaves inducing isomorphisms on
all germs. This is the class at which the paper's (7) localises the
presheaf topos to recover the sheaf topos; the localisation itself
exists in complete generality, as a higher inductive type.

```agda
module _ {I : Type ℓ} {probe : I → ⌞ C ⌟}
         (nbhd : ∀ i → Neighbourhoods (probe i))
  where

  is-local-iso : ∀ {X Y : ⌞ PSh ℓ C ⌟} → X => Y → Type ℓ
  is-local-iso F = ∀ i → is-equiv (germs-map (nbhd i) F)

  local-isos : Wide-subcat (PSh ℓ C) ℓ
  local-isos .Wide-subcat.P = is-local-iso
  local-isos .Wide-subcat.P-prop F = hlevel 1
  local-isos .Wide-subcat.P-id {X} i = subst is-equiv
    (sym (funext (germs-map-id (nbhd i) {X = X})))
    id-equiv
  local-isos .Wide-subcat.P-∘ {f = F} {g = G} pf pg i = subst is-equiv
    (sym (funext (germs-map-∘ (nbhd i) F G)))
    (((_ , pg i) ∙e (_ , pf i)) .snd)

  L-liso : Precategory (lsuc ℓ) (lsuc ℓ)
  L-liso = Localisation (PSh ℓ C) local-isos
```

The identification of `L-liso`{.Agda} with the topos of sheaves — the
statement that arbitrarily small probes suffice to see the smooth
structure — depends on the specific coverage and neighbourhood
structures of the site, and remains future work.
