<!--
```agda
open import Cat.Instances.Localisation.Invertible
open import Cat.Instances.Localisation
open import Cat.Functor.WideSubcategory
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
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

## Sites with trivial coverage

For the paper's (7) — sheaves are the localisation of presheaves at
the local isomorphisms — we can settle the case that actually applies
to the simplicial and infinitesimal sites of this development, where
the coverage is [[trivial|trivial-coverage]] and every presheaf is a
sheaf. There, the right neighbourhood structure is the *discrete*
one: a probe is its own only neighbourhood.

```agda
discrete-nbhd : ∀ (U : ⌞ C ⌟) → Neighbourhoods U
discrete-nbhd U .Neighbourhoods.Nb = Lift ℓ ⊤
discrete-nbhd U .Neighbourhoods.dom _ = U
discrete-nbhd U .Neighbourhoods.incl _ = C.id
discrete-nbhd U .Neighbourhoods.inhabited = inc (lift tt)
discrete-nbhd U .Neighbourhoods.directed n₁ n₂ =
  inc (lift tt , (C.id , C.idl _) , (C.id , C.idl _))
```

With discrete neighbourhoods, germs are just plots, so germ-wise
equivalences are plot-wise equivalences, and those are invertible
maps of presheaves.

```agda
module _ {U : ⌞ C ⌟} (X : ⌞ PSh ℓ C ⌟) where
  germs-discrete : Germs (discrete-nbhd U) X → ∣ X .F₀ U ∣
  germs-discrete = Quot-elim (λ _ → X .F₀ U .is-tr) (λ φ → φ)
    λ φ φ' r → case r of λ where
      n p → sym (happly (X .F-id) φ) ∙ p ∙ happly (X .F-id) φ'

  germs-discrete-is-equiv : is-equiv germs-discrete
  germs-discrete-is-equiv = is-iso→is-equiv (iso inc
    (λ φ → refl)
    (Quot-elim
      (λ g → is-prop→is-set (squash (inc (germs-discrete g)) g))
      (λ φ → refl)
      λ φ φ' r → is-prop→pathp
        (λ i → squash (inc (germs-discrete (quot r i))) (quot r i))
        refl refl))
```

<!--
```agda
private
  equiv→Sets-invertible
    : ∀ {A B : Set ℓ} {f : ∣ A ∣ → ∣ B ∣}
    → is-equiv f → Cat.Reasoning.is-invertible (Sets ℓ) {A} {B} f
  equiv→Sets-invertible {f = f} eq = Cat.Reasoning.make-invertible (Sets ℓ)
    (equiv→inverse eq)
    (funext (equiv→counit eq))
    (funext (equiv→unit eq))
```
-->

```agda
discrete-local-iso→invertible
  : ∀ {X Y : ⌞ PSh ℓ C ⌟} (F : X => Y)
  → is-local-iso {probe = λ U → U} discrete-nbhd F
  → Cat.Reasoning.is-invertible (PSh ℓ C) F
discrete-local-iso→invertible {X} {Y} F li =
  invertible→invertibleⁿ F λ U → equiv→Sets-invertible (η-equiv U)
  where
  η-equiv : ∀ U → is-equiv (F .η U)
  η-equiv U = subst is-equiv (funext λ φ → refl)
    ((( _ , is-iso→is-equiv (iso (germs-discrete X)
          (Quot-elim
            (λ g → is-prop→is-set
              (squash (inc (germs-discrete X g)) g))
            (λ φ → refl)
            λ φ φ' r → is-prop→pathp
              (λ i → squash (inc (germs-discrete X (quot r i))) (quot r i))
              refl refl)
          (λ φ → refl)))
      ∙e (germs-map (discrete-nbhd U) F , li U)
      ∙e (germs-discrete Y , germs-discrete-is-equiv Y)) .snd)
```

The paper's (7), for trivial-coverage sites, is then the composite of
three facts: every presheaf is a sheaf; the discrete local
isomorphisms are invertible; and [[localising at
isomorphisms|localisation-at-isomorphisms]] is inessential. The
localisation functor is an isomorphism of precategories, so
$m{Sh} = m{PSh} \simeq L^{m{liso}}m{PSh}$ on the nose.

```agda
Localise-discrete-is-precat-iso
  : is-precat-iso (Localise (PSh ℓ C)
      (local-isos {probe = λ U → U} discrete-nbhd))
Localise-discrete-is-precat-iso = Localise-is-precat-iso _ _
  λ F li → discrete-local-iso→invertible F li
```

What remains of (7) is exactly its analytic content: over the smooth
site, the neighbourhood structures are the *shrinking* open
neighbourhoods of a basepoint, germ-locality is strictly weaker than
globality, and the identification of the localisation with the sheaf
topos for the good-open-cover coverage is where the classical theory
of $R^n$ enters.
