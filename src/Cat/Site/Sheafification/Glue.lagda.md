<!--
```agda
open import Cat.Diagram.Sieve
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Data.Set.Coequaliser

open Functor
open Section
open Patch
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Glue
  {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc)
  where
```

<!--
```agda
open Precategory C
open Coverage J using (Membership-covers)
```
-->

# Gluing: the plus-construction {defines="saturation-of-a-coverage plus-construction-gluing"}

This module carries out the *gluing* half of the plus-construction:
for a [[separated presheaf|separated-presheaf]] $B$ on a site, the
presheaf of patches-modulo-agreement is built, receives $B$
injectively, and is separated. The patches are indexed not by the
covers of the coverage but by its **saturation** — the closure of
the covering sieves under maximality, supersets, and local
character — defined, like local equality before it, as a
proposition-valued higher inductive type, so that the coverage's
merely-existing stability witnesses eliminate freely.

```agda
data is-covering : {U : ⌞ C ⌟} (S : Sieve C U) → Type (o ⊔ ℓ ⊔ ℓc) where
  has-id
    : ∀ {U} {S : Sieve C U}
    → id ∈ S → is-covering S
  by-J
    : ∀ {U} {S : Sieve C U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c → f ∈ S)
    → is-covering S
  glue-cover
    : ∀ {U} {S : Sieve C U} (c : J ʻ U)
    → (∀ {V} (f : Hom V U) → f ∈ c → is-covering (pullback f S))
    → is-covering S
  squash
    : ∀ {U} {S : Sieve C U} → is-prop (is-covering S)
```

Saturated covers are closed under supersets and pullback — the
latter using stability, eliminated into the proposition.

```agda
covering-⊆
  : ∀ {U} {S T : Sieve C U}
  → (∀ {V} (f : Hom V U) → f ∈ S → f ∈ T)
  → is-covering S → is-covering T
covering-⊆ incl (has-id i) = has-id (incl id i)
covering-⊆ incl (by-J c sub) = by-J c λ f hf → incl f (sub f hf)
covering-⊆ incl (glue-cover c k) = glue-cover c λ f hf →
  covering-⊆ (λ g hg → incl (f ∘ g) hg) (k f hf)
covering-⊆ incl (squash a b i) =
  squash (covering-⊆ incl a) (covering-⊆ incl b) i

covering-stable
  : ∀ {U V} {S : Sieve C U} (g : Hom V U)
  → is-covering S → is-covering (pullback g S)
covering-stable {S = S} g (has-id i) = has-id
  (subst (_∈ S) (sym (idr g)) (subst (_∈ S) (idl g) (S .closed i g)))
covering-stable {S = S} g (by-J c sub) = ∥-∥-rec squash
  (λ (c' , sub') → by-J c' λ f hf → sub (g ∘ f) (sub' f hf))
  (J .stable c g)
covering-stable {S = S} g (glue-cover c k) = ∥-∥-rec squash
  (λ (c' , sub') → glue-cover c' λ f hf →
    covering-⊆ (λ h hh → subst (_∈ S) (sym (assoc g f h)) hh)
      (k (g ∘ f) (sub' f hf)))
  (J .stable c g)
covering-stable g (squash a b i) =
  squash (covering-stable g a) (covering-stable g b) i
```

A separated presheaf is separated at every saturated cover.

```agda
separated-at
  : ∀ {ℓs} {B : Functor (C ^op) (Sets ℓs)}
  → is-separated J B
  → ∀ {U} {S : Sieve C U} → is-covering S
  → is-separated₁ B S
separated-at {B = B} bsep (has-id i) l =
    sym (happly (B .F-id) _)
  ∙ l id i
  ∙ happly (B .F-id) _
separated-at bsep (by-J c sub) l =
  bsep c λ f hf → l f (sub f hf)
separated-at {B = B} bsep (glue-cover c k) l =
  bsep c λ f hf → separated-at {B = B} bsep (k f hf) λ g hg →
      sym (happly (B .F-∘ g f) _)
    ∙ l (f ∘ g) hg
    ∙ happly (B .F-∘ g f) _
separated-at {B = B} bsep (squash a b i) l =
  B .F₀ _ .is-tr _ _
    (separated-at {B = B} bsep a l) (separated-at {B = B} bsep b l) i
```

## The plus-construction on a separated presheaf

For separated $B$, the presheaf $B^+$ has, as sections over $U$,
*patches over saturated covers, modulo agreement*: two patches are
identified when their parts agree on every arrow belonging to both
covers. Separatedness makes this agreement relation transitive —
comparison through a third cover proceeds by restriction — so the
quotient is by a congruence, and is effective.

```agda
module _ {ℓs} (B : Functor (C ^op) (Sets ℓs)) (bsep : is-separated J B) where
  Patch⁺ : ⌞ C ⌟ → Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓs)
  Patch⁺ U = Σ (Sieve C U) λ S → is-covering S × Patch B S

  agree : ∀ {U} → Patch⁺ U → Patch⁺ U → Type (o ⊔ ℓ ⊔ ℓs)
  agree {U} (S , _ , p) (S' , _ , p') =
    ∀ {V} (f : Hom V U) (hf : f ∈ S) (hf' : f ∈ S')
    → p .part f hf ≡ p' .part f hf'
```

<!--
```agda
  private abstract
    agree-is-prop : ∀ {U} (α β : Patch⁺ U) → is-prop (agree α β)
    agree-is-prop (S , _ , p) (S' , _ , p') =
      Π-is-hlevel' 1 λ V → Π-is-hlevel 1 λ f →
      Π-is-hlevel 1 λ hf → Π-is-hlevel 1 λ hf' →
        B .F₀ V .is-tr _ _

    agree-refl : ∀ {U} (α : Patch⁺ U) → agree α α
    agree-refl (S , _ , p) f hf hf' = Patch.app p refl

    agree-sym : ∀ {U} {α β : Patch⁺ U} → agree α β → agree β α
    agree-sym r f hf hf' = sym (r f hf' hf)

    agree-trans
      : ∀ {U} {α β γ : Patch⁺ U}
      → agree α β → agree β γ → agree α γ
    agree-trans {α = S , _ , p} {S' , cov' , p'} {S'' , _ , p''} r₁ r₂ f hf hf'' =
      separated-at {B = B} bsep (covering-stable f cov') λ g hg →
          p .patch f hf g (S .closed hf g)
        ∙ r₁ (f ∘ g) (S .closed hf g) hg
        ∙ r₂ (f ∘ g) hg (S'' .closed hf'' g)
        ∙ sym (p'' .patch f hf'' g (S'' .closed hf'' g))

  private
    Cong⁺ : ∀ U → Congruence (Patch⁺ U) _
    Cong⁺ U .Congruence._∼_ = agree
    Cong⁺ U .Congruence.has-is-prop = agree-is-prop
    Cong⁺ U .Congruence.reflᶜ {α} = agree-refl α
    Cong⁺ U .Congruence._∙ᶜ_ {x} {y} {z} r s =
      agree-trans {α = x} {β = y} {γ = z} r s
    Cong⁺ U .Congruence.symᶜ {x} {y} r =
      agree-sym {α = x} {β = y} r

    module Cong⁺ (U : ⌞ C ⌟) = Congruence (Cong⁺ U)
```
-->

Restriction is pullback of covers and patches — no choices are made,
because the covers are arbitrary saturated sieves.

```agda
  B⁺ : Functor (C ^op) (Sets (o ⊔ ℓ ⊔ ℓc ⊔ ℓs))
  B⁺ .F₀ U = el (Patch⁺ U / agree) squash
  B⁺ .F₁ g = Coeq-rec
    (λ (S , cov , p) →
      inc (pullback g S , covering-stable g cov , pullback-patch g p))
    (λ ((S , _ , p) , (S' , _ , p') , r) →
      quot λ f hf hf' → r (g ∘ f) hf hf')
  B⁺ .F-id = funext $ Coeq-elim-prop (λ _ → squash _ _)
    λ (S , cov , p) → quot λ f hf hf' → Patch.app p (idl f)
  B⁺ .F-∘ f g = funext $ Coeq-elim-prop (λ _ → squash _ _)
    λ (S , cov , p) → quot λ h hh hh' → Patch.app p (sym (assoc g f h))
```

The unit sends a section to the total patch over the maximal sieve;
by effectivity and agreement at the identity, it is *injective* —
this is where separatedness of $B^+$'s input matters not at all, and
the maximality does all the work.

```agda
  private
    full-patch : ∀ {U} → B ʻ U → Patch B maximal'
    full-patch x .part f _ = B ⟪ f ⟫ x
    full-patch x .patch f hf g hgf = sym (happly (B .F-∘ g f) x)

  unit⁺ : ∀ {U} → B ʻ U → B⁺ ʻ U
  unit⁺ x = inc (maximal' , has-id tt , full-patch x)

  unit⁺-natural
    : ∀ {U V} (g : Hom V U) (x : B ʻ U)
    → unit⁺ (B ⟪ g ⟫ x) ≡ B⁺ ⟪ g ⟫ (unit⁺ x)
  unit⁺-natural g x = quot λ f hf hf' → sym (happly (B .F-∘ f g) x)

  unit⁺-injective
    : ∀ {U} {x y : B ʻ U}
    → unit⁺ x ≡ unit⁺ y → x ≡ y
  unit⁺-injective {U} {x} {y} p =
      sym (happly (B .F-id) x)
    ∙ Cong⁺.effective U p id tt tt
    ∙ happly (B .F-id) y
```

And $B^+$ is separated: two classes agreeing on a cover have
representatives whose parts agree on every common arrow, by
restricting to the cover, applying effectivity there, and using
separatedness of $B$ at the pulled-back cover.

```agda
  B⁺-is-separated : is-separated J B⁺
  B⁺-is-separated {U} d {x} {y} = go x y where
    go
      : (x y : Patch⁺ U / agree)
      → (∀ {V} (f : Hom V U) (hf : f ∈ d)
         → B⁺ ⟪ f ⟫ x ≡ B⁺ ⟪ f ⟫ y)
      → x ≡ y
    go = Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → squash _ _)
      λ (S , cov , p) → Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → squash _ _)
        λ (S' , cov' , p') l → quot λ f hf hf' →
          separated-at {B = B} bsep
            (covering-stable f (by-J {S = J .cover d} d (λ g hg → hg))) λ g hg →
              p .patch f hf g (S .closed hf g)
            ∙ Patch.app p (sym (idr (f ∘ g)))
            ∙ Cong⁺.effective _ (l (f ∘ g) hg) id
                (subst (_∈ S) (sym (idr (f ∘ g))) (S .closed hf g))
                (subst (_∈ S') (sym (idr (f ∘ g))) (S' .closed hf' g))
            ∙ Patch.app p' (idr (f ∘ g))
            ∙ sym (p' .patch f hf' g (S' .closed hf' g))
```

## B⁺ is a sheaf

Gluing is where the saturation pays for itself. The **total locus**
of a class — the sieve of restrictions along which it becomes a unit
— saturated-covers any representative's own cover, because
restricting a patch-class along a member of its cover yields the
unit of that part.

<!--
```agda
  private
    total-fibre : ∀ {W} → B⁺ ʻ W → Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓs)
    total-fibre ξ = Σ (B ʻ _) λ x → unit⁺ x ≡ ξ

  restrict-inc
    : ∀ {U V} (S : Sieve C U) (cov : is-covering S) (p : Patch B S)
    → (h : Hom V U) (hh : h ∈ S)
    → B⁺ ⟪ h ⟫ (inc (S , cov , p)) ≡ unit⁺ (p .part h hh)
  restrict-inc S cov p h hh = quot λ k hk hk' →
      Patch.app p refl
    ∙ sym (p .patch h hh k (S .closed hh k))

  private
    T-sieve : ∀ {V} → B⁺ ʻ V → Sieve C V
    T-sieve ξ .arrows g = elΩ (total-fibre (B⁺ ⟪ g ⟫ ξ))
    T-sieve {V} ξ .closed {f = g} hg k = □-map
      (λ (x , ux) →
          B ⟪ k ⟫ x
        , unit⁺-natural k x
        ∙ ap (B⁺ .F₁ k) ux
        ∙ sym (happly (B⁺ .F-∘ k g) ξ))
      hg

    T-covering : ∀ {V} (ξ : B⁺ ʻ V) → is-covering (T-sieve ξ)
    T-covering = Coeq-elim-prop (λ _ → squash)
      λ (S , cov , p) → covering-⊆
        (λ g hg → inc (p .part g hg , sym (restrict-inc S cov p g hg)))
        cov
```
-->

Given a $J$-cover $d$ and a patch $P$ of $B^+$ over it, the glued
class lives over the sieve $E$ of arrows factoring as $f \circ g$
with $f \in d$ and the restriction of $P(f)$ along $g$ a unit; its
part at such an arrow is the underlying section, which is unique by
injectivity of the unit, hence extractable through the truncation.

<!--
```agda
  module _ {U : ⌞ C ⌟} (d : J ʻ U) (P : Patch B⁺ (J .cover d)) where
    private
      E-data : ∀ {W} (h : Hom W U) → Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓs)
      E-data {W} h = Σ ⌞ C ⌟ λ V → Σ (Hom V U) λ f → Σ (Hom W V) λ g →
        Σ (f ∈ d) λ hf →
        (f ∘ g ≡ h) × total-fibre (B⁺ ⟪ g ⟫ (P .part f hf))

      E : Sieve C U
      E .arrows h = elΩ (E-data h)
      E .closed {f = h} hh k = □-map
        (λ (V , f , g , hf , e , x , ux) →
            V , f , g ∘ k , hf
          , assoc f g k ∙ ap (_∘ k) e
          , B ⟪ k ⟫ x
          , unit⁺-natural k x
          ∙ ap (B⁺ .F₁ k) ux
          ∙ sym (happly (B⁺ .F-∘ k g) (P .part f hf)))
        hh

      E-extract : ∀ {W} (h : Hom W U) → E-data h → B ʻ W
      E-extract h (V , f , g , hf , e , x , ux) = x

      E-const
        : ∀ {W} (h : Hom W U) (α β : E-data h)
        → E-extract h α ≡ E-extract h β
      E-const h (V , f , g , hf , e , x , ux) (V' , f' , g' , hf' , e' , x' , ux') =
        unit⁺-injective
          (ux ∙ Patch.compatible P g g' (e ∙ sym e') ∙ sym ux')

      qext : ∀ {W} (h : Hom W U) → ∥ E-data h ∥ → B ʻ W
      qext h = ∥-∥-rec-set (B .F₀ _ .is-tr) (E-extract h) (E-const h)

      q-patch
        : ∀ {W W'} (h : Hom W U) (k : Hom W' W)
        → (t : ∥ E-data h ∥) (t' : ∥ E-data (h ∘ k) ∥)
        → B ⟪ k ⟫ (qext h t) ≡ qext (h ∘ k) t'
      q-patch h k = ∥-∥-elim₂ (λ _ _ → B .F₀ _ .is-tr _ _)
        λ (V , f , g , hf , e , x , ux) (V' , f' , g' , hf' , e' , x' , ux') →
          unit⁺-injective
            ( unit⁺-natural k x
            ∙ ap (B⁺ .F₁ k) ux
            ∙ sym (happly (B⁺ .F-∘ k g) (P .part f hf))
            ∙ Patch.compatible P (g ∘ k) g'
                (assoc f g k ∙ ap (_∘ k) e ∙ sym e')
            ∙ sym ux')

      q : Patch B E
      q .part h hh = qext h (□-tr hh)
      q .patch h hh k hhk = q-patch h k (□-tr hh) (□-tr hhk)

      E-covering : is-covering E
      E-covering = glue-cover d λ f hf →
        covering-⊆
          (λ g hg → □-map (λ (x , ux) → _ , f , g , hf , refl , x , ux) hg)
          (T-covering (P .part f hf))

    whole⁺ : B⁺ ʻ U
    whole⁺ = inc (E , E-covering , q)

    glues⁺
      : ∀ {V} (f : Hom V U) (hf : f ∈ d)
      → B⁺ ⟪ f ⟫ whole⁺ ≡ P .part f hf
    glues⁺ f hf = separated-at {B = B⁺} B⁺-is-separated
      (T-covering (P .part f hf))
      λ g hg → □-rec (squash _ _)
        (λ (x , ux) →
            sym (happly (B⁺ .F-∘ g f) whole⁺)
          ∙ restrict-inc E E-covering q (f ∘ g)
              (inc (_ , f , g , hf , refl , x , ux))
          ∙ ux)
        hg
```
-->

Assembling the three pieces: **the plus-construction of a separated
presheaf is a sheaf**, receiving it injectively — the gluing half of
the two-step sheafification, over an arbitrary coverage.

```agda
  B⁺-is-sheaf : is-sheaf J B⁺
  B⁺-is-sheaf .is-sheaf.whole d P = whole⁺ d P
  B⁺-is-sheaf .is-sheaf.glues d P f hf = glues⁺ d P f hf
  B⁺-is-sheaf .is-sheaf.separate = B⁺-is-separated
```

Combined with the [[separated quotient|separated-quotient]] of the
previous module, every ingredient of the classical two-step
construction now exists; composing them — and extracting, via the
universal property of the higher-inductive sheafification, the
characterisation of the unit's kernel as saturated local equality,
whence left exactness — is the remaining assembly, now purely
mechanical in outline.
