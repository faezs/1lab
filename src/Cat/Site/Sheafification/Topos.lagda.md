<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Naturality
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Site.Sheafification
open import Cat.Instances.Sheaves
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Topoi.Base using (Topos)

import Cat.Site.Sheafification.Kernel
import Cat.Site.Sheafification.Plus
import Cat.Site.Sheafification.Lex
import Cat.Reasoning

open Functor
open _=>_
open is-pullback
```
-->

```agda
module Cat.Site.Sheafification.Topos
  {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  where
```

<!--
```agda
open Precategory C
open Coverage J using (Membership-covers)

private
  module S     = Small J
  module Sh    = Cat.Reasoning (Sheaves J ℓ)
  module PShR  = Cat.Reasoning (PSh ℓ C)
  module SetsR = Cat.Reasoning (Sets ℓ)
```
-->

# The topos of sheaves, officially {defines="sheafification-is-lex sheaves-topos"}

The [[topos of sheaves]] on a [[site]] deserves its name in the
official, structural sense of `Topos`{.Agda}: it is a full
subcategory of a presheaf category whose reflector preserves finite
limits. Everything but the left exactness of the reflector is
already established elsewhere; the [[kernel of the sheafification
unit|sheafification-kernel]] is the last missing ingredient, and this
module spends it. The strategy for pullback preservation is entirely
concrete: compute the pullback of presheaves *pointwise*, compute
the pullback of sheaves pointwise as well, and connect the
sheafification of the former to the latter by a comparison map whose
bijectivity is exactly the kernel theorem plus gluing.

## The pointwise pullback of presheaves

Fix a cospan $X \xrightarrow{f} Z \xleftarrow{g} Y$ of presheaves.
Its pullback is computed pointwise: a section over $U$ is a pair of
sections agreeing in $Z(U)$.

```agda
module _ {X Y Z : Functor (C ^op) (Sets ℓ)} (f : X => Z) (g : Y => Z) where
  Pc : Functor (C ^op) (Sets ℓ)
  Pc .F₀ U = el
    (Σ[ xy ∈ X ʻ U × Y ʻ U ] (f .η U (xy .fst) ≡ g .η U (xy .snd)))
    (Σ-is-hlevel 2
      (×-is-hlevel 2 (X .F₀ U .is-tr) (Y .F₀ U .is-tr))
      (λ _ → is-prop→is-set (Z .F₀ U .is-tr _ _)))
  Pc .F₁ h ((x , y) , e) = (X ⟪ h ⟫ x , Y ⟪ h ⟫ y) ,
       happly (f .is-natural _ _ h) x
    ∙∙ ap (Z .F₁ h) e
    ∙∙ sym (happly (g .is-natural _ _ h) y)
  Pc .F-id = funext λ ((x , y) , e) →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (happly (X .F-id) x) (happly (Y .F-id) y))
  Pc .F-∘ h₂ h₁ = funext λ ((x , y) , e) →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (happly (X .F-∘ h₂ h₁) x) (happly (Y .F-∘ h₂ h₁) y))
```

The two projections are natural on the nose, and the agreement
condition *is* the commutativity of the square.

```agda
  pc1 : Pc => X
  pc1 .η U ((x , y) , e) = x
  pc1 .is-natural U V h = refl

  pc2 : Pc => Y
  pc2 .η U ((x , y) , e) = y
  pc2 .is-natural U V h = refl
```

That this is a pullback in $\psh(\cC)$ is a pointwise computation:
maps into the pullback are pairs of maps with a pointwise agreement,
and equality of such maps is equality of the two components, since
the agreement is a proposition.

```agda
  Pc-is-pullback : is-pullback (PSh ℓ C) pc1 f pc2 g
  Pc-is-pullback .square = Nat-path λ U → funext λ ((x , y) , e) → e
  Pc-is-pullback .universal {p₁' = p₁'} {p₂'} sq .η U a =
    (p₁' .η U a , p₂' .η U a) , (sq ηₚ U $ₚ a)
  Pc-is-pullback .universal {p₁' = p₁'} {p₂'} sq .is-natural U V h =
    funext λ a → Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_
        (happly (p₁' .is-natural U V h) a)
        (happly (p₂' .is-natural U V h) a))
  Pc-is-pullback .p₁∘universal = Nat-path λ U → refl
  Pc-is-pullback .p₂∘universal = Nat-path λ U → refl
  Pc-is-pullback .unique {lim' = lim'} q₁ q₂ = Nat-path λ U → funext λ a →
    Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _)
      (ap₂ _,_ (q₁ ηₚ U $ₚ a) (q₂ ηₚ U $ₚ a))
```

## The pointwise pullback of sheaves

Now apply the same construction one level up: sheafify the cospan,
and form the pointwise pullback $Q$ of the resulting cospan
$X^+ \to Z^+ \ot Y^+$ of sheaves. Because the sheafification functor
is built from the universal property, its action on morphisms
computes definitionally on the `inc`{.Agda} constructor, which the
rest of this module uses without further comment.

<!--
```agda
  private
    module LX = Sheafification J X
    module LY = Sheafification J Y
    module LZ = Sheafification J Z
```
-->

```agda
  Lf : LX.Sheafify => LZ.Sheafify
  Lf = Sheafification {C = C} {J = J} .F₁ f

  Lg : LY.Sheafify => LZ.Sheafify
  Lg = Sheafification {C = C} {J = J} .F₁ g

  Q : Functor (C ^op) (Sets ℓ)
  Q .F₀ U = el
    (Σ[ ab ∈ LX.Sheafify ʻ U × LY.Sheafify ʻ U ]
      (Lf .η U (ab .fst) ≡ Lg .η U (ab .snd)))
    (Σ-is-hlevel 2
      (×-is-hlevel 2 LX.squash LY.squash)
      (λ _ → is-prop→is-set (LZ.squash _ _)))
  Q .F₁ h ((a , b) , w) = (LX.map h a , LY.map h b) ,
       happly (Lf .is-natural _ _ h) a
    ∙∙ ap (LZ.map h) w
    ∙∙ sym (happly (Lg .is-natural _ _ h) b)
  Q .F-id = funext λ ((a , b) , w) →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (LX.map-id a) (LY.map-id b))
  Q .F-∘ h₂ h₁ = funext λ ((a , b) , w) →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (LX.map-∘ a) (LY.map-∘ b))

  q1 : Q => LX.Sheafify
  q1 .η U ((a , b) , w) = a
  q1 .is-natural U V h = refl

  q2 : Q => LY.Sheafify
  q2 .η U ((a , b) , w) = b
  q2 .is-natural U V h = refl
```

The point of the construction: $Q$ is itself a sheaf. Separatedness
is componentwise, since both components live in sheaves. For gluing,
a patch of $Q$ has two component patches; gluing each in its own
sheafification gives the two components of the candidate section,
and the *agreement* of these components is a $J$-local question —
so it follows from separatedness of $Z^+$, since it holds on the
cover by the very compatibility the patch carries.

<!--
```agda
  private
    patch-X : ∀ {U} {c : J ʻ U} → Patch Q (J .cover c) → Patch LX.Sheafify (J .cover c)
    patch-X p .part h hh = p .part h hh .fst .fst
    patch-X p .patch h hh h' hh' = ap (λ t → t .fst .fst) (p .patch h hh h' hh')

    patch-Y : ∀ {U} {c : J ʻ U} → Patch Q (J .cover c) → Patch LY.Sheafify (J .cover c)
    patch-Y p .part h hh = p .part h hh .fst .snd
    patch-Y p .patch h hh h' hh' = ap (λ t → t .fst .snd) (p .patch h hh h' hh')
```
-->

```agda
  Q-is-sheaf : is-sheaf J Q
  Q-is-sheaf = from-is-separated Q-sep Q-split where
    Q-sep : is-separated J Q
    Q-sep c loc = Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_
        (LX.Sheafify-is-sep c λ h hh → ap (λ t → t .fst .fst) (loc h hh))
        (LY.Sheafify-is-sep c λ h hh → ap (λ t → t .fst .snd) (loc h hh)))

    Q-split : ∀ {U} (c : J .covers U) (p : Patch Q (J .cover c)) → Section Q p
    Q-split c p = record { whole = (wx , wy) , cond ; glues = λ h hh →
      Σ-prop-path (λ _ → LZ.squash _ _)
        (ap₂ _,_
          (LX.Sheafify-is-sheaf .glues c (patch-X p) h hh)
          (LY.Sheafify-is-sheaf .glues c (patch-Y p) h hh)) }
      where
      wx = LX.Sheafify-is-sheaf .whole c (patch-X p)
      wy = LY.Sheafify-is-sheaf .whole c (patch-Y p)

      cond : Lf .η _ wx ≡ Lg .η _ wy
      cond = LZ.Sheafify-is-sep c λ h hh →
           ap (Lf .η _) (LX.Sheafify-is-sheaf .glues c (patch-X p) h hh)
        ∙∙ p .part h hh .snd
        ∙∙ sym (ap (Lg .η _) (LY.Sheafify-is-sheaf .glues c (patch-Y p) h hh))
```

Finally, $Q$ is a pullback of the sheafified cospan *in the category
of sheaves*. Since morphisms of sheaves are just morphisms of the
underlying presheaves, the proof is word for word the one for
`Pc`{.Agda} — note that it nowhere uses that the competitor is a
sheaf.

```agda
  Q-is-pullback : is-pullback (Sheaves J ℓ)
    {X = LX.Sheafify , LX.Sheafify-is-sheaf}
    {Z = LZ.Sheafify , LZ.Sheafify-is-sheaf}
    {Y = LY.Sheafify , LY.Sheafify-is-sheaf}
    {P = Q , Q-is-sheaf}
    q1 Lf q2 Lg
  Q-is-pullback .square = Nat-path λ U → funext λ ((a , b) , w) → w
  Q-is-pullback .universal {p₁' = p₁'} {p₂'} sq .η U t =
    (p₁' .η U t , p₂' .η U t) , (sq ηₚ U $ₚ t)
  Q-is-pullback .universal {p₁' = p₁'} {p₂'} sq .is-natural U V h =
    funext λ t → Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_
        (happly (p₁' .is-natural U V h) t)
        (happly (p₂' .is-natural U V h) t))
  Q-is-pullback .p₁∘universal = Nat-path λ U → refl
  Q-is-pullback .p₂∘universal = Nat-path λ U → refl
  Q-is-pullback .unique {lim' = lim'} q₁ q₂ = Nat-path λ U → funext λ t →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (q₁ ηₚ U $ₚ t) (q₂ ηₚ U $ₚ t))
```

## The comparison map

The sheafification of `Pc`{.Agda} maps canonically into $Q$: on
generators, include both components. This is where the universal
property earns its keep — the comparison `θ`{.Agda} computes
definitionally on `inc`{.Agda}, and is natural by `refl`.

<!--
```agda
  private
    module LPc = Sheafification J Pc
    module PX  = Cat.Site.Sheafification.Plus J X
    module PY  = Cat.Site.Sheafification.Plus J Y
    module PZ  = Cat.Site.Sheafification.Plus J Z
    module KX  = Cat.Site.Sheafification.Kernel J X
    module KY  = Cat.Site.Sheafification.Kernel J Y
    module KZ  = Cat.Site.Sheafification.Kernel J Z

    inc-pc
      : ∀ {U} {p p' : Pc ʻ U} → p ≡ p'
      → Path (LPc.Sheafify₀ U) (LPc.inc p) (LPc.inc p')
    inc-pc = ap LPc.inc
```
-->

```agda
  φ : Pc => Q
  φ .η U ((x , y) , e) = (LX.inc x , LY.inc y) , ap LZ.inc e
  φ .is-natural U V h = funext λ ((x , y) , e) →
    Σ-prop-path (λ _ → LZ.squash _ _)
      (ap₂ _,_ (LX.inc-natural x) (LY.inc-natural y))

  θ : LPc.Sheafify => Q
  θ = S.univ Q Q-is-sheaf φ
```

## Injectivity

We first show `θ`{.Agda} is componentwise injective. The heart of
the argument concerns generators: if $\theta$ identifies
$\operatorname{inc}(x, y, e)$ and $\operatorname{inc}(x', y', e')$,
then $\operatorname{inc} x = \operatorname{inc} x'$ in $X^+$ and
likewise in $Y^+$, so by the [[kernel theorem|sheafification-kernel]]
$x$ and $x'$ (resp. $y, y'$) are *locally equal* — untruncated data,
by the design of `Loc-eq`{.Agda}. From a pair of local equalities we
can build a path of `inc`{.Agda}s in the sheafification of
`Pc`{.Agda} directly, by structural recursion: first rewrite along
the first derivation (restricting the second as we go, exactly the
shape of `loc-trans`{.Agda}), then along the second.

```agda
  private
    pair-inc-path-r
      : ∀ {U} {x : X ʻ U} {y y' : Y ʻ U}
      → PY.Loc-eq y y'
      → (e : f .η U x ≡ g .η U y) (e' : f .η U x ≡ g .η U y')
      → Path (LPc.Sheafify₀ U) (LPc.inc ((x , y) , e)) (LPc.inc ((x , y') , e'))
    pair-inc-path-r (PY.here q) e e' =
      inc-pc (Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _) (ap₂ _,_ refl q))
    pair-inc-path-r {x = x} {y} {y'} (PY.locally c k) e e' = LPc.sep c λ h hh →
        sym (LPc.inc-natural _)
      ∙∙ pair-inc-path-r (k h hh)
          ((Pc ⟪ h ⟫ ((x , y) , e)) .snd)
          ((Pc ⟪ h ⟫ ((x , y') , e')) .snd)
      ∙∙ LPc.inc-natural _
    pair-inc-path-r (PY.squash a b i) e e' =
      LPc.squash _ _ (pair-inc-path-r a e e') (pair-inc-path-r b e e') i

    pair-inc-path
      : ∀ {U} {x x' : X ʻ U} {y y' : Y ʻ U}
      → PX.Loc-eq x x' → PY.Loc-eq y y'
      → (e : f .η U x ≡ g .η U y) (e' : f .η U x' ≡ g .η U y')
      → Path (LPc.Sheafify₀ U) (LPc.inc ((x , y) , e)) (LPc.inc ((x' , y') , e'))
    pair-inc-path {x = x} {x'} {y = y} (PX.here p) w e e' =
        inc-pc {p' = (x' , y) , e-mid}
          (Σ-prop-path (λ _ → Z .F₀ _ .is-tr _ _) (ap₂ _,_ p refl))
      ∙ pair-inc-path-r w e-mid e'
      where e-mid = subst (λ v → f .η _ v ≡ g .η _ y) p e
    pair-inc-path {x = x} {x'} {y = y} {y'} (PX.locally c k) w e e' =
      LPc.sep c λ h hh →
          sym (LPc.inc-natural _)
        ∙∙ pair-inc-path (k h hh) (PY.restrict h w)
            ((Pc ⟪ h ⟫ ((x , y) , e)) .snd)
            ((Pc ⟪ h ⟫ ((x' , y') , e')) .snd)
        ∙∙ LPc.inc-natural _
    pair-inc-path (PX.squash a b i) w e e' =
      LPc.squash _ _ (pair-inc-path a w e e') (pair-inc-path b w e e') i
```

Injectivity itself is a double induction with the HIT's elimination
principle. The inner induction generalises over the generator on the
left, so that the motive stays inferable at every object; the
`plocal`{.Agda} cases go through separatedness of the
sheafification, using that `θ`{.Agda} commutes with restriction
definitionally.

```agda
  private
    θ-inj-inc
      : ∀ {U} (ζ : LPc.Sheafify₀ U) (p : Pc ʻ U)
      → θ .η U (LPc.inc p) ≡ θ .η U ζ
      → Path (LPc.Sheafify₀ U) (LPc.inc p) ζ
    θ-inj-inc = LPc.Sheafify-elim-prop
      (λ {U} ζ → (p : Pc ʻ U) → θ .η U (LPc.inc p) ≡ θ .η U ζ → LPc.inc p ≡ ζ)
      (λ ζ → Π-is-hlevel 1 λ p → Π-is-hlevel 1 λ w → LPc.squash _ _)
      (λ {U} p' p w → pair-inc-path
        (KX.encode {x = p .fst .fst} {y = p' .fst .fst} (ap (λ t → t .fst .fst) w))
        (KY.encode {x = p .fst .snd} {y = p' .fst .snd} (ap (λ t → t .fst .snd) w))
        (p .snd) (p' .snd))
      (λ {U} c ζ ih p w → LPc.sep c λ h hh →
          sym (LPc.inc-natural p)
        ∙ ih h hh (Pc ⟪ h ⟫ p) (happly (φ .is-natural _ _ h) p ∙ ap (Q .F₁ h) w))

  abstract
    θ-inj
      : ∀ {U} {ξ ζ : LPc.Sheafify₀ U}
      → θ .η U ξ ≡ θ .η U ζ → ξ ≡ ζ
    θ-inj {ξ = ξ} {ζ} w = go ξ ζ w where
      go : ∀ {U} (ξ ζ : LPc.Sheafify₀ U) → θ .η U ξ ≡ θ .η U ζ → ξ ≡ ζ
      go = LPc.Sheafify-elim-prop
        (λ {U} ξ → (ζ : LPc.Sheafify₀ U) → θ .η U ξ ≡ θ .η U ζ → ξ ≡ ζ)
        (λ ξ → Π-is-hlevel 1 λ ζ → Π-is-hlevel 1 λ w → LPc.squash _ _)
        (λ p ζ w → θ-inj-inc ζ p w)
        (λ {U} c ξ ih ζ w → LPc.sep c λ h hh →
          ih h hh (LPc.map h ζ) (ap (Q .F₁ h) w))
```

## Surjectivity

Because `θ`{.Agda} is injective into a set, its fibres are
propositions — this is the load-bearing observation, since it means
fibres can be *glued* along a cover without any choice: the local
witnesses agree wherever they overlap, again by injectivity, so they
form a patch in the sheafification, and the section they glue to is
a preimage by separatedness of $Q$.

```agda
  abstract
    θ-fibre-prop : ∀ {U} (t : Q ʻ U) → is-prop (fibre (θ .η U) t)
    θ-fibre-prop t (ξ , α) (ζ , β) =
      Σ-prop-path (λ _ → Q .F₀ _ .is-tr _ _) (θ-inj (α ∙ sym β))

    glue-fibre
      : ∀ {U} (c : J ʻ U) (t : Q ʻ U)
      → (ps : ∀ {V} (h : Hom V U) (hh : h ∈ c) → fibre (θ .η V) (Q ⟪ h ⟫ t))
      → fibre (θ .η U) t
    glue-fibre {U} c t ps =
        LPc.glue c parts patchy
      , Q-is-sheaf .separate c λ h hh →
          ap (θ .η _) (LPc.glues c parts patchy h hh) ∙ ps h hh .snd
      where
      parts : pre.Parts C LPc.map (J .cover c)
      parts h hh = ps h hh .fst

      patchy : pre.is-patch C LPc.map (J .cover c) parts
      patchy h hh h' hh' = θ-inj
        (  ap (Q .F₁ h') (ps h hh .snd)
        ∙∙ sym (happly (Q .F-∘ h' h) t)
        ∙∙ sym (ps (h ∘ h') hh' .snd))
```

Now every point of $Q$ has a fibre, by a triple induction: on the
$X^+$-component, on the $Y^+$-component, and finally — when both are
generators, so that the agreement is a path
$\operatorname{inc}(f\,x) = \operatorname{inc}(g\,y)$ in $Z^+$ — by
structural induction on the *local equality* that the kernel theorem
extracts from that path. In the base case the pair glues on the
nose; in the `locally`{.Agda} case the problem restricts to a cover,
where `glue-fibre`{.Agda} reassembles the recursively-obtained
preimages. Since the fibres are propositions, all the motives are
propositional and the coverage's mere existentials do no harm.

To keep the recursion structural, the generator case is generalised
over the endpoints of the local equality: the derivation lives at
arbitrary $u, v : Z(U)$ which are merely *connected* to $f\,x$ and
$g\,y$ by paths, and restriction acts on $u$ and $v$ directly, so
the induction hypothesis applies to the sub-derivation on the nose.

```agda
  abstract
    θ-surj-inc
      : ∀ {U} (x : X ʻ U) (y : Y ʻ U) (u v : Z ʻ U)
      → PZ.Loc-eq u v
      → (pu : f .η U x ≡ u) (pv : g .η U y ≡ v)
      → (w : Lf .η U (LX.inc x) ≡ Lg .η U (LY.inc y))
      → fibre (θ .η U) ((LX.inc x , LY.inc y) , w)
    θ-surj-inc x y u v (PZ.here p) pu pv w =
        LPc.inc ((x , y) , pu ∙∙ p ∙∙ sym pv)
      , Σ-prop-path (λ _ → LZ.squash _ _) refl
    θ-surj-inc {U} x y u v (PZ.locally c k) pu pv w =
      glue-fibre c _ λ {V} h hh →
        subst (fibre (θ .η V))
          (Σ-prop-path (λ _ → LZ.squash _ _)
            (ap₂ _,_ (LX.inc-natural x) (LY.inc-natural y)))
          (θ-surj-inc (X ⟪ h ⟫ x) (Y ⟪ h ⟫ y) (Z ⟪ h ⟫ u) (Z ⟪ h ⟫ v)
            (k h hh)
            (happly (f .is-natural _ _ h) x ∙ ap (Z .F₁ h) pu)
            (happly (g .is-natural _ _ h) y ∙ ap (Z .F₁ h) pv)
            (  ap LZ.inc (happly (f .is-natural _ _ h) x ∙ ap (Z .F₁ h) pu)
            ∙∙ PZ.loc-eq→inc-path (k h hh)
            ∙∙ sym (ap LZ.inc (happly (g .is-natural _ _ h) y ∙ ap (Z .F₁ h) pv))))
    θ-surj-inc x y u v (PZ.squash a b i) pu pv w =
      θ-fibre-prop _
        (θ-surj-inc x y u v a pu pv w)
        (θ-surj-inc x y u v b pu pv w) i

    θ-surj-Y
      : ∀ {U} (b : LY.Sheafify₀ U) (x : X ʻ U)
      → (w : Lf .η U (LX.inc x) ≡ Lg .η U b)
      → fibre (θ .η U) ((LX.inc x , b) , w)
    θ-surj-Y = LY.Sheafify-elim-prop
      (λ {U} b → (x : X ʻ U) (w : Lf .η U (LX.inc x) ≡ Lg .η U b)
               → fibre (θ .η U) ((LX.inc x , b) , w))
      (λ b → Π-is-hlevel 1 λ x → Π-is-hlevel 1 λ w → θ-fibre-prop _)
      (λ {U} y x w → θ-surj-inc x y (f .η U x) (g .η U y)
        (KZ.encode {x = f .η U x} {y = g .η U y} w) refl refl w)
      (λ {U} c b ih x w → glue-fibre c _ λ {V} h hh →
        subst (fibre (θ .η V))
          (Σ-prop-path (λ _ → LZ.squash _ _)
            (ap₂ _,_ (LX.inc-natural x) refl))
          (ih h hh (X ⟪ h ⟫ x)
            (ap (Lf .η V) (LX.inc-natural x)
              ∙ (Q ⟪ h ⟫ ((LX.inc x , b) , w)) .snd)))

    θ-surj-X
      : ∀ {U} (a : LX.Sheafify₀ U) (b : LY.Sheafify₀ U)
      → (w : Lf .η U a ≡ Lg .η U b)
      → fibre (θ .η U) ((a , b) , w)
    θ-surj-X = LX.Sheafify-elim-prop
      (λ {U} a → (b : LY.Sheafify₀ U) (w : Lf .η U a ≡ Lg .η U b)
               → fibre (θ .η U) ((a , b) , w))
      (λ a → Π-is-hlevel 1 λ b → Π-is-hlevel 1 λ w → θ-fibre-prop _)
      (λ {U} x b w → θ-surj-Y b x w)
      (λ {U} c a ih b w → glue-fibre c _ λ {V} h hh →
        ih h hh (LY.map h b) ((Q ⟪ h ⟫ ((a , b) , w)) .snd))

    θ-surj : ∀ {U} (t : Q ʻ U) → fibre (θ .η U) t
    θ-surj ((a , b) , w) = θ-surj-X a b w
```

## Invertibility

An untruncated preimage together with propositional fibres is
exactly contractibility of the fibres — so each component of
`θ`{.Agda} is an equivalence outright, with no lemma about
injective-surjective maps needed.

```agda
  θ-is-equiv : ∀ {U} → is-equiv (θ .η U)
  θ-is-equiv .is-eqv t = contr (θ-surj t) (θ-fibre-prop t (θ-surj t))
```

Componentwise invertibility makes `θ`{.Agda} invertible as a natural
transformation; and since morphisms, composition and identity in the
category of sheaves are literally those of presheaves, the same data
exhibits `θ`{.Agda} as invertible in $\Sh(\cC, J)$.

```agda
  θ-psh-invertible : PShR.is-invertible θ
  θ-psh-invertible = invertible→invertibleⁿ θ λ U → SetsR.make-invertible
    (equiv→inverse θ-is-equiv)
    (funext (equiv→counit θ-is-equiv))
    (funext (equiv→unit θ-is-equiv))

  θ-sh-invertible : Sh.is-invertible
    {a = LPc.Sheafify , LPc.Sheafify-is-sheaf}
    {b = Q , Q-is-sheaf}
    θ
  θ-sh-invertible = Sh.make-invertible
    (PShR.is-invertible.inv θ-psh-invertible)
    (PShR.is-invertible.invl θ-psh-invertible)
    (PShR.is-invertible.invr θ-psh-invertible)
```

Finally, `θ`{.Agda} commutes with the projections: both
$q_1 \circ \theta$ and the sheafification of `pc1`{.Agda} are maps
out of a sheafification into a sheaf which agree on generators, so
they are equal by the uniqueness half of the universal property —
definitionally on both sides.

```agda
  θ-pc1 : Sheafification {C = C} {J = J} .F₁ pc1 ≡ q1 PShR.∘ θ
  θ-pc1 = S.unique LX.Sheafify LX.Sheafify-is-sheaf
    (S.unit PShR.∘ pc1) (q1 PShR.∘ θ) λ U x → refl

  θ-pc2 : Sheafification {C = C} {J = J} .F₁ pc2 ≡ q2 PShR.∘ θ
  θ-pc2 = S.unique LY.Sheafify LY.Sheafify-is-sheaf
    (S.unit PShR.∘ pc2) (q2 PShR.∘ θ) λ U x → refl
```

## Pullback preservation

An abstract pullback square in $\psh(\cC)$ compares to the canonical
one by an invertible map, since both are pullbacks of the same
cospan; the sheafification functor preserves that invertibility, and
composing with `θ`{.Agda} lands in $Q$. The composite is the
canonical comparison of the sheafified square with the sheaf
pullback $Q$, so `invertible≃pullback`{.Agda} concludes.

```agda
module _ {P X Y Z : Functor (C ^op) (Sets ℓ)}
         {p1 : P => X} {f : X => Z} {p2 : P => Y} {g : Y => Z}
         (pb : is-pullback (PSh ℓ C) p1 f p2 g)
  where
  private
    L : Functor (PSh ℓ C) (Sheaves J ℓ)
    L = Sheafification {C = C} {J = J}

    module L = Functor L

    k : P => Pc f g
    k = Pc-is-pullback f g .universal (pb .square)

    k-invertible : PShR.is-invertible k
    k-invertible = pullback-unique (Pc-is-pullback f g) pb

    Lsq : L.₁ f PShR.∘ L.₁ p1 ≡ L.₁ g PShR.∘ L.₁ p2
    Lsq = sym (L.F-∘ f p1) ∙∙ ap L.₁ (pb .square) ∙∙ L.F-∘ g p2

    cmp : Sh.Hom (L.₀ P) (Q f g , Q-is-sheaf f g)
    cmp = θ f g PShR.∘ L.₁ k

    cmp-invertible
      : Sh.is-invertible {a = L.₀ P} {b = Q f g , Q-is-sheaf f g} cmp
    cmp-invertible = Sh.invertible-∘
      (θ-sh-invertible f g)
      (F-map-invertible L k-invertible)

    c1 : q1 f g PShR.∘ cmp ≡ L.₁ p1
    c1 = PShR.pulll (sym (θ-pc1 f g))
      ∙∙ sym (L.F-∘ (pc1 f g) k)
      ∙∙ ap L.₁ (Pc-is-pullback f g .p₁∘universal {p = pb .square})

    c2 : q2 f g PShR.∘ cmp ≡ L.₁ p2
    c2 = PShR.pulll (sym (θ-pc2 f g))
      ∙∙ sym (L.F-∘ (pc2 f g) k)
      ∙∙ ap L.₁ (Pc-is-pullback f g .p₂∘universal {p = pb .square})

  Sheafification-pres-pullback
    : is-pullback (Sheaves J ℓ)
        {X = L.₀ X} {Z = L.₀ Z} {Y = L.₀ Y} {P = L.₀ P}
        (L.₁ p1) (L.₁ f) (L.₁ p2) (L.₁ g)
  Sheafification-pres-pullback = Equiv.to
    (invertible≃pullback {p' = L.₀ P} (Q-is-pullback f g) Lsq)
    (subst (Sh.is-invertible {a = L.₀ P} {b = Q f g , Q-is-sheaf f g})
      (Q-is-pullback f g .unique {P' = L.₀ P} {p = Lsq} c1 c2)
      cmp-invertible)
```

## Left exactness, and the topos of sheaves

Terminal objects were [[already
preserved|lex-sheafification]]; together with pullback preservation,
the sheafification functor is left exact.

```agda
Sheafification-is-lex : is-lex (Sheafification {C = C} {J = J})
Sheafification-is-lex .is-lex.pres-⊤ {T} term =
  Cat.Site.Sheafification.Lex.Sheafification-pres-⊤ J T term
Sheafification-is-lex .is-lex.pres-pullback pb =
  Sheafification-pres-pullback pb
```

All the fields of the `Topos`{.Agda} record are now in hand: sheaves
on a site are a reflective subcategory of presheaves, the inclusion
is fully faithful with definitionally-identity action on morphisms,
and the reflector is lex.

```agda
Sheaves-topos : Topos ℓ Sh[ C , J ]
Sheaves-topos .Topos.site = C
Sheaves-topos .Topos.ι = forget-sheaf J ℓ
Sheaves-topos .Topos.has-ff = id-equiv
Sheaves-topos .Topos.L = Sheafification {C = C} {J = J}
Sheaves-topos .Topos.L-lex = Sheafification-is-lex
Sheaves-topos .Topos.L⊣ι = Sheafification⊣ι {C = C} {J = J}
```

In particular, the gros topoi of this development — categories of
sheaves `Sh[ C , J ]`{.Agda} over the sites of smooth, formally
extended, and super Cartesian spaces — are Grothendieck topoi in the
official, structural sense of the word: the diagram of adjunctions
they participate in bottoms out in an honest lex reflection of
presheaves.
