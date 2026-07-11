<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Reflection.Induction

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Cat.Diagram.Terminal
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Fin using (Fin ; Fin-absurd)

import Cat.Instances.Presheaf.Cohesive
import Cat.Instances.FormalSmoothSets
import Algebra.Ring.Grassmann as G
import Algebra.Ring.Polynomial
import Algebra.Ring.Center as Z
import Cat.Reasoning

open is-ring-hom
open Precategory
open Terminal
```
-->

```agda
module Cat.Instances.SuperFormalSmoothSets {ℓ} (R : CRing ℓ) where
```

<!--
```agda
open Algebra.Ring.Polynomial R

private
  module CR = Cat.Reasoning (CRings ℓ)
  module Th = Cat.Instances.FormalSmoothSets R

  ∘-is-ring-hom
    : ∀ {A B C : Ring ℓ} {f : ⌞ B ⌟ → ⌞ C ⌟} {g : ⌞ A ⌟ → ⌞ B ⌟}
    → is-ring-hom (B .snd) (C .snd) f
    → is-ring-hom (A .snd) (B .snd) g
    → is-ring-hom (A .snd) (C .snd) (f ⊙ g)
  ∘-is-ring-hom {f = f} {g} hf hg .pres-id =
    ap f (hg .pres-id) ∙ hf .pres-id
  ∘-is-ring-hom {f = f} {g} hf hg .pres-+ x y =
    ap f (hg .pres-+ x y) ∙ hf .pres-+ _ _
  ∘-is-ring-hom {f = f} {g} hf hg .pres-* x y =
    ap f (hg .pres-* x y) ∙ hf .pres-* _ _
```
-->

# Super formal smooth sets {defines="super-formal-smooth-sets super-thickening"}

The paper's site combines *all three* kinds of direction at once:
ordinary coordinates, [[infinitesimal thickenings|dual-numbers]],
and anticommuting odd directions. Since the [[Grassmann
algebra|grassmann-algebra]] is available over an arbitrary
commutative base, the combination costs nothing: the function
algebra of the super formal Cartesian space $\bA^{n,k|q}$ is the
Grassmann algebra on $q$ odd generators over the $k$-fold
[[thickened|formal-smooth-set]] polynomial algebra in $n$
variables.

```agda
data SupThAff : Type ℓ where
  𝔸[_,_∣_] : Nat → Nat → Nat → SupThAff

O : SupThAff → Ring ℓ
O 𝔸[ n , k ∣ q ] = G.Λ[q] (Th.O∙ n k) q

σO : ∀ x → ⌞ O x ⌟ → ⌞ O x ⌟
σO 𝔸[ n , k ∣ q ] = G.σ-parity (Th.O∙ n k) q

structF : ∀ x → ⌞ R ⌟ → ⌞ O x ⌟
structF 𝔸[ n , k ∣ q ] a = G.con (Th.structO n k .∫Hom.fst a)

structF-is-ring-hom
  : ∀ x → is-ring-hom (R .snd .CRing-on.has-ring-on) (O x .snd) (structF x)
structF-is-ring-hom 𝔸[ n , k ∣ q ] .pres-id =
  ap G.con (Th.structO n k .∫Hom.snd .pres-id)
structF-is-ring-hom 𝔸[ n , k ∣ q ] .pres-+ a b =
  ap G.con (Th.structO n k .∫Hom.snd .pres-+ a b) ∙ G.con-+ _ _
structF-is-ring-hom 𝔸[ n , k ∣ q ] .pres-* a b =
  ap G.con (Th.structO n k .∫Hom.snd .pres-* a b) ∙ G.con-* _ _

σO-is-ring-hom : ∀ x → is-ring-hom (O x .snd) (O x .snd) (σO x)
σO-is-ring-hom 𝔸[ n , k ∣ q ] = G.σ-is-ring-hom (Th.O∙ n k) q
```

Morphisms are parity-respecting algebra maps under $R$, exactly as
for the [[unthickened super site|super-cartesian-space]].

```agda
record SupThHom (x y : SupThAff) : Type ℓ where
  no-eta-equality
  field
    fun      : ⌞ O y ⌟ → ⌞ O x ⌟
    fun-hom  : is-ring-hom (O y .snd) (O x .snd) fun
    commutes : ∀ a → fun (structF y a) ≡ structF x a
    parity   : ∀ g → fun (σO y g) ≡ σO x (fun g)
```

<!--
```agda
open SupThHom

private unquoteDecl eqv = declare-record-iso eqv (quote SupThHom)

SupThHom-path
  : ∀ {x y} {f g : SupThHom x y} → (∀ a → f .fun a ≡ g .fun a) → f ≡ g
SupThHom-path {x} {y} {f} {g} p i .fun a = p a i
SupThHom-path {x} {y} {f} {g} p i .fun-hom =
  is-prop→pathp
    (λ i → hlevel {T = is-ring-hom (O y .snd) (O x .snd) (λ a → p a i)} 1)
    (f .fun-hom) (g .fun-hom) i
SupThHom-path {x} {y} {f} {g} p i .commutes a =
  is-prop→pathp
    (λ i → Ring-on.has-is-set (O x .snd) (p (structF y a) i) (structF x a))
    (f .commutes a) (g .commutes a) i
SupThHom-path {x} {y} {f} {g} p i .parity g' =
  is-prop→pathp
    (λ i → Ring-on.has-is-set (O x .snd) (p (σO y g') i) (σO x (p g' i)))
    (f .parity g') (g .parity g') i

SupThHom-set : ∀ x y → is-set (SupThHom x y)
SupThHom-set x y = Iso→is-hlevel 2 eqv $ Σ-is-hlevel 2
  (Π-is-hlevel 2 λ _ → Ring-on.has-is-set (O x .snd)) λ f →
  Σ-is-hlevel 2 (is-prop→is-set (hlevel 1)) λ _ →
  Σ-is-hlevel 2
    (Π-is-hlevel 2 λ a →
      is-prop→is-set (Ring-on.has-is-set (O x .snd) _ _)) λ _ →
  Π-is-hlevel 2 λ g →
    is-prop→is-set (Ring-on.has-is-set (O x .snd) _ _)
```
-->

```agda
SupThCartSp : Precategory ℓ ℓ
SupThCartSp .Ob = SupThAff
SupThCartSp .Hom = SupThHom
SupThCartSp .Hom-set = SupThHom-set
SupThCartSp .id .fun a = a
SupThCartSp .id .fun-hom = record
  { pres-id = refl ; pres-+ = λ _ _ → refl ; pres-* = λ _ _ → refl }
SupThCartSp .id .commutes a = refl
SupThCartSp .id .parity g = refl
SupThCartSp ._∘_ f g .fun = g .fun ⊙ f .fun
SupThCartSp ._∘_ {x} {y} {z} f g .fun-hom =
  ∘-is-ring-hom {A = O z} {B = O y} {C = O x} (g .fun-hom) (f .fun-hom)
SupThCartSp ._∘_ f g .commutes a =
  ap (g .fun) (f .commutes a) ∙ g .commutes a
SupThCartSp ._∘_ f g .parity h =
  ap (g .fun) (f .parity h) ∙ g .parity (f .fun h)
SupThCartSp .idr f = SupThHom-path λ _ → refl
SupThCartSp .idl f = SupThHom-path λ _ → refl
SupThCartSp .assoc f g h = SupThHom-path λ _ → refl
```

## The terminal probe

The completely trivial probe — no coordinates, no thickening, no
odd directions — is terminal, by the same composite of universal
properties as before: its base algebra is the polynomial ring on no
variables, so both the polynomial and the Grassmann extension have
no choices to make.

<!--
```agda
private
  no-vars : ∀ {C : CRing ℓ} → Lift ℓ (Fin 0) → ⌞ C ⌟
  no-vars v = absurd (Fin-absurd (v .Lift.lower))

module _ (x : SupThAff) where
  private
    module Ox = Ring-on (O x .snd)

    R∅ : CRing ℓ
    R∅ = R[ Lift ℓ (Fin 0) ]

    ZOx : CRing ℓ
    ZOx = Z.Centre (O x)

    φZ : CR.Hom R ZOx
    φZ .∫Hom.fst a = structF x a , cent a where
      cent : ∀ a → Z.is-central (O x) (structF x a)
      cent a y = lemma x a y where
        lemma : ∀ x a y →
          Ring-on._*_ (O x .snd) (structF x a) y
          ≡ Ring-on._*_ (O x .snd) y (structF x a)
        lemma 𝔸[ n , k ∣ q ] a y = G.con-comm _ y
    φZ .∫Hom.snd .pres-id =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-id)
    φZ .∫Hom.snd .pres-+ a b =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-+ a b)
    φZ .∫Hom.snd .pres-* a b =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-* a b)

    ψ : ⌞ R∅ ⌟ → ⌞ O x ⌟
    ψ z = extendᵖ φZ (no-vars {C = ZOx}) z .fst

    ψ-hom : is-ring-hom (R∅ .snd .CRing-on.has-ring-on) (O x .snd) ψ
    ψ-hom = ∘-is-ring-hom
      {A = R∅ .fst , R∅ .snd .CRing-on.has-ring-on}
      {B = ZOx .fst , ZOx .snd .CRing-on.has-ring-on}
      {C = O x}
      (Z.centre-proj-is-ring-hom (O x))
      (extend φZ (no-vars {C = ZOx}) .∫Hom.snd)

    ψ-central : ∀ z y → Ox._*_ (ψ z) y ≡ Ox._*_ y (ψ z)
    ψ-central z = extendᵖ φZ (no-vars {C = ZOx}) z .snd

    σ-fixes : ∀ z → σO x (ψ z) ≡ ψ z
    σ-fixes = Poly-elim-prop _
      (λ _ → Ox.has-is-set _ _)
      (λ v → absurd (Fin-absurd (v .Lift.lower)))
      (λ a → fixes-struct x a)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-+ _ _
        ∙ ap₂ Ox._+_ ihu ihv)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-* _ _
        ∙ ap₂ Ox._*_ ihu ihv)
      (λ u ih →
          is-ring-hom.pres-neg (σO-is-ring-hom x)
        ∙ ap Ox.-_ ih)
      where
      fixes-struct : ∀ x a → σO x (structF x a) ≡ structF x a
      fixes-struct 𝔸[ n , k ∣ q ] a = refl

  centre-hom : SupThHom x 𝔸[ 0 , 0 ∣ 0 ]
  centre-hom .fun = G.grassmann-extend R∅ 0 (O x) ψ ψ-hom ψ-central
    (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
    (λ i → absurd (Fin-absurd i))
  centre-hom .fun-hom = G.grassmann-extend-is-ring-hom R∅ 0 (O x)
    ψ ψ-hom ψ-central
    (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
    (λ i → absurd (Fin-absurd i))
  centre-hom .commutes a = refl
  centre-hom .parity = G.Grassmann-elim-prop R∅ 0 _
    (λ _ → Ox.has-is-set _ _)
    (λ i → absurd (Fin-absurd i))
    (λ z → sym (σ-fixes z))
    (λ u ihu v ihv → ap₂ Ox._+_ ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-+ _ _))
    (λ u ihu v ihv → ap₂ Ox._*_ ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-* _ _))
    (λ u ih → ap Ox.-_ ih
      ∙ sym (is-ring-hom.pres-neg (σO-is-ring-hom x)))

  centre-unique : (h : SupThHom x 𝔸[ 0 , 0 ∣ 0 ]) → centre-hom ≡ h
  centre-unique h = SupThHom-path λ a →
    sym (G.grassmann-extend-unique R∅ 0 (O x) ψ ψ-hom ψ-central
      (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
      (λ i → absurd (Fin-absurd i))
      (h .fun) (h .fun-hom) hcon (λ i → absurd (Fin-absurd i)) a)
    where
    Gcon-hom : is-ring-hom
      (R∅ .snd .CRing-on.has-ring-on) (O 𝔸[ 0 , 0 ∣ 0 ] .snd) G.con
    Gcon-hom .pres-id = refl
    Gcon-hom .pres-+ u v = G.con-+ u v
    Gcon-hom .pres-* u v = G.con-* u v

    hcon : ∀ z → h .fun (G.con z) ≡ ψ z
    hcon = Poly-elim-prop _
      (λ _ → Ox.has-is-set _ _)
      (λ v → absurd (Fin-absurd (v .Lift.lower)))
      (λ a → h .commutes a)
      (λ u ihu v ihv →
          ap (h .fun) (Gcon-hom .pres-+ u v)
        ∙ h .fun-hom .pres-+ _ _
        ∙ ap₂ Ox._+_ ihu ihv)
      (λ u ihu v ihv →
          ap (h .fun) (Gcon-hom .pres-* u v)
        ∙ h .fun-hom .pres-* _ _
        ∙ ap₂ Ox._*_ ihu ihv)
      (λ u ih →
          ap (h .fun) (is-ring-hom.pres-neg Gcon-hom)
        ∙ is-ring-hom.pres-neg (h .fun-hom)
        ∙ ap Ox.-_ ih)
```
-->

```agda
pt-terminal : Terminal SupThCartSp
pt-terminal .top = 𝔸[ 0 , 0 ∣ 0 ]
pt-terminal .has⊤ x .centre = centre-hom x
pt-terminal .has⊤ x .paths = centre-unique x
```

**Super formal smooth sets** are the presheaves on this site; with
a terminal probe, the topos is cohesive — this is the ambient
$\infty$-topos of the paper, in its $1$-categorical shadow, with
every column of the probe table present at once.

```agda
SupThSmthSet : Precategory (lsuc ℓ) ℓ
SupThSmthSet = PSh ℓ SupThCartSp

module SupThSmthSet-cohesion =
  Cat.Instances.Presheaf.Cohesive SupThCartSp pt-terminal
```

## Odd plots, with thickenings present

The [[odd-plot description|odd-plots]] of spinor fields carries
over verbatim: plots of the purely odd space by *any* super formal
probe — coordinates and infinitesimals included — are multiplets of
odd, anticommuting, square-zero functions.

```agda
Odd-multiplet : SupThAff → Nat → Type ℓ
Odd-multiplet x s =
  Σ[ t ∈ (Fin s → ⌞ O x ⌟) ]
    ( (∀ i j → Ox._*_ (t i) (t j) ≡ Ox.-_ (Ox._*_ (t j) (t i)))
    × (∀ i → Ox._*_ (t i) (t i) ≡ Ox.0r)
    × (∀ i → σO x (t i) ≡ Ox.-_ (t i)))
  where module Ox = Ring-on (O x .snd)
```

<!--
```agda
module _ (x : SupThAff) (s : Nat) where
  private
    module Ox = Ring-on (O x .snd)

    R∅ : CRing ℓ
    R∅ = R[ Lift ℓ (Fin 0) ]

    ZOx : CRing ℓ
    ZOx = Z.Centre (O x)

    φZ : CR.Hom R ZOx
    φZ .∫Hom.fst a = structF x a , cent a where
      cent : ∀ a → Z.is-central (O x) (structF x a)
      cent a y = lemma x a y where
        lemma : ∀ x a y →
          Ring-on._*_ (O x .snd) (structF x a) y
          ≡ Ring-on._*_ (O x .snd) y (structF x a)
        lemma 𝔸[ n , k ∣ q ] a y = G.con-comm _ y
    φZ .∫Hom.snd .pres-id =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-id)
    φZ .∫Hom.snd .pres-+ a b =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-+ a b)
    φZ .∫Hom.snd .pres-* a b =
      Σ-prop-path (Z.is-central-is-prop (O x))
        (structF-is-ring-hom x .pres-* a b)

    ψ : ⌞ R∅ ⌟ → ⌞ O x ⌟
    ψ z = extendᵖ φZ (no-vars {C = ZOx}) z .fst

    ψ-hom : is-ring-hom (R∅ .snd .CRing-on.has-ring-on) (O x .snd) ψ
    ψ-hom = ∘-is-ring-hom
      {A = R∅ .fst , R∅ .snd .CRing-on.has-ring-on}
      {B = ZOx .fst , ZOx .snd .CRing-on.has-ring-on}
      {C = O x}
      (Z.centre-proj-is-ring-hom (O x))
      (extend φZ (no-vars {C = ZOx}) .∫Hom.snd)

    ψ-central : ∀ z y → Ox._*_ (ψ z) y ≡ Ox._*_ y (ψ z)
    ψ-central z = extendᵖ φZ (no-vars {C = ZOx}) z .snd

    σ-fixes : ∀ z → σO x (ψ z) ≡ ψ z
    σ-fixes = Poly-elim-prop _
      (λ _ → Ox.has-is-set _ _)
      (λ v → absurd (Fin-absurd (v .Lift.lower)))
      (λ a → fixes-struct x a)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-+ _ _
        ∙ ap₂ Ox._+_ ihu ihv)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-* _ _
        ∙ ap₂ Ox._*_ ihu ihv)
      (λ u ih →
          is-ring-hom.pres-neg (σO-is-ring-hom x)
        ∙ ap Ox.-_ ih)
      where
      fixes-struct : ∀ x a → σO x (structF x a) ≡ structF x a
      fixes-struct 𝔸[ n , k ∣ q ] a = refl

  odd-to : SupThHom x 𝔸[ 0 , 0 ∣ s ] → Odd-multiplet x s
  odd-to h = (λ i → h .fun (G.θ i)) , anti , sq , odd where
    anti : ∀ i j
      → Ox._*_ (h .fun (G.θ i)) (h .fun (G.θ j))
      ≡ Ox.-_ (Ox._*_ (h .fun (G.θ j)) (h .fun (G.θ i)))
    anti i j =
        sym (h .fun-hom .pres-* (G.θ i) (G.θ j))
      ∙ ap (h .fun) (G.θ-anticomm i j)
      ∙ is-ring-hom.pres-neg (h .fun-hom)
      ∙ ap Ox.-_ (h .fun-hom .pres-* (G.θ j) (G.θ i))

    sq : ∀ i → Ox._*_ (h .fun (G.θ i)) (h .fun (G.θ i)) ≡ Ox.0r
    sq i =
        sym (h .fun-hom .pres-* (G.θ i) (G.θ i))
      ∙ ap (h .fun) (G.θ-sq i)
      ∙ is-ring-hom.pres-0 (h .fun-hom)

    odd : ∀ i → σO x (h .fun (G.θ i)) ≡ Ox.-_ (h .fun (G.θ i))
    odd i =
        sym (h .parity (G.θ i))
      ∙ is-ring-hom.pres-neg (h .fun-hom)

  odd-from : Odd-multiplet x s → SupThHom x 𝔸[ 0 , 0 ∣ s ]
  odd-from (t , anti , sq , odd) .fun =
    G.grassmann-extend R∅ s (O x) ψ ψ-hom ψ-central t anti sq
  odd-from (t , anti , sq , odd) .fun-hom =
    G.grassmann-extend-is-ring-hom R∅ s (O x) ψ ψ-hom ψ-central t anti sq
  odd-from (t , anti , sq , odd) .commutes a = refl
  odd-from (t , anti , sq , odd) .parity = G.Grassmann-elim-prop R∅ s _
    (λ _ → Ox.has-is-set _ _)
    (λ i → sym (odd i))
    (λ z → sym (σ-fixes z))
    (λ u ihu v ihv → ap₂ Ox._+_ ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-+ _ _))
    (λ u ihu v ihv → ap₂ Ox._*_ ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-* _ _))
    (λ u ih → ap Ox.-_ ih
      ∙ sym (is-ring-hom.pres-neg (σO-is-ring-hom x)))
```
-->

```agda
  odd-plots : SupThHom x 𝔸[ 0 , 0 ∣ s ] ≃ Odd-multiplet x s
  odd-plots = Iso→Equiv (odd-to , iso odd-from rinv linv) where
    rinv : ∀ d → odd-to (odd-from d) ≡ d
    rinv (t , _) = Σ-prop-path
      (λ t' → ×-is-hlevel 1
        (Π-is-hlevel 1 λ i → Π-is-hlevel 1 λ j → Ox.has-is-set _ _)
        (×-is-hlevel 1
          (Π-is-hlevel 1 λ i → Ox.has-is-set _ _)
          (Π-is-hlevel 1 λ i → Ox.has-is-set _ _)))
      refl

    linv : ∀ h → odd-from (odd-to h) ≡ h
    linv h = SupThHom-path λ a →
      sym (G.grassmann-extend-unique R∅ s (O x) ψ ψ-hom ψ-central
        (odd-to h .fst) (odd-to h .snd .fst)
        (odd-to h .snd .snd .fst)
        (h .fun) (h .fun-hom) hcon (λ i → refl) a)
      where
      Gcon-hom : is-ring-hom
        (R∅ .snd .CRing-on.has-ring-on) (O 𝔸[ 0 , 0 ∣ s ] .snd) G.con
      Gcon-hom .pres-id = refl
      Gcon-hom .pres-+ u v = G.con-+ u v
      Gcon-hom .pres-* u v = G.con-* u v

      hcon : ∀ z → h .fun (G.con z) ≡ ψ z
      hcon = Poly-elim-prop _
        (λ _ → Ox.has-is-set _ _)
        (λ v → absurd (Fin-absurd (v .Lift.lower)))
        (λ a → h .commutes a)
        (λ u ihu v ihv →
            ap (h .fun) (Gcon-hom .pres-+ u v)
          ∙ h .fun-hom .pres-+ _ _
          ∙ ap₂ Ox._+_ ihu ihv)
        (λ u ihu v ihv →
            ap (h .fun) (Gcon-hom .pres-* u v)
          ∙ h .fun-hom .pres-* _ _
          ∙ ap₂ Ox._*_ ihu ihv)
        (λ u ih →
            ap (h .fun) (is-ring-hom.pres-neg Gcon-hom)
          ∙ is-ring-hom.pres-neg (h .fun-hom)
          ∙ ap Ox.-_ ih)
```
