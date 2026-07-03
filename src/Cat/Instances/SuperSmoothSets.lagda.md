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
module Cat.Instances.SuperSmoothSets {ℓ} (R : CRing ℓ) where
```

<!--
```agda
open Algebra.Ring.Polynomial R

private
  module CR = Cat.Reasoning (CRings ℓ)
  module R' = CRing-on (R .snd)

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

# Super smooth sets {defines="super-smooth-sets super-cartesian-space"}

The paper's (19)–(20): the site of **super Cartesian spaces**
$\bR^{n|q}$ has, as function algebras, the tensor products of smooth
functions with [[Grassmann algebras|grassmann-algebra]] — and since
the Grassmann construction is available over *any* commutative base,
the tensor product is simply the Grassmann algebra over the
[[polynomial ring|polynomial-ring]]:
$\cO(\bA^{n|q}) = \Lambda_{R[x_1 \ldots x_n]}[\theta_1 \ldots
\theta_q]$. Morphisms are algebra maps under $R$ that respect the
$\mathbb{Z}/2$-grading, i.e. commute with the parity involutions.

```agda
data SupAff : Type ℓ where
  𝔸[_∣_] : Nat → Nat → SupAff

O : SupAff → Ring ℓ
O 𝔸[ n ∣ q ] = G.Λ[q] (R[ Lift ℓ (Fin n) ]) q

σO : ∀ x → ⌞ O x ⌟ → ⌞ O x ⌟
σO 𝔸[ n ∣ q ] = G.σ-parity (R[ Lift ℓ (Fin n) ]) q

structF : ∀ x → ⌞ R ⌟ → ⌞ O x ⌟
structF 𝔸[ n ∣ q ] a = G.con (con a)

structF-is-ring-hom
  : ∀ x → is-ring-hom (R .snd .CRing-on.has-ring-on) (O x .snd) (structF x)
structF-is-ring-hom 𝔸[ n ∣ q ] .pres-id = refl
structF-is-ring-hom 𝔸[ n ∣ q ] .pres-+ a b =
  ap G.con (con-+ a b) ∙ G.con-+ _ _
structF-is-ring-hom 𝔸[ n ∣ q ] .pres-* a b =
  ap G.con (con-* a b) ∙ G.con-* _ _

σO-is-ring-hom : ∀ x → is-ring-hom (O x .snd) (O x .snd) (σO x)
σO-is-ring-hom 𝔸[ n ∣ q ] = G.σ-is-ring-hom (R[ Lift ℓ (Fin n) ]) q
```

A morphism of super spaces is, dually, a parity-respecting algebra
map of function rings under $R$.

```agda
record SupHom (x y : SupAff) : Type ℓ where
  no-eta-equality
  field
    fun      : ⌞ O y ⌟ → ⌞ O x ⌟
    fun-hom  : is-ring-hom (O y .snd) (O x .snd) fun
    commutes : ∀ a → fun (structF y a) ≡ structF x a
    parity   : ∀ g → fun (σO y g) ≡ σO x (fun g)
```

<!--
```agda
open SupHom

private unquoteDecl eqv = declare-record-iso eqv (quote SupHom)

SupHom-path
  : ∀ {x y} {f g : SupHom x y} → (∀ a → f .fun a ≡ g .fun a) → f ≡ g
SupHom-path {x} {y} {f} {g} p i .fun a = p a i
SupHom-path {x} {y} {f} {g} p i .fun-hom =
  is-prop→pathp
    (λ i → hlevel {T = is-ring-hom (O y .snd) (O x .snd) (λ a → p a i)} 1)
    (f .fun-hom) (g .fun-hom) i
SupHom-path {x} {y} {f} {g} p i .commutes a =
  is-prop→pathp
    (λ i → Ring-on.has-is-set (O x .snd) (p (structF y a) i) (structF x a))
    (f .commutes a) (g .commutes a) i
SupHom-path {x} {y} {f} {g} p i .parity g' =
  is-prop→pathp
    (λ i → Ring-on.has-is-set (O x .snd) (p (σO y g') i) (σO x (p g' i)))
    (f .parity g') (g .parity g') i

SupHom-set : ∀ x y → is-set (SupHom x y)
SupHom-set x y = Iso→is-hlevel 2 eqv $ Σ-is-hlevel 2
  (Π-is-hlevel 2 λ _ → Ring-on.has-is-set (O x .snd)) λ f →
  Σ-is-hlevel 2 (is-prop→is-set (hlevel 1)) λ _ →
  Σ-is-hlevel 2
    (Π-is-hlevel 2 λ a →
      is-prop→is-set (Ring-on.has-is-set (O x .snd) _ _)) λ _ →
  Π-is-hlevel 2 λ g →
    is-prop→is-set (Ring-on.has-is-set (O x .snd) _ _)
```
-->

Because the underlying data of a morphism is a bare function, the
category laws hold definitionally.

```agda
SupCartSp : Precategory ℓ ℓ
SupCartSp .Ob = SupAff
SupCartSp .Hom = SupHom
SupCartSp .Hom-set = SupHom-set
SupCartSp .id .fun a = a
SupCartSp .id .fun-hom = record
  { pres-id = refl ; pres-+ = λ _ _ → refl ; pres-* = λ _ _ → refl }
SupCartSp .id .commutes a = refl
SupCartSp .id .parity g = refl
SupCartSp ._∘_ f g .fun = g .fun ⊙ f .fun
SupCartSp ._∘_ {x} {y} {z} f g .fun-hom =
  ∘-is-ring-hom {A = O z} {B = O y} {C = O x} (g .fun-hom) (f .fun-hom)
SupCartSp ._∘_ f g .commutes a =
  ap (g .fun) (f .commutes a) ∙ g .commutes a
SupCartSp ._∘_ f g .parity h =
  ap (g .fun) (f .parity h) ∙ g .parity (f .fun h)
SupCartSp .idr f = SupHom-path λ _ → refl
SupCartSp .idl f = SupHom-path λ _ → refl
SupCartSp .assoc f g h = SupHom-path λ _ → refl
```

## The terminal super point

The super point $\bA^{0|0}$ is terminal: its function algebra is
generated by the constants, so an algebra map out of it under $R$ has
no choices to make. The proof composes the universal properties of
the polynomial ring and the Grassmann algebra, routed through the
[[centre|centre-of-a-ring]] of the target — constants are central by
the `con-comm`{.Agda} relation, so the polynomial part of the
extension lands in a commutative ring, as it must.

<!--
```agda
private
  no-vars : ∀ {C : CRing ℓ} → Lift ℓ (Fin 0) → ⌞ C ⌟
  no-vars v = absurd (Fin-absurd (v .Lift.lower))

module _ (x : SupAff) where
  private
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
        lemma 𝔸[ n ∣ q ] a y = G.con-comm (con a) y
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

    ψ-central : ∀ z y →
      Ring-on._*_ (O x .snd) (ψ z) y ≡ Ring-on._*_ (O x .snd) y (ψ z)
    ψ-central z = extendᵖ φZ (no-vars {C = ZOx}) z .snd
```
-->

```agda
  centre-hom : SupHom x 𝔸[ 0 ∣ 0 ]
  centre-hom .fun = G.grassmann-extend R∅ 0 (O x) ψ ψ-hom ψ-central
    (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
  centre-hom .fun-hom = G.grassmann-extend-is-ring-hom R∅ 0 (O x)
    ψ ψ-hom ψ-central (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
  centre-hom .commutes a = refl
  centre-hom .parity = G.Grassmann-elim-prop R∅ 0 _
    (λ _ → Ring-on.has-is-set (O x .snd) _ _)
    (λ i → absurd (Fin-absurd i))
    (λ z → sym (σ-fixes z))
    (λ u ihu v ihv →
        ap₂ (Ring-on._+_ (O x .snd)) ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-+ _ _))
    (λ u ihu v ihv →
        ap₂ (Ring-on._*_ (O x .snd)) ihu ihv
      ∙ sym (σO-is-ring-hom x .pres-* _ _))
    (λ u ih →
        ap (Ring-on.-_ (O x .snd)) ih
      ∙ sym (is-ring-hom.pres-neg (σO-is-ring-hom x)))
    where
    σ-fixes : ∀ z → σO x (ψ z) ≡ ψ z
    σ-fixes = Poly-elim-prop _
      (λ _ → Ring-on.has-is-set (O x .snd) _ _)
      (λ v → absurd (Fin-absurd (v .Lift.lower)))
      (λ a → fixes-struct x a)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-+ _ _
        ∙ ap₂ (Ring-on._+_ (O x .snd)) ihu ihv)
      (λ u ihu v ihv →
          σO-is-ring-hom x .pres-* _ _
        ∙ ap₂ (Ring-on._*_ (O x .snd)) ihu ihv)
      (λ u ih →
          is-ring-hom.pres-neg (σO-is-ring-hom x)
        ∙ ap (Ring-on.-_ (O x .snd)) ih)
      where
      fixes-struct : ∀ x a → σO x (structF x a) ≡ structF x a
      fixes-struct 𝔸[ n ∣ q ] a = refl
```

Uniqueness routes any competitor through both universal properties.

```agda
  centre-unique : (h : SupHom x 𝔸[ 0 ∣ 0 ]) → centre-hom ≡ h
  centre-unique h = SupHom-path λ a →
    sym (G.grassmann-extend-unique R∅ 0 (O x) ψ ψ-hom ψ-central
      (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i)) (λ i → absurd (Fin-absurd i))
      (h .fun) (h .fun-hom) hcon (λ i → absurd (Fin-absurd i)) a)
    where
    Gcon-hom : is-ring-hom
      (R∅ .snd .CRing-on.has-ring-on) (O 𝔸[ 0 ∣ 0 ] .snd) G.con
    Gcon-hom .pres-id = refl
    Gcon-hom .pres-+ u v = G.con-+ u v
    Gcon-hom .pres-* u v = G.con-* u v

    hcon : ∀ z → h .fun (G.con z) ≡ ψ z
    hcon = Poly-elim-prop _
      (λ _ → Ring-on.has-is-set (O x .snd) _ _)
      (λ v → absurd (Fin-absurd (v .Lift.lower)))
      (λ a → h .commutes a)
      (λ u ihu v ihv →
          ap (h .fun) (Gcon-hom .pres-+ u v)
        ∙ h .fun-hom .pres-+ _ _
        ∙ ap₂ (Ring-on._+_ (O x .snd)) ihu ihv)
      (λ u ihu v ihv →
          ap (h .fun) (Gcon-hom .pres-* u v)
        ∙ h .fun-hom .pres-* _ _
        ∙ ap₂ (Ring-on._*_ (O x .snd)) ihu ihv)
      (λ u ih →
          ap (h .fun) (is-ring-hom.pres-neg Gcon-hom)
        ∙ is-ring-hom.pres-neg (h .fun-hom)
        ∙ ap (Ring-on.-_ (O x .snd)) ih)

pt-terminal : Terminal SupCartSp
pt-terminal .top = 𝔸[ 0 ∣ 0 ]
pt-terminal .has⊤ x .centre = centre-hom x
pt-terminal .has⊤ x .paths = centre-unique x
```

**Super smooth sets** are the presheaves on this site — the paper's
(20), with the trivial coverage as before — and since the site has a
terminal probe, the topos is cohesive.

```agda
SupSmthSet : Precategory (lsuc ℓ) ℓ
SupSmthSet = PSh ℓ SupCartSp

module SupSmthSet-cohesion =
  Cat.Instances.Presheaf.Cohesive SupCartSp pt-terminal
```

The odd-plot description of spinor fields (21) — plots of $\Pi S$ by
$\bA^{0|1}$ are odd sections — needs a concrete spinor bundle and
remains future work, as do super-thickenings combining this site with
the infinitesimal one.
