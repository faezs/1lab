<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Algebra.Ring.Commutative
open import Algebra.Ring using (is-ring-hom)

open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Fin using (Fin ; fzero ; fin-view ; Fin-view ; Fin-absurd)

import Cat.Instances.Presheaf.Cohesive
import Algebra.Ring.DualNumbers as Dual
import Algebra.Ring.Polynomial
import Cat.Reasoning

open Precategory
open Terminal
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.FormalSmoothSets {ℓ} (R : CRing ℓ) where
```

<!--
```agda
open Algebra.Ring.Polynomial R

private
  module CR = Cat.Reasoning (CRings ℓ)
```
-->

# Formal smooth sets and the Kock–Lawvere theorem {defines="formal-smooth-sets thickened-cartesian-space"}

This module assembles, constructively and over an arbitrary
commutative [[ring]] $R$, the site that Schreiber's *Higher Topos
Theory in Physics* calls $\rm{ThCrtSp}$ — **infinitesimally thickened
Cartesian spaces** — and its gros topos of *formal smooth sets*, in
which the [[tangent bundle|formal-sets]] is a mapping space and the
Kock–Lawvere axiom of synthetic differential geometry is a *theorem*.

Classically the site has objects $\bR^n \times \bD$, for $\bD$ an
infinitesimal thickening of the point. Constructively we read this,
as the paper itself does, through the dual algebras of functions: the
probe $\bA^n \times \bD^k$ *is* the algebra
$R[x_1, \dots, x_n][\epsilon_1]\cdots[\epsilon_k]$ — a [[polynomial
ring|polynomial-ring]] with $k$ layers of [[dual
numbers|dual-numbers]]. "Smooth" here means *polynomial*: the honest
constructive content of coordinate manipulation. Classically, sheaves
on this site (with all Weil algebras, and $C^\infty$-rings for the
smooth column) form the *Cahiers topos* of Dubuc, the standard
well-adapted model of synthetic differential geometry; what follows
is its constructive core.

```agda
data ThAff : Type ℓ where
  𝔸 : Nat → Nat → ThAff

O∙ : Nat → Nat → CRing ℓ
O∙ n zero = R[ Lift ℓ (Fin n) ]
O∙ n (suc k) = Dual.R[ε] (O∙ n k)

O : ThAff → CRing ℓ
O (𝔸 n k) = O∙ n k

structO : ∀ n k → CR.Hom R (O∙ n k)
structO n zero = con-hom
structO n (suc k) = Dual.ι-dual (O∙ n k) CR.∘ structO n k

struct : ∀ x → CR.Hom R (O x)
struct (𝔸 n k) = structO n k
```

A morphism of thickened Cartesian spaces is, dually, a homomorphism
of $R$-algebras between the function rings.

```agda
record ThHom (x y : ThAff) : Type ℓ where
  no-eta-equality
  constructor thhom
  field
    fun      : CR.Hom (O y) (O x)
    commutes : fun CR.∘ struct y ≡ struct x
```

<!--
```agda
open ThHom

private unquoteDecl eqv = declare-record-iso eqv (quote ThHom)

ThHom-path
  : ∀ {x y} {f g : ThHom x y} → f .fun ≡ g .fun → f ≡ g
ThHom-path {f = f} {g} p i .fun = p i
ThHom-path {x} {y} {f = f} {g} p i .commutes =
  is-prop→pathp (λ i → CR.Hom-set R (O x) (p i CR.∘ struct y) (struct x))
    (f .commutes) (g .commutes) i

ThHom-set : ∀ x y → is-set (ThHom x y)
ThHom-set x y = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (CR.Hom-set _ _) λ h → is-prop→is-set (CR.Hom-set _ _ _ _)

pointwise
  : ∀ {x y} {f g : ThHom x y} → f ≡ g
  → ∀ a → f .fun .∫Hom.fst a ≡ g .fun .∫Hom.fst a
pointwise p a = ap (λ e → e .fun .∫Hom.fst a) p
```
-->

```agda
ThCartSp : Precategory ℓ ℓ
ThCartSp .Ob = ThAff
ThCartSp .Hom = ThHom
ThCartSp .Hom-set = ThHom-set
ThCartSp .id = thhom CR.id (CR.idl _)
ThCartSp ._∘_ {z = z} f g = thhom
  (g .fun CR.∘ f .fun)
  ( sym (CR.assoc (g .fun) (f .fun) (struct z))
  ∙ ap (g .fun CR.∘_) (f .commutes) ∙ g .commutes)
ThCartSp .idr f = ThHom-path (CR.idl _)
ThCartSp .idl f = ThHom-path (CR.idr _)
ThCartSp .assoc f g h =
  ThHom-path (sym (CR.assoc (h .fun) (g .fun) (f .fun)))
```

The $0$-dimensional, unthickened space is the terminal probe, because
$R[\varnothing]$ is the initial $R$-algebra: this equips the topos
below with its [[cohesion|cohesive-topos]].

```agda
private
  no-vars : ∀ {C : CRing ℓ} → Lift ℓ (Fin 0) → ⌞ C ⌟
  no-vars v = absurd (Fin-absurd (v .Lift.lower))

pt-terminal : Terminal ThCartSp
pt-terminal .top = 𝔸 0 0
pt-terminal .has⊤ x .centre =
  thhom (extend (struct x) (no-vars {C = O x}))
        (extend-con (struct x) (no-vars {C = O x}))
pt-terminal .has⊤ x .paths h = ThHom-path $ sym $
  extend-unique (struct x) (no-vars {C = O x}) (h .fun)
    (λ a → ap (λ e → e .∫Hom.fst a) (h .commutes))
    (λ v → absurd (Fin-absurd (v .Lift.lower)))
```

**Formal smooth sets** are the presheaves on this site. Since the
site has a terminal probe, the topos is cohesive over sets.

```agda
FrmlSmthSet : Precategory (lsuc ℓ) ℓ
FrmlSmthSet = PSh ℓ ThCartSp

module FrmlSmthSet-cohesion =
  Cat.Instances.Presheaf.Cohesive ThCartSp pt-terminal

𝔸¹ : ⌞ FrmlSmthSet ⌟
𝔸¹ = よ₀ ThCartSp (𝔸 1 0)

𝔻 : ⌞ FrmlSmthSet ⌟
𝔻 = よ₀ ThCartSp (𝔸 0 1)
```

## Products with the infinitesimal disk

What makes this site *work* — the reason the paper's (13) includes
the thickenings in the probes, rather than hoping to find them among
the unthickened spaces — is that the product of any probe with the
disk $\bD$ is again a probe: dually, tensoring with the [[dual
numbers|dual-numbers]] adds one layer of $\epsilon$. The [[universal
property of the dual numbers|universal-property-of-dual-numbers]] is
exactly the universal property of this product.

<!--
```agda
private
  ψ₂ : ∀ n k → CR.Hom (O∙ 0 0) (O∙ n (suc k))
  ψ₂ n k = extend (structO n (suc k)) (no-vars {C = O∙ n (suc k)})

  ε₀ : ⌞ O∙ 0 1 ⌟
  ε₀ = Dual.εᴿ (O∙ 0 0)

  -- Square-zero image of ε under any algebra map out of O(𝔻).
  sq : ∀ {C : CRing ℓ} (h : CR.Hom (O∙ 0 1) C)
     → C .snd .CRing-on._*_ (h .∫Hom.fst ε₀) (h .∫Hom.fst ε₀)
     ≡ C .snd .CRing-on.0r
  sq {C} h =
      sym (h .∫Hom.snd .is-ring-hom.pres-* ε₀ ε₀)
    ∙ ap (h .∫Hom.fst) (Dual.ε² (O∙ 0 0))
    ∙ is-ring-hom.pres-0 (h .∫Hom.snd)

  -- Algebra maps out of R[∅] agreeing under R are equal.
  R0-unique
    : ∀ {C : CRing ℓ} (φC : CR.Hom R C) (h h' : CR.Hom (O∙ 0 0) C)
    → (∀ a → h .∫Hom.fst (con a) ≡ φC .∫Hom.fst a)
    → (∀ a → h' .∫Hom.fst (con a) ≡ φC .∫Hom.fst a)
    → h ≡ h'
  R0-unique {C} φC h h' p p' =
      extend-unique φC (no-vars {C = C}) h p
        (λ v → absurd (Fin-absurd (v .Lift.lower)))
    ∙ sym (extend-unique φC (no-vars {C = C}) h' p'
        (λ v → absurd (Fin-absurd (v .Lift.lower))))

  -- Algebra maps out of O(𝔻) under R with the same image of ε are
  -- equal: O(𝔻) is the walking square-zero element among R-algebras.
  𝔻-hom-unique
    : ∀ {C : CRing ℓ} (φC : CR.Hom R C) (h h' : CR.Hom (O∙ 0 1) C)
    → h CR.∘ structO 0 1 ≡ φC
    → h' CR.∘ structO 0 1 ≡ φC
    → h .∫Hom.fst ε₀ ≡ h' .∫Hom.fst ε₀
    → h ≡ h'
  𝔻-hom-unique {C} φC h h' hc hc' q =
      Dual.ε-extend-unique (O∙ 0 0) (h CR.∘ Dual.ι-dual (O∙ 0 0))
        (h .∫Hom.fst ε₀) (sq h) h (λ a → refl) refl
    ∙ (λ i → Dual.ε-extend (O∙ 0 0) (p i) (q i) (dd i))
    ∙ sym (Dual.ε-extend-unique (O∙ 0 0) (h' CR.∘ Dual.ι-dual (O∙ 0 0))
        (h' .∫Hom.fst ε₀) (sq h') h' (λ a → refl) refl)
    where
    p : h CR.∘ Dual.ι-dual (O∙ 0 0) ≡ h' CR.∘ Dual.ι-dual (O∙ 0 0)
    p = R0-unique φC _ _
      (λ a → ap (λ e → e .∫Hom.fst a) hc)
      (λ a → ap (λ e → e .∫Hom.fst a) hc')

    dd : PathP
      (λ i → C .snd .CRing-on._*_ (q i) (q i) ≡ C .snd .CRing-on.0r)
      (sq h) (sq h')
    dd = is-prop→pathp (λ i → C .fst .is-tr _ _) (sq h) (sq h')
```
-->

```agda
𝔻-product : ∀ n k → Product ThCartSp (𝔸 n k) (𝔸 0 1)
𝔻-product n k = prod where
  open Product
  open is-product

  A = O∙ n k
  εA = Dual.εᴿ A

  pr1 : ThHom (𝔸 n (suc k)) (𝔸 n k)
  pr1 = thhom (Dual.ι-dual A) refl

  pr2 : ThHom (𝔸 n (suc k)) (𝔸 0 1)
  pr2 = thhom (Dual.ε-extend (O∙ 0 0) (ψ₂ n k) εA (Dual.ε² A))
    ( CR.assoc (Dual.ε-extend (O∙ 0 0) (ψ₂ n k) εA (Dual.ε² A))
        (Dual.ι-dual (O∙ 0 0)) con-hom
    ∙ ap (CR._∘ con-hom)
        (Dual.ε-extend-ι (O∙ 0 0) (ψ₂ n k) εA (Dual.ε² A))
    ∙ extend-con (structO n (suc k)) (no-vars {C = O∙ n (suc k)}))

  pair : ∀ {Q} → ThHom Q (𝔸 n k) → ThHom Q (𝔸 0 1)
       → ThHom Q (𝔸 n (suc k))
  pair {Q} f g = thhom
    (Dual.ε-extend A {C = O Q} (f .fun) (g .fun .∫Hom.fst ε₀) (sq (g .fun)))
    ( CR.assoc
        (Dual.ε-extend A {C = O Q} (f .fun) (g .fun .∫Hom.fst ε₀)
          (sq (g .fun)))
        (Dual.ι-dual A) (structO n k)
    ∙ ap (CR._∘ structO n k)
        (Dual.ε-extend-ι A (f .fun) (g .fun .∫Hom.fst ε₀) (sq (g .fun)))
    ∙ f .commutes)
```

The pairing sends $\epsilon$ to the square-zero element named by the
second map; both computation rules and the uniqueness of pairing
follow from the walking-square-zero property of $\cO(\bD)$, by
computing the image of $\epsilon$ on each side.

<!--
```agda
  pair-at-ε
    : ∀ {Q} (f : ThHom Q (𝔸 n k)) (g : ThHom Q (𝔸 0 1))
    → pair f g .fun .∫Hom.fst εA ≡ g .fun .∫Hom.fst ε₀
  pair-at-ε {Q} f g =
      ap₂ OQ._+_
        (is-ring-hom.pres-0 (f .fun .∫Hom.snd))
        ( ap (g .fun .∫Hom.fst ε₀ OQ.*_)
            (is-ring-hom.pres-id (f .fun .∫Hom.snd))
        ∙ OQ.*-idr)
    ∙ OQ.+-idl
    where module OQ = CRing-on (O Q .snd)

  prod : Product ThCartSp (𝔸 n k) (𝔸 0 1)
  prod .apex = 𝔸 n (suc k)
  prod .π₁ = pr1
  prod .π₂ = pr2
  prod .has-is-product .⟨_,_⟩ = pair
  prod .has-is-product .π₁∘⟨⟩ {p1 = f} {p2 = g} = ThHom-path
    (Dual.ε-extend-ι A (f .fun) (g .fun .∫Hom.fst ε₀) (sq (g .fun)))
  prod .has-is-product .π₂∘⟨⟩ {Q} {p1 = f} {p2 = g} = ThHom-path $
    𝔻-hom-unique (struct Q) _ (g .fun)
      ((ThCartSp ._∘_ pr2 (pair f g)) .commutes)
      (g .commutes)
      ( ap (pair f g .fun .∫Hom.fst)
          (Dual.ε-extend-ε (O∙ 0 0) (ψ₂ n k) εA (Dual.ε² A))
      ∙ pair-at-ε f g)
  prod .has-is-product .unique {Q} {p1 = f} {p2 = g} {other} p1 p2 =
    ThHom-path $
        Dual.ε-extend-unique A (other .fun CR.∘ Dual.ι-dual A)
          (other .fun .∫Hom.fst εA) ddo (other .fun) (λ a → refl) refl
      ∙ (λ i → Dual.ε-extend A (q1 i) (q2 i) (dd i))
    where
    module OQ = CRing-on (O Q .snd)

    ddo : OQ._*_ (other .fun .∫Hom.fst εA) (other .fun .∫Hom.fst εA)
        ≡ OQ.0r
    ddo =
        sym (is-ring-hom.pres-* (other .fun .∫Hom.snd) εA εA)
      ∙ ap (other .fun .∫Hom.fst) (Dual.ε² A)
      ∙ is-ring-hom.pres-0 (other .fun .∫Hom.snd)

    q1 : other .fun CR.∘ Dual.ι-dual A ≡ f .fun
    q1 = ap (λ e → e .fun) p1

    q2 : other .fun .∫Hom.fst εA ≡ g .fun .∫Hom.fst ε₀
    q2 =
        sym (ap (other .fun .∫Hom.fst)
          (Dual.ε-extend-ε (O∙ 0 0) (ψ₂ n k) εA (Dual.ε² A)))
      ∙ pointwise p2 ε₀

    dd : PathP (λ i → OQ._*_ (q2 i) (q2 i) ≡ OQ.0r) ddo (sq (g .fun))
    dd = is-prop→pathp (λ i → O Q .fst .is-tr _ _) ddo (sq (g .fun))
```
-->

## The Kock–Lawvere theorem {defines="kock-lawvere"}

In synthetic differential geometry the **Kock–Lawvere axiom** says
that maps out of the infinitesimal disk into the line are exactly
pairs *value and derivative*: $\rm{Maps}(\bD, \bA^1) \simeq \bA^1
\times \bA^1$. Over our site it is a theorem, and the proof is pure
universal-property bookkeeping: plots of the mapping space by $U$ are
plots of $\bA^1$ by the thickening $U \times \bD$, which is again a
probe; and plots of the line are ring elements, so a plot by the
thickened $U$ is a dual number over the functions of $U$ — a pair.

First: plots of the affine line are exactly elements of the function
ring, by the [[universal property of the polynomial
ring|universal-property-of-polynomial-rings]] on one generator.

```agda
plots-𝔸¹ : ∀ x → ThHom x (𝔸 1 0) ≃ ⌞ O x ⌟
plots-𝔸¹ x = Iso→Equiv (to , iso from ri li) where
  to : ThHom x (𝔸 1 0) → ⌞ O x ⌟
  to h = h .fun .∫Hom.fst (var (lift fzero))

  from : ⌞ O x ⌟ → ThHom x (𝔸 1 0)
  from c = thhom (extend (struct x) (λ _ → c))
    (extend-con (struct x) (λ _ → c))

  ri : is-right-inverse from to
  ri c = refl

  li : is-left-inverse from to
  li h = ThHom-path $ sym $
    extend-unique (struct x) (λ _ → to h) (h .fun)
      (λ a → ap (λ e → e .∫Hom.fst a) (h .commutes))
      (λ v → ap (λ z → h .fun .∫Hom.fst (var (lift z))) (fin1 (v .Lift.lower)))
    where
    fin1 : (v : Fin 1) → v ≡ fzero
    fin1 v with fin-view v
    ... | Fin-view.zero = refl
    ... | Fin-view.suc i = absurd (Fin-absurd i)
```

Second: because the products $U \times \bD$ are representable in the
site, maps out of $\yo U \times \bD$ are the same as maps out of
$\yo(U \times \bD)$ — this is where thickening earns its keep.

```agda
private
  module PC = Cartesian-closed (PSh-closed ThCartSp)

T : ⌞ FrmlSmthSet ⌟ → ⌞ FrmlSmthSet ⌟
T X = PC.[ 𝔻 , X ]

module _ (n k : Nat) where
  private
    module P = Product (𝔻-product n k)

    U apx : ThAff
    U = 𝔸 n k
    apx = 𝔸 n (suc k)

    ⟨⟩∘-
      : ∀ {V W} (u : ThHom V U) (d : ThHom V (𝔸 0 1)) (w : ThHom W V)
      → ThCartSp ._∘_ P.⟨ u , d ⟩ w
      ≡ P.⟨ ThCartSp ._∘_ u w , ThCartSp ._∘_ d w ⟩
    ⟨⟩∘- u d w = P.unique
      ( ThCartSp .assoc P.π₁ P.⟨ u , d ⟩ w
      ∙ ap (λ e → ThCartSp ._∘_ e w) P.π₁∘⟨⟩)
      ( ThCartSp .assoc P.π₂ P.⟨ u , d ⟩ w
      ∙ ap (λ e → ThCartSp ._∘_ e w) P.π₂∘⟨⟩)

    thicken-eqv : ∣ T 𝔸¹ .F₀ U ∣ ≃ (よ₀ ThCartSp apx => 𝔸¹)
    thicken-eqv = Iso→Equiv (to' , iso from' ri li) where
      to' : ∣ T 𝔸¹ .F₀ U ∣ → よ₀ ThCartSp apx => 𝔸¹
      to' α .η V h =
        α .η V (ThCartSp ._∘_ P.π₁ h , ThCartSp ._∘_ P.π₂ h)
      to' α .is-natural V W w = funext λ h →
          ap (α .η W) (ap₂ _,_
            (ThCartSp .assoc P.π₁ h w)
            (ThCartSp .assoc P.π₂ h w))
        ∙ happly (α .is-natural V W w)
            (ThCartSp ._∘_ P.π₁ h , ThCartSp ._∘_ P.π₂ h)

      from' : (よ₀ ThCartSp apx => 𝔸¹) → ∣ T 𝔸¹ .F₀ U ∣
      from' β .η V (u , d) = β .η V P.⟨ u , d ⟩
      from' β .is-natural V W w = funext λ (u , d) →
          ap (β .η W) (sym (⟨⟩∘- u d w))
        ∙ happly (β .is-natural V W w) P.⟨ u , d ⟩

      ri : is-right-inverse from' to'
      ri β = Nat-path {C = ThCartSp ^op} {D = Sets ℓ} λ V →
        funext λ h → ap (β .η V) (sym (P.unique refl refl))

      li : is-left-inverse from' to'
      li α = Nat-path {C = (ThCartSp ^op)} {D = Sets ℓ} λ V →
        funext λ (u , d) →
          ap (α .η V) (ap₂ _,_ P.π₁∘⟨⟩ P.π₂∘⟨⟩)
```

Composing the two universal properties with the [[Yoneda
lemma|yoneda-lemma]] gives the theorem: a map from the infinitesimal
disk into the line, in any family over any probe, is exactly a pair
of ring elements — *value and derivative*, and nothing more. The
axiom of synthetic differential geometry holds in this topos.

```agda
  Kock-Lawvere
    : ∣ T 𝔸¹ .F₀ (𝔸 n k) ∣
    ≃ (∣ 𝔸¹ .F₀ (𝔸 n k) ∣ × ∣ 𝔸¹ .F₀ (𝔸 n k) ∣)
  Kock-Lawvere =
    thicken-eqv
    ∙e Equiv.inverse (yo 𝔸¹ , yo-is-equiv 𝔸¹)
    ∙e plots-𝔸¹ apx
    ∙e Σ-ap (Equiv.inverse (plots-𝔸¹ U))
        (λ _ → Equiv.inverse (plots-𝔸¹ U))
```

Together with the [[cohesion|cohesive-topos]] above, this makes
`FrmlSmthSet`{.Agda} a faithful constructive core of the paper's
$\rm{FrmlSmthSet}$: a gros topos of spaces probed by thickened
affine spaces, containing the line $\bA^1$, in which mapping spaces
exist, tangent bundles are mapping spaces out of $\bD$, and the
infinitesimal analysis of variational calculus is valid — with
"smooth" read, constructively, as "polynomial".
