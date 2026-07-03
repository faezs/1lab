<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Data.Fin using (Fin)

import Algebra.Ring.Reasoning
import Cat.Reasoning

open make-ring
open is-ring-hom
```
-->

```agda
module Algebra.Ring.Grassmann {ℓ} (R : CRing ℓ) (q : Nat) where
```

<!--
```agda
private
  module R = CRing-on (R .snd)
```
-->

# Grassmann algebras {defines="grassmann-algebra anticommutation"}

A classical fermion field is an *anticommuting* variable: the paper's
(17), $\psi\psi' = -\psi'\psi$, is forced on classical field values
by the existence of the Dirac Lagrangian. The universal home for $q$
such variables over a commutative [[ring]] $R$ is the **Grassmann
algebra** $\Lambda_R[\theta_1, \dots, \theta_q]$: the free
$R$-algebra on $q$ generators subject to anticommutation and to the
vanishing of squares. It is not commutative, but it is
*super*-commutative, and it is the odd half of the function algebra
$C^\infty(\bR^{n|q})$ of a super Cartesian space, the paper's (18).

As before, the higher-inductive presentation adjoins the generators
and the laws and nothing else. Since the algebra is noncommutative we
need both unit and both distributivity laws, and centrality of the
constants is now a *relation*.

```agda
data Grassmann : Type ℓ where
  θ         : Fin q → Grassmann
  con       : ⌞ R ⌟ → Grassmann
  _+g_ _*g_ : Grassmann → Grassmann → Grassmann
  negg      : Grassmann → Grassmann

  +g-idl     : ∀ x → con R.0r +g x ≡ x
  +g-invr    : ∀ x → x +g negg x ≡ con R.0r
  +g-assoc   : ∀ x y z → x +g (y +g z) ≡ (x +g y) +g z
  +g-comm    : ∀ x y → x +g y ≡ y +g x
  *g-idl     : ∀ x → con R.1r *g x ≡ x
  *g-idr     : ∀ x → x *g con R.1r ≡ x
  *g-assoc   : ∀ x y z → x *g (y *g z) ≡ (x *g y) *g z
  *g-distribl : ∀ x y z → x *g (y +g z) ≡ (x *g y) +g (x *g z)
  *g-distribr : ∀ x y z → (y +g z) *g x ≡ (y *g x) +g (z *g x)
  con-+      : ∀ a b → con (a R.+ b) ≡ con a +g con b
  con-*      : ∀ a b → con (a R.* b) ≡ con a *g con b
  con-comm   : ∀ a x → con a *g x ≡ x *g con a
  θ-anticomm : ∀ i j → θ i *g θ j ≡ negg (θ j *g θ i)
  θ-sq       : ∀ i → θ i *g θ i ≡ con R.0r
  squashg    : is-set Grassmann
```

Packaging gives a (noncommutative) ring under $R$; the anticommuting
relation (17) and the vanishing of squares are the constructors
`θ-anticomm`{.Agda} and `θ-sq`{.Agda}.

```agda
Λ[q] : Ring ℓ
Λ[q] = to-ring mk where
  mk : make-ring Grassmann
  mk .ring-is-set = squashg
  mk .0R = con R.0r
  mk ._+_ = _+g_
  mk .-_ = negg
  mk .+-idl = +g-idl
  mk .+-invr = +g-invr
  mk .+-assoc = +g-assoc
  mk .+-comm = +g-comm
  mk .1R = con R.1r
  mk ._*_ = _*g_
  mk .*-idl = *g-idl
  mk .*-idr = *g-idr
  mk .*-assoc = *g-assoc
  mk .*-distribl = *g-distribl
  mk .*-distribr = *g-distribr
```

<!--
```agda
private
  module Λr = Algebra.Ring.Reasoning Λ[q]
```
-->

<details>
<summary>The eliminator into propositions is derived by reflection,
as usual.</summary>

```agda
Grassmann-elim-prop
  : ∀ {ℓ'} (B : Grassmann → Type ℓ')
  → (∀ x → is-prop (B x))
  → (∀ i → B (θ i))
  → (∀ a → B (con a))
  → (∀ x → B x → ∀ y → B y → B (x +g y))
  → (∀ x → B x → ∀ y → B y → B (x *g y))
  → (∀ x → B x → B (negg x))
  → ∀ x → B x
unquoteDef Grassmann-elim-prop = make-elim-with (default-elim-visible into 1)
  Grassmann-elim-prop (quote Grassmann)
```

</details>

## The parity involution

Constructively and minimally, the $\mathbb{Z}/2$-grading of the
Grassmann algebra is carried by its **parity involution**: the ring
automorphism fixing the constants and negating every odd generator.
Homomorphisms of super algebras are the ring homomorphisms commuting
with the involutions, which is how the super site (19) is assembled
from plain ring maps.

```agda
σ-parity : Grassmann → Grassmann
σ-parity (θ i) = negg (θ i)
σ-parity (con a) = con a
σ-parity (x +g y) = σ-parity x +g σ-parity y
σ-parity (x *g y) = σ-parity x *g σ-parity y
σ-parity (negg x) = negg (σ-parity x)

σ-parity (+g-idl x i) = +g-idl (σ-parity x) i
σ-parity (+g-invr x i) = +g-invr (σ-parity x) i
σ-parity (+g-assoc x y z i) =
  +g-assoc (σ-parity x) (σ-parity y) (σ-parity z) i
σ-parity (+g-comm x y i) = +g-comm (σ-parity x) (σ-parity y) i
σ-parity (*g-idl x i) = *g-idl (σ-parity x) i
σ-parity (*g-idr x i) = *g-idr (σ-parity x) i
σ-parity (*g-assoc x y z i) =
  *g-assoc (σ-parity x) (σ-parity y) (σ-parity z) i
σ-parity (*g-distribl x y z i) =
  *g-distribl (σ-parity x) (σ-parity y) (σ-parity z) i
σ-parity (*g-distribr x y z i) =
  *g-distribr (σ-parity x) (σ-parity y) (σ-parity z) i
σ-parity (con-+ a b i) = con-+ a b i
σ-parity (con-* a b i) = con-* a b i
σ-parity (con-comm a x i) = con-comm a (σ-parity x) i
σ-parity (θ-anticomm i j k) = lemma i j k where
  neg-neg-* : ∀ x y → negg x *g negg y ≡ x *g y
  neg-neg-* x y =
      Λr.*-negatel
    ∙ ap negg Λr.*-negater
    ∙ Λr.a.inv-inv

  lemma : ∀ i j → negg (θ i) *g negg (θ j) ≡ negg (negg (θ j) *g negg (θ i))
  lemma i j =
      neg-neg-* (θ i) (θ j)
    ∙ θ-anticomm i j
    ∙ ap negg (sym (neg-neg-* (θ j) (θ i)))
σ-parity (θ-sq i k) = (neg-neg-θ ∙ θ-sq i) k where
  neg-neg-θ : negg (θ i) *g negg (θ i) ≡ θ i *g θ i
  neg-neg-θ = Λr.*-negatel ∙ ap negg Λr.*-negater ∙ Λr.a.inv-inv
σ-parity (squashg x y p q i j) = squashg
  (σ-parity x) (σ-parity y)
  (λ i → σ-parity (p i)) (λ i → σ-parity (q i)) i j
```

The involution is a ring homomorphism squaring to the identity — the
minimal witness that the algebra is $\mathbb{Z}/2$-graded, with the
constants even and the generators odd.

```agda
σ-is-ring-hom : is-ring-hom (Λ[q] .snd) (Λ[q] .snd) σ-parity
σ-is-ring-hom .pres-id = refl
σ-is-ring-hom .pres-+ x y = refl
σ-is-ring-hom .pres-* x y = refl

σ-σ : ∀ x → σ-parity (σ-parity x) ≡ x
σ-σ = Grassmann-elim-prop (λ x → σ-parity (σ-parity x) ≡ x)
  (λ _ → squashg _ _)
  (λ i → Λr.a.inv-inv)
  (λ a → refl)
  (λ x ihx y ihy → ap₂ _+g_ ihx ihy)
  (λ x ihx y ihy → ap₂ _*g_ ihx ihy)
  (λ x ih → ap negg ih)
```

The full super site (19) — super Cartesian spaces $\bR^{n|q}$, dual
to tensor products of [[polynomial rings|polynomial-ring]] with
Grassmann algebras, with involution-respecting algebra maps — and its
topos of super smooth sets (20) assemble from this module and the
polynomial ring exactly as the thickened site did from the dual
numbers; the assembly, and the odd-plot description of spinor fields
(21), remain future work.

## The universal property

An algebra map out of the Grassmann algebra into any ring $C$ is
exactly: a ring map on the constants landing *centrally* in $C$,
together with images for the generators that anticommute and square
to zero. Centrality of the constants is forced by the relation
`con-comm`{.Agda}, which quantifies over every element.

```agda
module _ (C : Ring ℓ)
         (ψf : ⌞ R ⌟ → ⌞ C ⌟)
         (ψh : is-ring-hom (R .snd .CRing-on.has-ring-on) (C .snd) ψf)
         (central : ∀ a y →
           C .snd .Ring-on._*_ (ψf a) y ≡ C .snd .Ring-on._*_ y (ψf a))
         (c : Fin q → ⌞ C ⌟)
         (anti : ∀ i j →
           C .snd .Ring-on._*_ (c i) (c j)
           ≡ Ring-on.-_ (C .snd) (C .snd .Ring-on._*_ (c j) (c i)))
         (sq : ∀ i →
           C .snd .Ring-on._*_ (c i) (c i) ≡ Ring-on.0r (C .snd))
  where

  private
    module C = Ring-on (C .snd)
    module ψ = is-ring-hom ψh

  grassmann-extend : Grassmann → ⌞ C ⌟
  grassmann-extend (θ i) = c i
  grassmann-extend (con a) = ψf a
  grassmann-extend (x +g y) = grassmann-extend x C.+ grassmann-extend y
  grassmann-extend (x *g y) = grassmann-extend x C.* grassmann-extend y
  grassmann-extend (negg x) = C.- grassmann-extend x

  grassmann-extend (+g-idl x i) =
    (ap (C._+ grassmann-extend x) ψ.pres-0 ∙ C.+-idl) i
  grassmann-extend (+g-invr x i) =
    (C.+-invr {grassmann-extend x} ∙ sym ψ.pres-0) i
  grassmann-extend (+g-assoc x y z i) =
    C.+-associative
      {grassmann-extend x} {grassmann-extend y} {grassmann-extend z} i
  grassmann-extend (+g-comm x y i) =
    C.+-commutes {grassmann-extend x} {grassmann-extend y} i
  grassmann-extend (*g-idl x i) =
    (ap (C._* grassmann-extend x) ψ.pres-id ∙ C.*-idl) i
  grassmann-extend (*g-idr x i) =
    (ap (grassmann-extend x C.*_) ψ.pres-id ∙ C.*-idr) i
  grassmann-extend (*g-assoc x y z i) =
    C.*-associative
      {grassmann-extend x} {grassmann-extend y} {grassmann-extend z} i
  grassmann-extend (*g-distribl x y z i) =
    C.*-distribl
      {grassmann-extend x} {grassmann-extend y} {grassmann-extend z} i
  grassmann-extend (*g-distribr x y z i) =
    C.*-distribr
      {grassmann-extend x} {grassmann-extend y} {grassmann-extend z} i
  grassmann-extend (con-+ a b i) = ψ.pres-+ a b i
  grassmann-extend (con-* a b i) = ψ.pres-* a b i
  grassmann-extend (con-comm a x i) = central a (grassmann-extend x) i
  grassmann-extend (θ-anticomm i j k) = anti i j k
  grassmann-extend (θ-sq i k) = (sq i ∙ sym ψ.pres-0) k
  grassmann-extend (squashg x y p q i j) = C.has-is-set
    (grassmann-extend x) (grassmann-extend y)
    (λ i → grassmann-extend (p i)) (λ i → grassmann-extend (q i)) i j

  grassmann-extend-is-ring-hom
    : is-ring-hom (Λ[q] .snd) (C .snd) grassmann-extend
  grassmann-extend-is-ring-hom .pres-id = ψ.pres-id
  grassmann-extend-is-ring-hom .pres-+ x y = refl
  grassmann-extend-is-ring-hom .pres-* x y = refl

  grassmann-extend-unique
    : (h : Grassmann → ⌞ C ⌟)
    → is-ring-hom (Λ[q] .snd) (C .snd) h
    → (∀ a → h (con a) ≡ ψf a)
    → (∀ i → h (θ i) ≡ c i)
    → ∀ x → h x ≡ grassmann-extend x
  grassmann-extend-unique h hh hcon hθ = Grassmann-elim-prop
    (λ x → h x ≡ grassmann-extend x)
    (λ _ → C.has-is-set _ _)
    hθ
    hcon
    (λ x ihx y ihy → is-ring-hom.pres-+ hh x y ∙ ap₂ C._+_ ihx ihy)
    (λ x ihx y ihy → is-ring-hom.pres-* hh x y ∙ ap₂ C._*_ ihx ihy)
    (λ x ih → is-ring-hom.pres-neg hh ∙ ap C.-_ ih)
```
