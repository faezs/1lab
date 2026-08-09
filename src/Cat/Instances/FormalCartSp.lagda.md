<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Cat.Displayed.Total

open import Data.Real.Smooth
open import Data.Real.Ring
open import Data.Real.Base

open import Data.Fin using (Fin ; Fin-absurd)

import Cat.Instances.Presheaf.Cohesive
import Algebra.Ring.DualNumbers as Dual
import Cat.Reasoning

open is-ring-hom
open Precategory
open Terminal
```
-->

```agda
module Cat.Instances.FormalCartSp where
```

<!--
```agda
private
  module CR = Cat.Reasoning (CRings lzero)
```
-->

# The site of thickened Cartesian spaces {defines="formal-cartesian-space formal-smooth-set-honest"}

The paper's (13): infinitesimally thickened Cartesian spaces are
*declared*, dually, as the objects of the opposite category of
commutative $\bR$-algebras whose function algebras are the [[rings
of smooth functions|smooth-function]] with nilpotent monomials
adjoined:

$$
\bR^n \times \bD_k \;\mapsto\; C^\infty(\bR^n) \otimes_\bR
\bR[\epsilon_1, \ldots]/(\epsilon^2).
$$

The smooth-function ring is now the honest one — carried by
functions of Dedekind reals with Hadamard towers — and the
nilpotent adjunction is the generic dual-numbers construction,
iterated.

One implementation note: the smooth-function ring is wrapped in an
`opaque`{.Agda} definition. Category-level reasoning about algebra
homomorphisms never needs to compute inside the ring of smooth
functions — and letting the normaliser see through it makes even
a single composite of homomorphisms intractable. The few facts
that *do* require computation (that evaluation at the empty tuple
splits the constants) are proven inside `unfolding` blocks, where
no composite is ever formed.

```agda
opaque
  C∞R : Nat → CRing lzero
  C∞R n = C∞Ring n

opaque
  unfolding C∞R

  const∞ : (n : Nat) → CR.Hom ℝ-comm (C∞R n)
  const∞ n .∫Hom.fst c = (λ _ → c) , inc (smooth-const c)
  const∞ n .∫Hom.snd .pres-id = Σ-prop-path (λ _ → squash) refl
  const∞ n .∫Hom.snd .pres-+ a b = Σ-prop-path (λ _ → squash) refl
  const∞ n .∫Hom.snd .pres-* a b = Σ-prop-path (λ _ → squash) refl

data ThAff : Type where
  𝔸 : Nat → Nat → ThAff

O∙ : Nat → Nat → CRing lzero
O∙ n zero    = C∞R n
O∙ n (suc k) = Dual.R[ε] (O∙ n k)

O : ThAff → CRing lzero
O (𝔸 n k) = O∙ n k

structO : ∀ n k → CR.Hom ℝ-comm (O∙ n k)
structO n zero    = const∞ n
structO n (suc k) = Dual.ι-dual (O∙ n k) CR.∘ structO n k

struct : ∀ x → CR.Hom ℝ-comm (O x)
struct (𝔸 n k) = structO n k
```

A morphism is, dually, a homomorphism of $\bR$-algebras between the
function rings — all of them, exactly as in the paper's full
subcategory.

```agda
record ThHom (x y : ThAff) : Type where
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
ThHom-path {x} {y} {f} {g} p i .fun = p i
ThHom-path {x} {y} {f} {g} p i .commutes =
  is-prop→pathp
    (λ i → CR.Hom-set ℝ-comm (O x) (p i CR.∘ struct y) (struct x))
    (f .commutes) (g .commutes) i

ThHom-set : ∀ x y → is-set (ThHom x y)
ThHom-set x y = Iso→is-hlevel 2 eqv $ Σ-is-hlevel 2
  (CR.Hom-set (O y) (O x))
  (λ _ → is-prop→is-set (CR.Hom-set ℝ-comm (O x) _ _))
```
-->

```agda
FormalCartSp : Precategory lzero lzero
FormalCartSp .Ob = ThAff
FormalCartSp .Hom = ThHom
FormalCartSp .Hom-set = ThHom-set
FormalCartSp .id {x} = thhom CR.id (CR.idl (struct x))
FormalCartSp ._∘_ {x} {y} {z} f g = thhom
  (g .fun CR.∘ f .fun)
  ( sym (CR.assoc (g .fun) (f .fun) (struct z))
  ∙ ap (g .fun CR.∘_) (f .commutes)
  ∙ g .commutes)
FormalCartSp .idr f = ThHom-path (CR.idl _)
FormalCartSp .idl f = ThHom-path (CR.idr _)
FormalCartSp .assoc f g h =
  ThHom-path (sym (CR.assoc (h .fun) (g .fun) (f .fun)))
```

## The terminal probe

The unthickened point's function ring is the smooth functions of no
variables — canonically the reals themselves, since a smooth
$0$-ary function is determined by its value at the empty tuple. So
an algebra map out of it under $\bR$ has no choices to make.

<!--
```agda
private opaque
  unfolding const∞

  ev∅ : CR.Hom (C∞R 0) ℝ-comm
  ev∅ .∫Hom.fst (f , _) = f (λ j → absurd (Fin-absurd j))
  ev∅ .∫Hom.snd .pres-id = refl
  ev∅ .∫Hom.snd .pres-+ a b = refl
  ev∅ .∫Hom.snd .pres-* a b = refl

  C∞0-η
    : (a : ⌞ C∞R 0 ⌟)
    → const∞ 0 .∫Hom.fst (ev∅ .∫Hom.fst a) ≡ a
  C∞0-η a = Σ-prop-path (λ _ → squash)
    (funext λ v → ap (a .fst)
      (funext λ j → absurd (Fin-absurd j)))

  C∞0-ε
    : (c : ⌞ ℝ-comm ⌟)
    → ev∅ .∫Hom.fst (const∞ 0 .∫Hom.fst c) ≡ c
  C∞0-ε c = refl

private
  hom-path
    : {A B : CRing lzero} {f g : CR.Hom A B}
    → (∀ a → f .∫Hom.fst a ≡ g .∫Hom.fst a) → f ≡ g
  hom-path {A} {B} {f} {g} p i .∫Hom.fst a = p a i
  hom-path {A} {B} {f} {g} p i .∫Hom.snd = is-prop→pathp
    (λ i → hlevel {T = is-ring-hom
      (CRing-on.has-ring-on (A .snd))
      (CRing-on.has-ring-on (B .snd))
      (λ a → p a i)} 1)
    (f .∫Hom.snd) (g .∫Hom.snd) i
```
-->

```agda
pt-terminal : Terminal FormalCartSp
pt-terminal .top = 𝔸 0 0
pt-terminal .has⊤ x .centre = thhom
  (struct x CR.∘ ev∅)
  ( sym (CR.assoc (struct x) ev∅ (const∞ 0))
  ∙ ap (struct x CR.∘_) (hom-path C∞0-ε)
  ∙ CR.idr (struct x))
pt-terminal .has⊤ x .paths h = ThHom-path $ hom-path λ a →
  sym ( ap (h .fun .∫Hom.fst) (sym (C∞0-η a))
      ∙ ap (λ w → w .∫Hom.fst (ev∅ .∫Hom.fst a)) (h .commutes))
```

**Formal smooth sets**, honestly: the presheaf topos over this site
is cohesive; the sheaf-theoretic refinement (14) awaits only the
coverage of differentiably good open covers, the generic
sheafification machinery being already in place.

```agda
FormalSmoothSet : Precategory (lsuc lzero) lzero
FormalSmoothSet = PSh lzero FormalCartSp

module FormalSmoothSet-cohesion =
  Cat.Instances.Presheaf.Cohesive FormalCartSp pt-terminal
```
