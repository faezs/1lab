<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Cat.Displayed.Total

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.Polynomial {ℓ} (R : CRing ℓ) where
```

<!--
```agda
private
  module R = CRing-on (R .snd)
  module CR = Cat.Reasoning (CRings ℓ)

open make-ring
open is-ring-hom

private variable
  X : Type ℓ
```
-->

# Polynomial rings, as free commutative algebras {defines="polynomial-ring free-commutative-algebra"}

The **polynomial ring** $R[X]$ over a commutative [[ring]] $R$, on a
type $X$ of *variables*, is the free commutative $R$-algebra on $X$:
the universal solution to adjoining the elements of $X$ to $R$. Its
universal property is what makes local coordinate manipulations in
physics tick — an "$n$-dimensional coordinate expression" is exactly a
morphism out of $R[x_1, \dots, x_n]$, and substitution of expressions
is composition.

Classically, $R[X]$ is presented by normal forms: formal sums of
monomials. Constructively and cubically, we may instead give a direct,
higher-inductive presentation — there is no need to fix a
representation of monomials and then quotient: we add point
constructors for the variables, the constants, and the ring
operations, then path constructors making this into a commutative
$R$-algebra, and *nothing else*. The universal property is then
immediate, which is all we shall need.

```agda
data Poly (X : Type ℓ) : Type ℓ where
  var       : X → Poly X
  con       : ⌞ R ⌟ → Poly X
  _+ₚ_ _*ₚ_ : Poly X → Poly X → Poly X
  negₚ      : Poly X → Poly X
```

The path constructors are precisely the data of `make-ring`{.Agda},
together with commutativity of multiplication and the requirement that
`con`{.Agda} is a ring homomorphism.

```agda
  +ₚ-idl     : ∀ x → con R.0r +ₚ x ≡ x
  +ₚ-invr    : ∀ x → x +ₚ negₚ x ≡ con R.0r
  +ₚ-assoc   : ∀ x y z → x +ₚ (y +ₚ z) ≡ (x +ₚ y) +ₚ z
  +ₚ-comm    : ∀ x y → x +ₚ y ≡ y +ₚ x
  *ₚ-idl     : ∀ x → con R.1r *ₚ x ≡ x
  *ₚ-assoc   : ∀ x y z → x *ₚ (y *ₚ z) ≡ (x *ₚ y) *ₚ z
  *ₚ-comm    : ∀ x y → x *ₚ y ≡ y *ₚ x
  *ₚ-distribl : ∀ x y z → x *ₚ (y +ₚ z) ≡ (x *ₚ y) +ₚ (x *ₚ z)
  con-+      : ∀ a b → con (a R.+ b) ≡ con a +ₚ con b
  con-*      : ∀ a b → con (a R.* b) ≡ con a *ₚ con b
  squash     : is-set (Poly X)
```

Packaging the constructors gives a commutative ring, and `con`{.Agda}
a ring homomorphism into it.

```agda
R[_] : Type ℓ → CRing ℓ
R[ X ] .fst = el (Poly X) squash
R[ X ] .snd .CRing-on.has-ring-on = to-ring-on mk where
  mk : make-ring (Poly X)
  mk .ring-is-set = squash
  mk .0R = con R.0r
  mk ._+_ = _+ₚ_
  mk .-_ = negₚ
  mk .+-idl = +ₚ-idl
  mk .+-invr = +ₚ-invr
  mk .+-assoc = +ₚ-assoc
  mk .+-comm = +ₚ-comm
  mk .1R = con R.1r
  mk ._*_ = _*ₚ_
  mk .*-idl = *ₚ-idl
  mk .*-idr x = *ₚ-comm x (con R.1r) ∙ *ₚ-idl x
  mk .*-assoc = *ₚ-assoc
  mk .*-distribl = *ₚ-distribl
  mk .*-distribr x y z =
      *ₚ-comm (y +ₚ z) x ∙ *ₚ-distribl x y z
    ∙ ap₂ _+ₚ_ (*ₚ-comm x y) (*ₚ-comm x z)
R[ X ] .snd .CRing-on.*-commutes {x} {y} = *ₚ-comm x y

con-hom : ∀ {X} → CR.Hom R R[ X ]
con-hom .∫Hom.fst = con
con-hom .∫Hom.snd .pres-id = refl
con-hom .∫Hom.snd .pres-+ = con-+
con-hom .∫Hom.snd .pres-* = con-*
```

<details>
<summary>Since propositions automatically respect the path
constructors, our reflection machinery derives the eliminator into
families of propositions.</summary>

```agda
Poly-elim-prop
  : ∀ {ℓ'} (B : Poly X → Type ℓ')
  → (∀ x → is-prop (B x))
  → (∀ x → B (var x))
  → (∀ a → B (con a))
  → (∀ x → B x → ∀ y → B y → B (x +ₚ y))
  → (∀ x → B x → ∀ y → B y → B (x *ₚ y))
  → (∀ x → B x → B (negₚ x))
  → ∀ x → B x
unquoteDef Poly-elim-prop = make-elim-with (default-elim-visible into 1)
  Poly-elim-prop (quote Poly)
```

</details>

## The universal property {defines="universal-property-of-polynomial-rings"}

A commutative $R$-algebra is a commutative ring $C$ with a
homomorphism $\varphi : R \to C$. The universal property of $R[X]$
says: to give an algebra map $R[X] \to C$ is exactly to give a
function $X \to C$, saying where the variables go — *evaluation* of
polynomials, and the precise sense in which a polynomial is a
coordinate expression.

```agda
module _ {C : CRing ℓ} (φ : CR.Hom R C) {X : Type ℓ} (f : X → ⌞ C ⌟) where
  private
    module C = CRing-on (C .snd)
    module φ = is-ring-hom (φ .∫Hom.snd)

  extendᵖ : Poly X → ⌞ C ⌟
  extendᵖ (var x) = f x
  extendᵖ (con a) = φ .∫Hom.fst a
  extendᵖ (p +ₚ q) = extendᵖ p C.+ extendᵖ q
  extendᵖ (p *ₚ q) = extendᵖ p C.* extendᵖ q
  extendᵖ (negₚ p) = C.- extendᵖ p
```

The higher constructors are sent to the corresponding laws of $C$,
using that $\varphi$ is a homomorphism for the constants.

```agda
  extendᵖ (+ₚ-idl x i) =
    (ap (C._+ extendᵖ x) φ.pres-0 ∙ C.+-idl) i
  extendᵖ (+ₚ-invr x i) =
    (C.+-invr {x = extendᵖ x} ∙ sym φ.pres-0) i
  extendᵖ (+ₚ-assoc x y z i) =
    C.+-associative {extendᵖ x} {extendᵖ y} {extendᵖ z} i
  extendᵖ (+ₚ-comm x y i) = C.+-commutes {extendᵖ x} {extendᵖ y} i
  extendᵖ (*ₚ-idl x i) =
    (ap (C._* extendᵖ x) φ.pres-id ∙ C.*-idl) i
  extendᵖ (*ₚ-assoc x y z i) =
    C.*-associative {extendᵖ x} {extendᵖ y} {extendᵖ z} i
  extendᵖ (*ₚ-comm x y i) = C.*-commutes {extendᵖ x} {extendᵖ y} i
  extendᵖ (*ₚ-distribl x y z i) =
    C.*-distribl {extendᵖ x} {extendᵖ y} {extendᵖ z} i
  extendᵖ (con-+ a b i) = φ.pres-+ a b i
  extendᵖ (con-* a b i) = φ.pres-* a b i
  extendᵖ (squash x y p q i j) = C.has-is-set
    (extendᵖ x) (extendᵖ y) (λ i → extendᵖ (p i)) (λ i → extendᵖ (q i)) i j

  extend : CR.Hom R[ X ] C
  extend .∫Hom.fst = extendᵖ
  extend .∫Hom.snd .pres-id = φ.pres-id
  extend .∫Hom.snd .pres-+ p q = refl
  extend .∫Hom.snd .pres-* p q = refl

  extend-con : extend CR.∘ con-hom ≡ φ
  extend-con = ∫Hom-path _ refl prop!

  extend-var : ∀ x → extendᵖ (var x) ≡ f x
  extend-var x = refl
```

Uniqueness: any algebra map out of $R[X]$ agreeing with $f$ on the
variables is the extension. Together with `extend-con`{.Agda} and
`extend-var`{.Agda}, this is the [[universal property of the
polynomial ring|universal-property-of-polynomial-rings]].

```agda
  extend-unique
    : (h : CR.Hom R[ X ] C)
    → (∀ a → h .∫Hom.fst (con a) ≡ φ .∫Hom.fst a)
    → (∀ x → h .∫Hom.fst (var x) ≡ f x)
    → h ≡ extend
  extend-unique h hcon hvar = ∫Hom-path _ (funext go) prop! where
    module h = is-ring-hom (h .∫Hom.snd)

    go : ∀ p → h .∫Hom.fst p ≡ extendᵖ p
    go = Poly-elim-prop _ (λ _ → C.has-is-set _ _)
      hvar
      hcon
      (λ x p y q → h.pres-+ x y ∙ ap₂ C._+_ p q)
      (λ x p y q → h.pres-* x y ∙ ap₂ C._*_ p q)
      (λ x p → h.pres-neg ∙ ap C.-_ p)
```

When the variable type is empty, `extend`{.Agda} and
`extend-unique`{.Agda} say that algebra maps out of $R[\varnothing]$
are *no data at all*: $R[\varnothing]$ is an initial $R$-algebra,
which is what makes the $0$-dimensional affine space terminal among
the probes of algebraic geometry.
