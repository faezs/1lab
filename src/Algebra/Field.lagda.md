<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Prelude hiding (_*_ ; _+_)

open import Algebra.Semigroup
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Displayed.Univalence.Thin
open import Cat.Base

open import Data.Int.Properties
open import Data.Int.Base

import Algebra.Monoid.Reasoning as Mon

import Cat.Reasoning
```
-->

```agda
module Algebra.Field where
```

# Fields {defines=field}

The **ring** is one of the basic objects of study in algebra, which
abstracts the best bits of the common algebraic structures: The integers
$\bb{Z}$, the rationals $\bb{Q}$, the reals $\bb{R}$, and the complex
numbers $\bb{C}$ are all rings, as are the collections of polynomials
with coefficients in any of those. Less familiar examples of rings
include square matrices (with values in a ring) and the integral
cohomology ring of a topological space: that these are so far from being
"number-like" indicates the incredible generality of rings.

A **ring** is an [[abelian group]] $R$ (which we call the **additive
group** of $R$), together with the data of a monoid on $R$ (the
**multiplicative monoid**), where the multiplication of the monoid
_distributes over_ the addition. We'll see why this compatibility
condition is required afterwards. Check out what it means for a triple
$(1, *, +)$ to be a ring structure on a type:

```agda
record is-field {ℓ} {R : Type ℓ} (1r : R) (_*_ _+_ : R → R → R) : Type ℓ where
  no-eta-equality
  field
    *-group : is-abelian-group _*_
    +-group  : is-abelian-group _+_
    *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  open is-abelian-group *-group
    renaming ( _—_ to _-*_
             ; inverse to -*_
             ; 1g to 0r*
             ; inversel to *-inversel
             ; inverser to *-inverser
             ; associative to *-associative
             ; idl to *-idl
             ; idr to *-idr
             ; commutes to *-commutes
             )


  open is-abelian-group +-group
    renaming ( _—_ to _-_
             ; inverse to -_
             ; 1g to 0r
             ; inversel to +-invl
             ; inverser to +-invr
             ; associative to +-associative
             ; idl to +-idl
             ; idr to +-idr
             ; commutes to +-commutes
             )
    hiding (has-is-group; has-is-monoid)
    public

  additive-group : Σ (Set ℓ) (λ x → Group-on ⌞ x ⌟)
  ∣ additive-group .fst ∣                    = R
  additive-group .fst .is-tr                 = is-abelian-group.has-is-set +-group
  additive-group .snd .Group-on._⋆_          = _+_
  additive-group .snd .Group-on.has-is-group = is-abelian-group.has-is-group +-group

  group : Abelian-group ℓ
  ∣ group .fst ∣                         = R
  group .fst .is-tr                      = is-abelian-group.has-is-set +-group
  group .snd .Abelian-group-on._*_       = _+_
  group .snd .Abelian-group-on.has-is-ab = +-group

  multiplicative-monoid : Monoid ℓ
  multiplicative-monoid .fst = R
  multiplicative-monoid .snd = record { has-is-monoid =  has-is-monoid }

  module m = Mon multiplicative-monoid
  module a = Abelian-group-on record { has-is-ab = +-group }
    hiding (_*_ ; 1g ; _⁻¹)

record Field-on {ℓ} (R : Type ℓ) : Type ℓ where
  field
    1r : R
    _*_ _+_ : R → R → R
    has-is-field : is-field 1r _*_ _+_

  open is-field has-is-field public
  infixl 25 _*_
  infixl 20 _+_

instance
  H-Level-is-field
    : ∀ {ℓ} {R : Type ℓ} {1r : R} {_*_ _+_ : R → R → R} {n}
    → H-Level (is-field 1r _*_ _+_) (suc n)
  H-Level-is-field {1r = 1r} {_*_} {_+_} =
    prop-instance {T = is-field 1r _*_ _+_} $ λ where
      x y i .*-group   → hlevel 1 (x .*-group) (y .*-group) i
      x y i .+-group    → hlevel 1 (x .+-group) (y .+-group) i
      x y i .*-distribl → x .+-group .is-abelian-group.has-is-set _ _ (x .*-distribl) (y .*-distribl) i
      x y i .*-distribr → x .+-group .is-abelian-group.has-is-set _ _ (x .*-distribr) (y .*-distribr) i
    where open is-field
```
-->

There is a natural notion of field homomorphism, which we get by smashing
together that of a monoid homomorphism (for the multiplicative part) and
of group homomorphism; Every map of fields has an underlying map of
groups which preserves the addition operation, and it must also preserve
the multiplication. This encodes the view of a field as an "abelian group
with a monoid structure".

```agda
record is-field-hom
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (R : Field-on A) (S : Field-on B)
  (f : A → B)
  : Type (ℓ ⊔ ℓ') where
  private
    module A = Field-on R
    module B = Field-on S

  field
    pres-id : f A.1r ≡ B.1r
    pres-+  : ∀ x y → f (x A.+ y) ≡ f x B.+ f y
    pres-*  : ∀ x y → f (x A.* y) ≡ f x B.* f y
```

<!--
```agda
  field-hom→group-hom : is-group-hom (A.additive-group .snd) (B.additive-group .snd) f
  field-hom→group-hom = record { pres-⋆ = pres-+ }

  module gh = is-group-hom field-hom→group-hom renaming (pres-id to pres-0 ; pres-inv to pres-neg)
  open gh using (pres-0 ; pres-neg ; pres-diff) public

private unquoteDecl eqv = declare-record-iso eqv (quote is-field-hom)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {R : Field-on A} {S : Field-on B} where
  open Field-on R using (magma-hlevel)
  open Field-on S using (magma-hlevel)

  instance abstract
    H-Level-field-hom : ∀ {f n} → H-Level (is-field-hom R S f) (suc n)
    H-Level-field-hom = prop-instance λ x y → Iso→is-hlevel 1 eqv (hlevel 1) x y

open is-field-hom
```
-->

It follows, by standard equational nonsense, that fields and field
homomorphisms form a precategory --- for instance, we have $f(g(1_R)) =
f(1_S) = 1_T$.

```agda
Field-structure : ∀ ℓ → Thin-structure ℓ Field-on
Field-structure ℓ .is-hom f x y = el! (is-field-hom x y f)
Field-structure ℓ .id-is-hom .pres-id = refl
Field-structure ℓ .id-is-hom .pres-+ x y = refl
Field-structure ℓ .id-is-hom .pres-* x y = refl
Field-structure ℓ .∘-is-hom f g α β .pres-id = ap f (β .pres-id) ∙ α .pres-id
Field-structure ℓ .∘-is-hom f g α β .pres-+ x y = ap f (β .pres-+ x y) ∙ α .pres-+ _ _
Field-structure ℓ .∘-is-hom f g α β .pres-* x y = ap f (β .pres-* x y) ∙ α .pres-* _ _
Field-structure ℓ .id-hom-unique α β i .Field-on.1r = α .pres-id i
Field-structure ℓ .id-hom-unique α β i .Field-on._*_ x y = α .pres-* x y i
Field-structure ℓ .id-hom-unique α β i .Field-on._+_ x y = α .pres-+ x y i
Field-structure ℓ .id-hom-unique {s = s} {t} α β i .Field-on.has-is-field =
  is-prop→pathp
    (λ i → hlevel {T = is-field (α .pres-id i)
      (λ x y → α .pres-* x y i) (λ x y → α .pres-+ x y i)} 1)
    (s .Field-on.has-is-field) (t .Field-on.has-is-field) i

Fields : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Fields _ = Structured-objects (Field-structure _)
module Fields {ℓ} = Cat.Reasoning (Fields ℓ)

Field : ∀ ℓ → Type (lsuc ℓ)
Field ℓ = Fields.Ob
```

## In components

We give a more elementary description of fields, which is suitable for
_constructing_ values of the record type `Field`{.Agda} above. This
re-expresses the data included in the definition of a field with the
least amount of redundancy possible, in the most direct terms
possible: A field is a set, equipped with two binary operations $*$ and
$+$, such that $*$ distributes over $+$ on either side; $+$ is an
abelian group; and $*$ is a monoid.

```agda
record make-field {ℓ} (R : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    field-is-set : is-set R

    -- R is an abelian group:
    0R      : R
    _+_     : R → R → R
    -_      : R → R
    +-idl   : ∀ x → 0R + x ≡ x
    +-invr  : ∀ x → x + (- x) ≡ 0R
    +-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
    +-comm  : ∀ x y → x + y ≡ y + x

    -- R is a *-abelian group
    1R      : R
    _*_     : R → R → R
    _÷      : R → R
    *-idl   : ∀ x → 1R * x ≡ x
    *-idr   : ∀ x → x * 1R ≡ x
    *-invr  : ∀ x → x * (1R * x) ≡ x
    *-assoc : ∀ x y z → x * (y * z) ≡ (x * y) * z
    *-comm : ∀ x y → x * y ≡ y * x

    -- Multiplication is bilinear:
    *-distribl : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ x y z → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  to-field-on : Field-on R
  to-field-on = field' where
    open is-field hiding (-_ ; +-invr ; +-invl ; *-distribl ; *-distribr ; +-idl ; +-idr)
    module *R = is-monoid
    open is-monoid


    -- All in copatterns to prevent the unfolding from exploding on you
    field' : Field-on R
    field' .Field-on.1r = 1R
    field' .Field-on._*_ = _*_
    field' .Field-on._+_ = _+_
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.unit =  1R
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.inverse x = x ÷
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .associative = *-assoc _ _ _
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .has-is-magma = record { has-is-set = field-is-set }
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idl = *-idl _
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idr = *-comm _ _ ∙ *-idl _
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.inversel = {!λ i -> 0R!}
    field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group .is-group.inverser = {!*-invr _!}
    field' .Field-on.has-is-field .*-group .is-abelian-group.commutes = *-comm _ _
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.unit = 0R
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .has-is-magma = record { has-is-set = field-is-set }
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .associative = +-assoc _ _ _
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idl = +-idl _
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idr = +-comm _ _ ∙ +-idl _
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inverse = -_
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inversel = +-comm _ _ ∙ +-invr _
    field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inverser = +-invr _
    field' .Field-on.has-is-field .+-group .is-abelian-group.commutes = +-comm _ _
    field' .Field-on.has-is-field .is-field.*-distribl = *-distribl _ _ _
    field' .Field-on.has-is-field .is-field.*-distribr = *-distribr _ _ _

  to-field : Field ℓ
  to-field .fst = el R field-is-set
  to-field .snd = to-field-on

open make-field using (to-field ; to-field-on) public
```
-->

This data is missing (by design, actually!) one condition which we would
expect: $0 \ne 1$. We exploit this to give our first example of a field,
the **zero field**, which has carrier set the `unit`{.Agda ident=⊤} ---
the type with one object.

Despite the name, the zero field is not the [zero object] in the category
of fields: it is the [[terminal object]]. In the category of fields, the
initial object is the field $\bb{Z}$, which is very far (infinitely far!)
from having a single element. It's called the "zero field" because it has
one element $x$, which must be the additive identity, hence we call it
$0$. But it's also the multiplicative identity, so we might also call
the field $\{*\}$ the _One Field_, which would be objectively cooler.

[zero object]: Cat.Diagram.Zero.html

```agda
Zero-field : Field lzero
Zero-field = to-field {R = ⊤} λ where
  .make-field.field-is-set _ _ _ _ _ _ → tt
  .make-field.0R                      → tt
  .make-field._+_ _ _                 → tt
  .make-field.-_  _                   → tt
  .make-field.+-idl  _ _              → tt
  .make-field.+-invr _ _              → tt
  .make-field.+-assoc _ _ _ _         → tt
  .make-field.+-comm _ _ _            → tt
  .make-field.1R                      → tt
  .make-field._*_ _ _                 → tt
  .make-field._÷ _                 → tt
  .make-field.*-idl _ _               → tt
  .make-field.*-idr _ _               → tt
  .make-field.*-invr _ _              → tt
  .make-field.*-assoc _ _ _ _         → tt
  .make-field.*-comm _ _ _            → tt
  .make-field.*-distribl _ _ _ _      → tt
  .make-field.*-distribr _ _ _ _      → tt

  -- .make-field.
```

Fields, unlike other categories of algebraic structures (like that of
[groups] or [abelian groups]), are structured enough to differentiate
between the initial and terminal objects. As mentioned above, the
initial object is the field $\bb{Z}$, and the terminal field is the zero
field. As for why this happens, consider that, since field homomorphisms
must preserve the unit^[being homomorphisms for the additive group, they
automatically preserve zero], it is impossible to have a field
homomorphism $h : 0 \to R$ unless $0 = h(0) = h(1) = 1$ in $R$.

[groups]: Algebra.Group.html
[abelian groups]: Algebra.Group.Ab.html

```agda

-- open import Data.Int.DivMod
-- open import Data.Int.Base

-- No field instance for ℤ

-- ℤ : Field lzero
-- ℤ = to-field {R = Int} λ where
--   .make-field.field-is-set → hlevel 2
--   .make-field.1R         → 1
--   .make-field.0R         → 0
--   .make-field._+_        → _+ℤ_
--   .make-field.-_         → negℤ
--   .make-field._*_        → _*ℤ_
--   .make-field.+-idl      → +ℤ-zerol
--   .make-field.+-invr     → +ℤ-invr
--   .make-field.+-assoc    → +ℤ-assoc
--   .make-field.+-comm     → +ℤ-commutative
--   .make-field.*-idl      → *ℤ-onel
--   .make-field.*-idr      → *ℤ-oner
--   .make-field.*-invr (pos (suc x)) i → {!(pos x) /ℤ x!}
--   .make-field.*-invr (negsuc x) i → {!!}
--   .make-field.*-assoc    → *ℤ-associative
--   .make-field.*-distribl → *ℤ-distribl
--   .make-field.*-distribr → *ℤ-distribr
--   .make-field._÷ → λ x → {!!}
```




-- <!--
-- ```agda
--   to-field-on : Field-on R
--   to-field-on = field' where
--     open is-field hiding (-_ ; +-invr ; +-invl ; *-distribl ; *-distribr ; *-idl ; *-idr ; +-idl ; +-idr)
--     open is-monoid

--     -- All in copatterns to prevent the unfolding from exploding on you
--     field' : Field-on R
--     field' .Field-on.1r = 1R
--     field' .Field-on._*_ = _*_
--     field' .Field-on._+_ = _+_
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.unit = 0R
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .has-is-magma = record { has-is-set = field-is-set }
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .associative = +-assoc _ _ _
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idl = +-idl _
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idr = +-comm _ _ ∙ +-idl _
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inverse = -_
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inversel = +-comm _ _ ∙ +-invr _
--     field' .Field-on.has-is-field .+-group .is-abelian-group.has-is-group .is-group.inverser = +-invr _
--     field' .Field-on.has-is-field .+-group .is-abelian-group.commutes = +-comm _ _
--     field' .Field-on.has-is-field .is-field.*-distribl = *-distribl _ _ _
--     field' .Field-on.has-is-field .is-field.*-distribr = *-distribr _ _ _
--     field' .Field-on.has-is-field .*-group .is-abelian-group.has-is-group.is-semigroup.has-is-magma = record { has-is-set = field-is-set }
--     field' .Field-on.has-is-field .*-group .has-is-group .has-is-semigroup .is-semigroup.associative = *-assoc _ _ _
--     field' .Field-on.has-is-field .*-group .idl = *-idl _
--     field' .Field-on.has-is-field .*-group .idr = *-idr _

-- open make-field using (to-field ; to-field-on) public
-- ```
-- -->

-- This data is missing (by design, actually!) one condition which we would
-- expect: $0 \ne 1$. We exploit this to give our first example of a field,
-- the **zero field**, which has carrier set the `unit`{.Agda ident=⊤} ---
-- the type with one object.

-- Despite the name, the zero field is not the [zero object] in the category
-- of fields: it is the [[terminal object]]. In the category of fields, the
-- initial object is the field $\bb{Z}$, which is very far (infinitely far!)
-- from having a single element. It's called the "zero field" because it has
-- one element $x$, which must be the additive identity, hence we call it
-- $0$. But it's also the multiplicative identity, so we might also call
-- the field $\{*\}$ the _One Field_, which would be objectively cooler.

-- [zero object]: Cat.Diagram.Zero.html

-- ```agda
-- Zero-field : Field lzero
-- Zero-field = to-field {R = ⊤} λ where
--   .make-field.field-is-set _ _ _ _ _ _ → tt
--   .make-field.0R                      → tt
--   .make-field._+_ _ _                 → tt
--   .make-field.-_  _                   → tt
--   .make-field.+-idl  _ _              → tt
--   .make-field.+-invr _ _              → tt
--   .make-field.+-assoc _ _ _ _         → tt
--   .make-field.+-comm _ _ _            → tt
--   .make-field.1R                      → tt
--   .make-field._*_ _ _                 → tt
--   .make-field.*-idl _ _               → tt
--   .make-field.*-idr _ _               → tt
--   .make-field.*-assoc _ _ _ _         → tt
--   .make-field.*-distribl _ _ _ _      → tt
--   .make-field.*-distribr _ _ _ _      → tt
-- ```

-- Fields, unlike other categories of algebraic structures (like that of
-- [groups] or [abelian groups]), are structured enough to differentiate
-- between the initial and terminal objects. As mentioned above, the
-- initial object is the field $\bb{Z}$, and the terminal field is the zero
-- field. As for why this happens, consider that, since field homomorphisms
-- must preserve the unit^[being homomorphisms for the additive group, they
-- automatically preserve zero], it is impossible to have a field
-- homomorphism $h : 0 \to R$ unless $0 = h(0) = h(1) = 1$ in $R$.

-- [groups]: Algebra.Group.html
-- [abelian groups]: Algebra.Group.Ab.html

-- ```agda
-- ℤ : Field lzero
-- ℤ = to-field {R = Int} λ where
--   .make-field.field-is-set → hlevel 2
--   .make-field.1R         → 1
--   .make-field.0R         → 0
--   .make-field._+_        → _+ℤ_
--   .make-field.-_         → negℤ
--   .make-field._*_        → _*ℤ_
--   .make-field.+-idl      → +ℤ-zerol
--   .make-field.+-invr     → +ℤ-invr
--   .make-field.+-assoc    → +ℤ-assoc
--   .make-field.+-comm     → +ℤ-commutative
--   .make-field.*-idl      → *ℤ-onel
--   .make-field.*-idr      → *ℤ-oner
--   .make-field.*-assoc    → *ℤ-associative
--   .make-field.*-distribl → *ℤ-distribl
--   .make-field.*-distribr → *ℤ-distribr
-- ```
