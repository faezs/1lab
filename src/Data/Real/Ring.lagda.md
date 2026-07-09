<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Base
```
-->
```agda
module Data.Real.Ring where
```

# The Dedekind reals as a commutative ring

Every axiom of a [[commutative ring]] has now been verified for the
[[Dedekind reals]] $\bR$, with **zero postulates**: addition is an
[[abelian group]] (`+ᴿ-assoc`{.Agda}, `+ᴿ-comm`{.Agda},
`+ᴿ-idr`{.Agda}, `+ᴿ-invr`{.Agda}), multiplication is a commutative
monoid (`*ᴿ-assoc`{.Agda}, `*ᴿ-comm`{.Agda}, `*ᴿ-idl`{.Agda},
`*ᴿ-idr`{.Agda}), and the two are linked by
[[distributivity|real-multiplication]] (`*ᴿ-distribˡ`{.Agda},
`*ᴿ-distribʳ`{.Agda}). The `make-ring`{.Agda} smart constructor
assembles them into a bundled `Ring`{.Agda}; adding commutativity of
multiplication upgrades it to a `CRing`{.Agda}.

The multiplicative laws are the hard-won ones: they come from the
sign-analysis-free *interval product* of located two-sided cuts,
whose distributivity and associativity each required a bracket
`δ`/`η`-budget against the four-fold minimum (associativity being
exact once the interval product is seen to associate on the nose).

```agda
ℝ-ring : Ring lzero
ℝ-ring = to-ring {R = ℝ} λ where
  .make-ring.ring-is-set   → ℝ-is-set
  .make-ring.0R            → 0ᴿ
  .make-ring._+_           → _+ᴿ_
  .make-ring.-_            → -ᴿ_
  .make-ring.+-idl x       → +ᴿ-comm 0ᴿ x ∙ +ᴿ-idr x
  .make-ring.+-invr        → +ᴿ-invr
  .make-ring.+-assoc       → +ᴿ-assoc
  .make-ring.+-comm        → +ᴿ-comm
  .make-ring.1R            → 1ᴿ
  .make-ring._*_           → _*ᴿ_
  .make-ring.*-idl         → *ᴿ-idl
  .make-ring.*-idr         → *ᴿ-idr
  .make-ring.*-assoc x y z → sym (*ᴿ-assoc x y z)
  .make-ring.*-distribl    → *ᴿ-distribˡ
  .make-ring.*-distribr    → *ᴿ-distribʳ

ℝ-comm : CRing lzero
ℝ-comm = record
  { fst = el! ℝ
  ; snd = record
    { has-ring-on = ℝ-ring .snd
    ; *-commutes  = λ {x y} → *ᴿ-comm x y
    }
  }
```
