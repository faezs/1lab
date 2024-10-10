<!--
```agda


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
open import Algebra.Field

import Cat.Reasoning
```
-->


```agda
module Algebra.Group.Representation where
```

```agda
open is-group-hom
open Functor


invertible-matrix : {F : Field} → Nat → Nat → Set
invertible-matrix {F} n m = F × n × m

record GroupRepresentation (G : Group) (F : Field) (n : Nat) : Set where
  field
    rep : G → invertible-matrix F n n
    hom : is-group-hom rep
```



# Group representations {defines="group-representations"}
