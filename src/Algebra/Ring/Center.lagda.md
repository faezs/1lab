<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring

import Algebra.Ring.Reasoning

open make-ring
open is-ring-hom
```
-->

```agda
module Algebra.Ring.Center {ℓ} (C : Ring ℓ) where
```

<!--
```agda
private
  module C = Ring-on (C .snd)
  module Cr = Algebra.Ring.Reasoning C
```
-->

# The centre of a ring {defines="centre-of-a-ring central-element"}

An element of a ring is **central** when it commutes with everything;
the central elements form a *commutative* subring, the **centre**.
The centre is the bridge between commutative and noncommutative
algebra: a map from a commutative ring into a noncommutative one is
the same thing as a map into its centre, which is how the polynomial
(even) coordinates of a super space coexist with its anticommuting
(odd) ones.

```agda
is-central : ⌞ C ⌟ → Type ℓ
is-central c = ∀ y → c C.* y ≡ y C.* c

is-central-is-prop : ∀ c → is-prop (is-central c)
is-central-is-prop c = hlevel 1
```

Centrality is closed under all the ring operations, so the centre is
a ring; and any two central elements commute *with each other*, so it
is commutative.

```agda
Centre : CRing ℓ
Centre .fst = el! (Σ ⌞ C ⌟ is-central)
Centre .snd .CRing-on.has-ring-on = to-ring-on mk where
  mk : make-ring (Σ ⌞ C ⌟ is-central)
  mk .ring-is-set = hlevel 2
  mk .0R = C.0r , λ y → Cr.*-zerol ∙ sym Cr.*-zeror
  mk .1R = C.1r , λ y → C.*-idl ∙ sym C.*-idr
  mk ._+_ (c , p) (d , q) = c C.+ d , λ y →
    C.*-distribr ∙ ap₂ C._+_ (p y) (q y) ∙ sym C.*-distribl
  mk .-_ (c , p) = (C.- c) , λ y →
    Cr.*-negatel ∙ ap C.-_ (p y) ∙ sym Cr.*-negater
  mk ._*_ (c , p) (d , q) = c C.* d , λ y →
      sym C.*-associative
    ∙ ap (c C.*_) (q y)
    ∙ C.*-associative
    ∙ ap (C._* d) (p y)
    ∙ sym C.*-associative
  mk .+-idl x = Σ-prop-path is-central-is-prop C.+-idl
  mk .+-invr x = Σ-prop-path is-central-is-prop C.+-invr
  mk .+-assoc x y z = Σ-prop-path is-central-is-prop C.+-associative
  mk .+-comm x y = Σ-prop-path is-central-is-prop C.+-commutes
  mk .*-idl x = Σ-prop-path is-central-is-prop C.*-idl
  mk .*-idr x = Σ-prop-path is-central-is-prop C.*-idr
  mk .*-assoc x y z = Σ-prop-path is-central-is-prop C.*-associative
  mk .*-distribl x y z = Σ-prop-path is-central-is-prop C.*-distribl
  mk .*-distribr x y z = Σ-prop-path is-central-is-prop C.*-distribr
Centre .snd .CRing-on.*-commutes {c , p} {d , q} =
  Σ-prop-path is-central-is-prop (p d)
```

The projection back to the ring is a homomorphism, tautologically.

```agda
centre-proj : ⌞ Centre ⌟ → ⌞ C ⌟
centre-proj = fst

centre-proj-is-ring-hom
  : is-ring-hom (Centre .snd .CRing-on.has-ring-on) (C .snd) centre-proj
centre-proj-is-ring-hom .pres-id = refl
centre-proj-is-ring-hom .pres-+ x y = refl
centre-proj-is-ring-hom .pres-* x y = refl
```
