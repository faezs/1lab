<!--
```agda
open import 1Lab.Prelude

open import Data.Set.Coequaliser

open import Data.Rational.Order
open import Data.Rational.Base hiding (_/_)
open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Base
open import Data.Real.Smooth
open import Data.Real.Smooth.Partial
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Germ where
```

# Germs of smooth functions at a rational point {defines="smooth-germ"}

The paper's (5) and (6) take *germs* of plots along a directed
family of shrinking neighbourhoods, and (7) asks for the analytic
content of localisation: identifying two locally-defined smooth
functions when they agree on some smaller neighbourhood of a point.
Over the constructive substrate of [[rational
boxes|rational-box]] the directed family is the sequential one: the
boxes centred at a rational point $c$ whose radius halves at each
stage. A germ at $c$ is then a [[partial smooth
function|partial-smooth-function]] defined on *some* box of the
family, and two of them are identified when they agree on a common
refinement — a set-quotient, exactly as in the site-theoretic
picture, but with the colimit taken over $\bN$ rather than over all
opens. This module builds that quotient and its restriction maps.

## Shrinking radii

The radii $1, \tfrac12, \tfrac14, \dots$ are positive and
antitone: this is all the order theory the directed family needs.

```agda
radius : Nat → Ratio
radius zero    = 1
radius (suc k) = half (radius k)

radius-pos : ∀ k → 0 < radius k
radius-pos zero    = 0<1'
radius-pos (suc k) = half-pos (radius-pos k)

radius-suc : ∀ k → radius (suc k) ≤ radius k
radius-suc k = <-weaken (half-lt (radius-pos k))
```

<!--
```agda
private
  inv2-pos : 0 < invℚ 2
  inv2-pos = decide!

  half-mono : ∀ {x y} → x ≤ y → half x ≤ half y
  half-mono p = *ℚ-preserves-≤r (invℚ 2) p (<-weaken inv2-pos)
```
-->

Antitonicity is by simultaneous induction: on the zero side the
single-step inequalities compose, and on the successor side halving
is monotone.

```agda
radius-anti : ∀ {k m} → k Nat.≤ m → radius m ≤ radius k
radius-anti {k} {m} le = go k m le where
  go : ∀ k m → k Nat.≤ m → radius m ≤ radius k
  go zero    zero    _  = ≤-refl
  go zero    (suc m) _  = ≤-trans (radius-suc m) (go zero m Nat.0≤x)
  go (suc k) zero    le = absurd (Nat.¬suc≤0 le)
  go (suc k) (suc m) le = half-mono (go k m (Nat.≤-peel le))
```

## The boxes at a centre

The $k$-th box at a rational centre $c$ has each side the open
interval of radius `radius k` around the corresponding coordinate.

```agda
boxAt : ∀ {n} → (Fin n → Ratio) → Nat → Box n
boxAt c k i = c i +ℚ (-ℚ radius k) , c i +ℚ radius k
```

Membership is antitone in the stage. The comparison happens
entirely at the rational level: a point above the wider lower
endpoint is above the narrower one because the strict cut witness
— some rational strictly between endpoint and point — still works,
by mixed rational transitivity.

```agda
ratℝ≤-<ᴿ-trans
  : ∀ {p q} (x : ℝ) → p ≤ q → ratℝ q <ᴿ x → ratℝ p <ᴿ x
ratℝ≤-<ᴿ-trans x pq = ∥-∥-map λ (r , q<r , lr) →
  r , ≤-<-trans pq q<r , lr

<ᴿ-ratℝ≤-trans
  : ∀ {q p} (x : ℝ) → x <ᴿ ratℝ q → q ≤ p → x <ᴿ ratℝ p
<ᴿ-ratℝ≤-trans x h qp = ∥-∥-map
  (λ (r , ur , r<q) → r , ur , <-≤-trans r<q qp) h

∈ᵇ-anti
  : ∀ {n} {c : Fin n → Ratio} {k m} (x : Fin n → ℝ)
  → k Nat.≤ m → x ∈ᵇ boxAt c m → x ∈ᵇ boxAt c k
∈ᵇ-anti {c = c} {k} {m} x le px i =
    ratℝ≤-<ᴿ-trans (x i) lo-le (px i .fst)
  , <ᴿ-ratℝ≤-trans (x i) (px i .snd) hi-le
  where
  rm≤rk : radius m ≤ radius k
  rm≤rk = radius-anti le

  lo-le : (c i +ℚ (-ℚ radius k)) ≤ (c i +ℚ (-ℚ radius m))
  lo-le = +ℚ-preserves-≤ (≤-refl {c i}) (negℚ-anti-≤ rm≤rk)

  hi-le : (c i +ℚ radius m) ≤ (c i +ℚ radius k)
  hi-le = +ℚ-preserves-≤ (≤-refl {c i}) rm≤rk
```

A partial function on an earlier box restricts to any later one —
these are the restriction maps of (6), here indexed by
$k \le m$ in $\bN$.

```agda
shrinkPF
  : ∀ {n} {c : Fin n → Ratio} {k m} → k Nat.≤ m
  → PFun n (boxAt c k) → PFun n (boxAt c m)
shrinkPF le f x px = f x (∈ᵇ-anti x le px)
```

## Towers restrict along box inclusions

Smoothness restricts too, and it is no harder to prove this for an
arbitrary pair of boxes related by *membership inclusion* than for
the concentric family: containment of boxes is the statement that
every point of the smaller is a point of the larger.

```agda
sub-box : ∀ {n} → Box n → Box n → Type
sub-box {n} B B' = (x : Fin n → ℝ) → x ∈ᵇ B' → x ∈ᵇ B
```

The [[Hadamard tower|hadamard-tower]] on a box also quantifies over
*interval* points in each direction, so we need to extract, from
membership inclusion, the inclusion of the $i$-th intervals. Given
any point $x$ of the smaller box, overwriting its $i$-th coordinate
with a point $t$ of the smaller interval stays in the smaller box;
pushing through the containment and projecting the $i$-th
coordinate gives the bounds for $t$ in the larger interval.

<!--
```agda
private
  set-same : ∀ {n} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) → set x i t i ≡ t
  set-same x i t with Discrete-Fin .decide i i
  ... | yes _ = refl
  ... | no ¬p = absurd (¬p refl)
```
-->

```agda
sub-interval
  : ∀ {n} {B B' : Box n} → sub-box B B' → (i : Fin n)
  → (x : Fin n → ℝ) → x ∈ᵇ B' → (t : ℝ)
  → (ratℝ (B' i .fst) <ᴿ t) × (t <ᴿ ratℝ (B' i .snd))
  → (ratℝ (B  i .fst) <ᴿ t) × (t <ᴿ ratℝ (B  i .snd))
sub-interval {B = B} {B'} sub i x px t pt =
  subst (λ s → (ratℝ (B i .fst) <ᴿ s) × (s <ᴿ ratℝ (B i .snd)))
    (set-same x i t)
    (sub (set x i t) (set-∈ᵇ i px pt) i)
```

Containment then propagates to the cylinders: the fresh coordinate
of a cylinder point is a point of the $i$-th interval, and its tail
is a point of the base box.

```agda
cyl-sub
  : ∀ {n} {B B' : Box n} → sub-box B B' → (i : Fin n)
  → sub-box (cylᵇ B i) (cylᵇ B' i)
cyl-sub {n} {B} {B'} sub i x px = go where
  y : Fin n → ℝ
  y j = x (fsuc j)

  py : y ∈ᵇ B'
  py j = px (fsuc j)

  go : x ∈ᵇ cylᵇ B i
  go l with fin-view l
  ... | zero  = sub-interval sub i y py (x fzero) (px fzero)
  ... | suc j = sub y py j
```

Restricting a tower along a containment is now structural
recursion. The two occurrences of a membership proof that do not
line up definitionally are bridged through `∈ᵇ-is-prop`{.Agda}: a
partial function applied to a fixed point is a function of a
proposition, so it cannot see which witness it is given.

```agda
towerOn-shrink
  : ∀ k {n} {B B' : Box n} (sub : sub-box B B') (f : PFun n B)
  → TowerOnTo k B f
  → TowerOnTo k B' (λ x px → f x (sub x px))
towerOn-shrink zero    sub f T = lift tt
towerOn-shrink (suc k) {n} {B} {B'} sub f T i =
  let
    g  = T i .fst
    q  = T i .snd .fst
    Tg = T i .snd .snd
  in
    (λ x px → g x (cyl-sub sub i x px))
  , (λ x px t pt →
        ap (λ p → f x (sub x px) −ᴿ f (set x i t) p)
          (∈ᵇ-is-prop (set x i t) B
            (sub (set x i t) (set-∈ᵇ i px pt))
            (set-∈ᵇ i (sub x px) (sub-interval sub i x px t pt)))
      ∙ q x (sub x px) t (sub-interval sub i x px t pt)
      ∙ ap (λ p → (x i −ᴿ t) *ᴿ g (cons t x) p)
          (∈ᵇ-is-prop (cons t x) (cylᵇ B i)
            (cons-∈ᵇ i (sub-interval sub i x px t pt) (sub x px))
            (cyl-sub sub i (cons t x) (cons-∈ᵇ i pt px))))
  , towerOn-shrink k (cyl-sub sub i) g Tg

smoothOn-shrink
  : ∀ {n} {B B' : Box n} (sub : sub-box B B') (f : PFun n B)
  → SmoothOn B f → SmoothOn B' (λ x px → f x (sub x px))
smoothOn-shrink sub f S k = towerOn-shrink k sub f (S k)
```

For the concentric family this specialises to the restriction maps
acting on smooth structures:

```agda
shrink-smooth
  : ∀ {n} {c : Fin n → Ratio} {k m} (le : k Nat.≤ m)
    {f : PFun n (boxAt c k)}
  → SmoothOn (boxAt c k) f → SmoothOn (boxAt c m) (shrinkPF le f)
shrink-smooth le {f} = smoothOn-shrink (λ x px → ∈ᵇ-anti x le px) f
```

## The set of germs

A *pre-germ* at $c$ is a stage together with a partial function on
the box of that stage and (mere) smoothness on it. Two pre-germs
present the same germ when they agree pointwise on some common
later stage — the paper's identification of plots that coincide on
a smaller neighbourhood.

```agda
PreGerm : ∀ n → (Fin n → Ratio) → Type
PreGerm n c =
  Σ[ k ∈ Nat ] Σ[ f ∈ PFun n (boxAt c k) ] ∥ SmoothOn (boxAt c k) f ∥

germ-rel : ∀ {n} {c : Fin n → Ratio} → PreGerm n c → PreGerm n c → Type
germ-rel {n} {c} (k , f , _) (k' , f' , _) =
  ∥ (Σ[ m ∈ Nat ] Σ[ lk ∈ (k Nat.≤ m) ] Σ[ lk' ∈ (k' Nat.≤ m) ]
      ((x : Fin n → ℝ) (px : x ∈ᵇ boxAt c m)
        → f x (∈ᵇ-anti x lk px) ≡ f' x (∈ᵇ-anti x lk' px))) ∥
```

The germ set is the [[set quotient|set-coequaliser]] by this
relation: the sequential, rational-box form of the colimit over
shrinking opens in (5). It is honestly weaker than the
site-theoretic colimit — only the countable concentric family at a
*rational* centre is quantified over, not all opens containing an
arbitrary point — but over this family the restriction maps and the
quotient behave exactly as (5)–(7) prescribe.

```agda
Germ : ∀ n → (Fin n → Ratio) → Type
Germ n c = PreGerm n c / germ-rel {n} {c}
```

Every globally smooth function has a germ at every rational centre,
through the stage-zero box:

```agda
germ : ∀ {n} (c : Fin n → Ratio) (f : Fun n) → ∥ Smooth n f ∥ → Germ n c
germ {n} c f s = inc
  ( 0
  , restrict (boxAt c 0) f
  , ∥-∥-map (smooth-restrict (boxAt c 0)) s)
```

And restricting a pre-germ to a later stage does not change its
germ: the common refinement is the later stage itself, with the
pointwise agreement holding because both sides are the same
function applied to two witnesses of the same proposition.

```agda
germ-shrink
  : ∀ {n} {c : Fin n → Ratio} {k m} (le : k Nat.≤ m)
    (f : PFun n (boxAt c k)) (s : ∥ SmoothOn (boxAt c k) f ∥)
  → Path (Germ n c)
      (inc (k , f , s))
      (inc (m , shrinkPF le f , ∥-∥-map (shrink-smooth le) s))
germ-shrink {n} {c} {k} {m} le f s = quot (inc
  ( m , le , Nat.≤-refl
  , λ x px → ap (f x) (∈ᵇ-is-prop x (boxAt c k) _ _)))
```

What is *not* built here is the ring of germs: pointwise addition
and multiplication of pre-germs would need box-relative closure
combinators for the Hadamard towers (`towerOn-add`,
`towerOn-mul`), which the partial-smoothness layer does not yet
provide.
