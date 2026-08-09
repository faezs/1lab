<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Cat.Displayed.Total

import Algebra.Ring.Reasoning
import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.Weil {ℓ} (R : CRing ℓ) where
```

<!--
```agda
private
  module R = CRing-on (R .snd)
  module CR = Cat.Reasoning (CRings ℓ)

open make-ring
open is-ring-hom
```
-->

# The second-order Weil algebra {defines="second-order-weil-algebra"}

The **dual numbers** $R[\epsilon] = R[\delta]/(\delta^2)$ probe a space
to first order: a map out of them is a tangent vector. To reach
*jets* — second-order approximations, the data needed for
acceleration as well as velocity — the truncation must be relaxed by
one more power. The **second-order Weil algebra** $W_2 = R[\delta]/
(\delta^3)$ keeps $1, \delta, \delta^2$ and kills $\delta^3$: its
elements are triples $(a, b, c)$ standing for $a + b\delta +
c\delta^2$, and its arithmetic is truncated convolution, exactly the
polynomial product with every term of degree $\geq 3$ discarded.

As with the dual numbers, the truncation is so mild that no quotient
construction is needed: the carrier is simply $R \times R \times R$,
and every ring law is decided by the [[commutative ring
solver|ring-solver]], applied three times per equation (once per
component).

The ring axioms are proved by expanding both sides of each triple
equation into the *three* scalar equations the solver can discharge,
one per component, with variables named for their position
(zeroth/first/second coefficient of each of up to three triples).

<!--
```agda
private abstract
  l+idl : ∀ a → R.0r R.+ a ≡ a
  l+idl a = cring! R

  l+invr : ∀ a → a R.+ (R.- a) ≡ R.0r
  l+invr a = cring! R

  +-assoc-0 : ∀ a₀ c₀ e₀ → a₀ R.+ (c₀ R.+ e₀) ≡ (a₀ R.+ c₀) R.+ e₀
  +-assoc-0 a₀ c₀ e₀ = cring! R

  l+comm : ∀ a c → a R.+ c ≡ c R.+ a
  l+comm a c = cring! R

  *-idl-0 : ∀ a₀ → R.1r R.* a₀ ≡ a₀
  *-idl-0 a₀ = cring! R

  *-idl-1 : ∀ a₀ a₁ → R.1r R.* a₁ R.+ R.0r R.* a₀ ≡ a₁
  *-idl-1 a₀ a₁ = cring! R

  *-idl-2
    : ∀ a₀ a₁ a₂
    → R.1r R.* a₂ R.+ R.0r R.* a₁ R.+ R.0r R.* a₀ ≡ a₂
  *-idl-2 a₀ a₁ a₂ = cring! R

  *-idr-0 : ∀ a₀ → a₀ R.* R.1r ≡ a₀
  *-idr-0 a₀ = cring! R

  *-idr-1 : ∀ a₀ a₁ → a₀ R.* R.0r R.+ a₁ R.* R.1r ≡ a₁
  *-idr-1 a₀ a₁ = cring! R

  *-idr-2
    : ∀ a₀ a₁ a₂
    → a₀ R.* R.0r R.+ a₁ R.* R.0r R.+ a₂ R.* R.1r ≡ a₂
  *-idr-2 a₀ a₁ a₂ = cring! R

  *-assoc-0 : ∀ a₀ c₀ e₀ → a₀ R.* (c₀ R.* e₀) ≡ (a₀ R.* c₀) R.* e₀
  *-assoc-0 a₀ c₀ e₀ = cring! R

  *-assoc-1
    : ∀ a₀ a₁ c₀ c₁ e₀ e₁
    → a₀ R.* (c₀ R.* e₁ R.+ c₁ R.* e₀) R.+ a₁ R.* (c₀ R.* e₀)
    ≡ (a₀ R.* c₀) R.* e₁ R.+ (a₀ R.* c₁ R.+ a₁ R.* c₀) R.* e₀
  *-assoc-1 a₀ a₁ c₀ c₁ e₀ e₁ = cring! R

  *-assoc-2
    : ∀ a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂
    → a₀ R.* (c₀ R.* e₂ R.+ c₁ R.* e₁ R.+ c₂ R.* e₀)
      R.+ a₁ R.* (c₀ R.* e₁ R.+ c₁ R.* e₀) R.+ a₂ R.* (c₀ R.* e₀)
    ≡ (a₀ R.* c₀) R.* e₂ R.+ (a₀ R.* c₁ R.+ a₁ R.* c₀) R.* e₁
      R.+ (a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀) R.* e₀
  *-assoc-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂ = cring! R

  *-distl-0 : ∀ a₀ c₀ e₀ → a₀ R.* (c₀ R.+ e₀) ≡ a₀ R.* c₀ R.+ a₀ R.* e₀
  *-distl-0 a₀ c₀ e₀ = cring! R

  *-distl-1
    : ∀ a₀ a₁ c₀ c₁ e₀ e₁
    → a₀ R.* (c₁ R.+ e₁) R.+ a₁ R.* (c₀ R.+ e₀)
    ≡ (a₀ R.* c₁ R.+ a₁ R.* c₀) R.+ (a₀ R.* e₁ R.+ a₁ R.* e₀)
  *-distl-1 a₀ a₁ c₀ c₁ e₀ e₁ = cring! R

  *-distl-2
    : ∀ a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂
    → a₀ R.* (c₂ R.+ e₂) R.+ a₁ R.* (c₁ R.+ e₁) R.+ a₂ R.* (c₀ R.+ e₀)
    ≡ (a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀)
      R.+ (a₀ R.* e₂ R.+ a₁ R.* e₁ R.+ a₂ R.* e₀)
  *-distl-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂ = cring! R

  *-distr-0 : ∀ a₀ c₀ e₀ → (c₀ R.+ e₀) R.* a₀ ≡ c₀ R.* a₀ R.+ e₀ R.* a₀
  *-distr-0 a₀ c₀ e₀ = cring! R

  *-distr-1
    : ∀ a₀ a₁ c₀ c₁ e₀ e₁
    → (c₀ R.+ e₀) R.* a₁ R.+ (c₁ R.+ e₁) R.* a₀
    ≡ (c₀ R.* a₁ R.+ c₁ R.* a₀) R.+ (e₀ R.* a₁ R.+ e₁ R.* a₀)
  *-distr-1 a₀ a₁ c₀ c₁ e₀ e₁ = cring! R

  *-distr-2
    : ∀ a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂
    → (c₀ R.+ e₀) R.* a₂ R.+ (c₁ R.+ e₁) R.* a₁ R.+ (c₂ R.+ e₂) R.* a₀
    ≡ (c₀ R.* a₂ R.+ c₁ R.* a₁ R.+ c₂ R.* a₀)
      R.+ (e₀ R.* a₂ R.+ e₁ R.* a₁ R.+ e₂ R.* a₀)
  *-distr-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂ = cring! R

  *-comm-0 : ∀ a₀ c₀ → a₀ R.* c₀ ≡ c₀ R.* a₀
  *-comm-0 a₀ c₀ = cring! R

  *-comm-1 : ∀ a₀ a₁ c₀ c₁ → a₀ R.* c₁ R.+ a₁ R.* c₀ ≡ c₀ R.* a₁ R.+ c₁ R.* a₀
  *-comm-1 a₀ a₁ c₀ c₁ = cring! R

  *-comm-2
    : ∀ a₀ a₁ a₂ c₀ c₁ c₂
    → a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀
    ≡ c₀ R.* a₂ R.+ c₁ R.* a₁ R.+ c₂ R.* a₀
  *-comm-2 a₀ a₁ a₂ c₀ c₁ c₂ = cring! R
```
-->

```agda
W₂ : CRing ℓ
W₂ .fst = el! (⌞ R ⌟ × ⌞ R ⌟ × ⌞ R ⌟)
W₂ .snd .CRing-on.has-ring-on = to-ring-on mk where
  mk : make-ring (⌞ R ⌟ × ⌞ R ⌟ × ⌞ R ⌟)
  mk .ring-is-set = hlevel 2
  mk .0R = R.0r , R.0r , R.0r
  mk ._+_ (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) =
    a₀ R.+ c₀ , a₁ R.+ c₁ , a₂ R.+ c₂
  mk .-_ (a₀ , a₁ , a₂) = R.- a₀ , R.- a₁ , R.- a₂
  mk .+-idl (a₀ , a₁ , a₂) =
    ap₂ _,_ (l+idl a₀) (ap₂ _,_ (l+idl a₁) (l+idl a₂))
  mk .+-invr (a₀ , a₁ , a₂) =
    ap₂ _,_ (l+invr a₀) (ap₂ _,_ (l+invr a₁) (l+invr a₂))
  mk .+-assoc (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) (e₀ , e₁ , e₂) =
    ap₂ _,_ (+-assoc-0 a₀ c₀ e₀)
      (ap₂ _,_ (+-assoc-0 a₁ c₁ e₁) (+-assoc-0 a₂ c₂ e₂))
  mk .+-comm (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) =
    ap₂ _,_ (l+comm a₀ c₀) (ap₂ _,_ (l+comm a₁ c₁) (l+comm a₂ c₂))
  mk .1R = R.1r , R.0r , R.0r
  mk ._*_ (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) =
      a₀ R.* c₀
    , a₀ R.* c₁ R.+ a₁ R.* c₀
    , a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀
  mk .*-idl (a₀ , a₁ , a₂) =
    ap₂ _,_ (*-idl-0 a₀) (ap₂ _,_ (*-idl-1 a₀ a₁) (*-idl-2 a₀ a₁ a₂))
  mk .*-idr (a₀ , a₁ , a₂) =
    ap₂ _,_ (*-idr-0 a₀) (ap₂ _,_ (*-idr-1 a₀ a₁) (*-idr-2 a₀ a₁ a₂))
  mk .*-assoc (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) (e₀ , e₁ , e₂) =
    ap₂ _,_ (*-assoc-0 a₀ c₀ e₀)
      (ap₂ _,_ (*-assoc-1 a₀ a₁ c₀ c₁ e₀ e₁) (*-assoc-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂))
  mk .*-distribl (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) (e₀ , e₁ , e₂) =
    ap₂ _,_ (*-distl-0 a₀ c₀ e₀)
      (ap₂ _,_ (*-distl-1 a₀ a₁ c₀ c₁ e₀ e₁) (*-distl-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂))
  mk .*-distribr (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) (e₀ , e₁ , e₂) =
    ap₂ _,_ (*-distr-0 a₀ c₀ e₀)
      (ap₂ _,_ (*-distr-1 a₀ a₁ c₀ c₁ e₀ e₁) (*-distr-2 a₀ a₁ a₂ c₀ c₁ c₂ e₀ e₁ e₂))
W₂ .snd .CRing-on.*-commutes {a₀ , a₁ , a₂} {c₀ , c₁ , c₂} =
  ap₂ _,_ (*-comm-0 a₀ c₀)
    (ap₂ _,_ (*-comm-1 a₀ a₁ c₀ c₁) (*-comm-2 a₀ a₁ a₂ c₀ c₁ c₂))
```

<!--
```agda
private module W = CRing-on (W₂ .snd)
```
-->

The truncated infinitesimal $\delta = 0 + 1\delta + 0\delta^2$ is
nilpotent of order three rather than two: its square is $\delta^2$
on the nose, and one more multiplication kills it.

<!--
```agda
private abstract
  δ²-0 : R.0r R.* R.0r ≡ R.0r
  δ²-0 = cring! R

  δ²-1 : R.0r R.* R.1r R.+ R.1r R.* R.0r ≡ R.0r
  δ²-1 = cring! R

  δ²-2 : R.0r R.* R.0r R.+ R.1r R.* R.1r R.+ R.0r R.* R.0r ≡ R.1r
  δ²-2 = cring! R

  δ³-0 : R.0r R.* R.0r ≡ R.0r
  δ³-0 = cring! R

  δ³-1 : R.0r R.* R.1r R.+ R.0r R.* R.0r ≡ R.0r
  δ³-1 = cring! R

  δ³-2
    : R.0r R.* R.0r R.+ R.0r R.* R.1r R.+ R.1r R.* R.0r ≡ R.0r
  δ³-2 = cring! R
```
-->

```agda
δ¹ : ⌞ W₂ ⌟
δ¹ = R.0r , R.1r , R.0r

δ²-value : δ¹ W.* δ¹ ≡ (R.0r , R.0r , R.1r)
δ²-value = ap₂ _,_ δ²-0 (ap₂ _,_ δ²-1 δ²-2)

δ³ : δ¹ W.* δ¹ W.* δ¹ ≡ W.0r
δ³ = ap (W._* δ¹) δ²-value ∙ ap₂ _,_ δ³-0 (ap₂ _,_ δ³-1 δ³-2)
```

$W_2$ is an $R$-algebra exactly as $R[\epsilon]$ was: constants
include with zero infinitesimal parts, and the augmentation
$W_2 \to R$ forgets them again.

<!--
```agda
private abstract
  ι+-1 : R.0r ≡ R.0r R.+ R.0r
  ι+-1 = cring! R

  ι*-1 : ∀ a b → R.0r ≡ a R.* R.0r R.+ R.0r R.* b
  ι*-1 a b = cring! R

  ι*-2 : ∀ a b → R.0r ≡ (a R.* R.0r R.+ R.0r R.* R.0r) R.+ R.0r R.* b
  ι*-2 a b = cring! R
```
-->

```agda
ι : CR.Hom R W₂
ι .∫Hom.fst a = a , R.0r , R.0r
ι .∫Hom.snd .pres-id = refl
ι .∫Hom.snd .pres-+ x y = ap₂ _,_ refl (ap₂ _,_ ι+-1 ι+-1)
ι .∫Hom.snd .pres-* x y = ap₂ _,_ refl (ap₂ _,_ (ι*-1 x y) (ι*-2 x y))

aug : CR.Hom W₂ R
aug .∫Hom.fst (a , _ , _) = a
aug .∫Hom.snd .pres-id = refl
aug .∫Hom.snd .pres-+ x y = refl
aug .∫Hom.snd .pres-* x y = refl
```

## The jet derivative {defines="jet-derivative"}

Formal differentiation with respect to $\delta$ sends $a + b\delta +
c\delta^2$ to $b + 2c\delta$: the coefficient of $\delta^k$ picks up
a factor of $k$ and drops one power of $\delta$, and everything
beyond $\delta^1$ is discarded since $W_2$ has no room for
$\delta^2$ once shifted. Because the construction is not assumed to
divide by $2$, this is the *undivided* derivative: it is $2c$, not
$c$, that appears — the same convention responsible for the
$\textstyle\frac12$ in the Taylor expansion $x_0 + vt + \textstyle
\frac12 at^2$ becoming visible algebra rather than a hidden
normalization.

```agda
D : ⌞ W₂ ⌟ → ⌞ W₂ ⌟
D (a , b , c) = b , c R.+ c , R.0r
```

$D$ is additive.

<!--
```agda
private abstract
  D+-1 : ∀ a₂ c₂ → a₂ R.+ c₂ R.+ (a₂ R.+ c₂) ≡ (a₂ R.+ a₂) R.+ (c₂ R.+ c₂)
  D+-1 a₂ c₂ = cring! R
```
-->

```agda
D-+ : ∀ u v → D (u W.+ v) ≡ D u W.+ D v
D-+ (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) =
  ap₂ _,_ refl (ap₂ _,_ (D+-1 a₂ c₂) (sym (l+idl R.0r)))
```

$D$ is, moreover, a **derivation** for the truncated product — but
only up to the order at which $D$ itself is still meaningful. $D$
discards the top coefficient entirely (there being no room left for
a $\delta^2$ once everything has shifted down by one power), so it
lands, in effect, in the *first-order* jets sitting inside $W_2$: its
own value always has zero top coefficient. The Leibniz rule
$D(uv) = (Du)v + u(Dv)$ can only be asked to hold where both sides
still see genuine information, namely in the constant and linear
coefficients; the quadratic coefficient of the right-hand side sees
contributions from $\delta^1\cdot\delta^2$ cross terms that $D(uv)$,
having already truncated $uv$ at $\delta^3$ before differentiating,
never had the chance to produce. So the theorem is exactly:
**the first two components of $D(uv)$ and $(Du)v + u(Dv)$ agree**,
for every $u, v \in W_2$.

<!--
```agda
private abstract
  leibniz-0
    : ∀ a₀ a₁ c₀ c₁
    → a₀ R.* c₁ R.+ a₁ R.* c₀ ≡ a₁ R.* c₀ R.+ a₀ R.* c₁
  leibniz-0 a₀ a₁ c₀ c₁ = cring! R

  leibniz-1
    : ∀ a₀ a₁ a₂ c₀ c₁ c₂
    → (a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀)
      R.+ (a₀ R.* c₂ R.+ a₁ R.* c₁ R.+ a₂ R.* c₀)
    ≡ (a₁ R.* c₁ R.+ (a₂ R.+ a₂) R.* c₀)
      R.+ (a₀ R.* (c₂ R.+ c₂) R.+ a₁ R.* c₁)
  leibniz-1 a₀ a₁ a₂ c₀ c₁ c₂ = cring! R
```
-->

```agda
D-leibniz₀ : ∀ u v → D (u W.* v) .fst ≡ ((D u W.* v) W.+ (u W.* D v)) .fst
D-leibniz₀ (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) = leibniz-0 a₀ a₁ c₀ c₁

D-leibniz₁
  : ∀ u v → D (u W.* v) .snd .fst ≡ ((D u W.* v) W.+ (u W.* D v)) .snd .fst
D-leibniz₁ (a₀ , a₁ , a₂) (c₀ , c₁ , c₂) = leibniz-1 a₀ a₁ a₂ c₀ c₁ c₂
```

Constants have zero derivative, and $\delta$ itself differentiates
to $1$ — the two boundary conditions pinning down $D$ as *the*
derivative on $W_2$.

```agda
D-ι : ∀ a → D (ι .∫Hom.fst a) ≡ W.0r
D-ι a = ap₂ _,_ refl (ap₂ _,_ (l+idl R.0r) refl)

D-δ : D δ¹ ≡ W.1r
D-δ = ap₂ _,_ refl (ap₂ _,_ (l+idl R.0r) refl)
```
