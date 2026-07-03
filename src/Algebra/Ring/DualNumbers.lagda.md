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
module Algebra.Ring.DualNumbers {ℓ} (R : CRing ℓ) where
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

# The ring of dual numbers {defines="dual-numbers"}

The **dual numbers** over a commutative [[ring]] $R$ are the
commutative $R$-algebra $R[\epsilon] := R[x]/(x^2)$: the "smallest"
extension of $R$ by a formally infinitesimal quantity, one whose
square — and every higher power — simply *is* zero. Physicists'
computations that keep terms "to first order in $\epsilon$" are exact
computations in $R[\epsilon]$, and probing spaces by the formal dual
of $R[\epsilon]$ is what makes the naive infinitesimal reasoning of
variational calculus rigorous, in the tradition of synthetic
differential geometry.

Because the quotient is by such a tame relation, no quotient is
needed: $R[\epsilon]$ has carrier $R \times R$, recording coefficients
$a + b\epsilon$, with multiplication truncating the $\epsilon^2$ term.
All the ring laws are decided by the [[commutative ring
solver|ring-solver]].

<!--
```agda
private abstract
  l+idl : ∀ a → R.0r R.+ a ≡ a
  l+idl a = cring! R

  l+invr : ∀ a → a R.+ (R.- a) ≡ R.0r
  l+invr a = cring! R

  l+assoc : ∀ a c e → a R.+ (c R.+ e) ≡ (a R.+ c) R.+ e
  l+assoc a c e = cring! R

  l+comm : ∀ a c → a R.+ c ≡ c R.+ a
  l+comm a c = cring! R

  l*idl : ∀ a → R.1r R.* a ≡ a
  l*idl a = cring! R

  l*idl' : ∀ a b → R.1r R.* b R.+ R.0r R.* a ≡ b
  l*idl' a b = cring! R

  l*idr : ∀ a → a R.* R.1r ≡ a
  l*idr a = cring! R

  l*idr' : ∀ a b → a R.* R.0r R.+ b R.* R.1r ≡ b
  l*idr' a b = cring! R

  l*assoc : ∀ a c e → a R.* (c R.* e) ≡ (a R.* c) R.* e
  l*assoc a c e = cring! R

  l*assoc'
    : ∀ a b c d e f
    → a R.* (c R.* f R.+ d R.* e) R.+ b R.* (c R.* e)
    ≡ (a R.* c) R.* f R.+ (a R.* d R.+ b R.* c) R.* e
  l*assoc' a b c d e f = cring! R

  l*distl : ∀ a c e → a R.* (c R.+ e) ≡ a R.* c R.+ a R.* e
  l*distl a c e = cring! R

  l*distl'
    : ∀ a b c d e f
    → a R.* (d R.+ f) R.+ b R.* (c R.+ e)
    ≡ (a R.* d R.+ b R.* c) R.+ (a R.* f R.+ b R.* e)
  l*distl' a b c d e f = cring! R

  l*distr : ∀ a c e → (c R.+ e) R.* a ≡ c R.* a R.+ e R.* a
  l*distr a c e = cring! R

  l*distr'
    : ∀ a b c d e f
    → (c R.+ e) R.* b R.+ (d R.+ f) R.* a
    ≡ (c R.* b R.+ d R.* a) R.+ (e R.* b R.+ f R.* a)
  l*distr' a b c d e f = cring! R

  l*comm : ∀ a c → a R.* c ≡ c R.* a
  l*comm a c = cring! R

  l*comm' : ∀ a b c d → a R.* d R.+ b R.* c ≡ c R.* b R.+ d R.* a
  l*comm' a b c d = cring! R

  lι+ : R.0r ≡ R.0r R.+ R.0r
  lι+ = cring! R

  lι* : ∀ a b → R.0r ≡ a R.* R.0r R.+ R.0r R.* b
  lι* a b = cring! R

  lε₁ : R.0r R.* R.0r ≡ R.0r
  lε₁ = cring! R

  lε₂ : R.0r R.* R.1r R.+ R.1r R.* R.0r ≡ R.0r
  lε₂ = cring! R
```
-->

```agda
R[ε] : CRing ℓ
R[ε] .fst = el! (⌞ R ⌟ × ⌞ R ⌟)
R[ε] .snd .CRing-on.has-ring-on = to-ring-on mk where
  mk : make-ring (⌞ R ⌟ × ⌞ R ⌟)
  mk .ring-is-set = hlevel 2
  mk .0R = R.0r , R.0r
  mk ._+_ x y = x .fst R.+ y .fst , x .snd R.+ y .snd
  mk .-_ x = R.- x .fst , R.- x .snd
  mk .+-idl (a , b) = ap₂ _,_ (l+idl a) (l+idl b)
  mk .+-invr (a , b) = ap₂ _,_ (l+invr a) (l+invr b)
  mk .+-assoc (a , b) (c , d) (e , f) = ap₂ _,_ (l+assoc a c e) (l+assoc b d f)
  mk .+-comm (a , b) (c , d) = ap₂ _,_ (l+comm a c) (l+comm b d)
  mk .1R = R.1r , R.0r
  mk ._*_ x y =
    x .fst R.* y .fst , x .fst R.* y .snd R.+ x .snd R.* y .fst
  mk .*-idl (a , b) = ap₂ _,_ (l*idl a) (l*idl' a b)
  mk .*-idr (a , b) = ap₂ _,_ (l*idr a) (l*idr' a b)
  mk .*-assoc (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*assoc a c e) (l*assoc' a b c d e f)
  mk .*-distribl (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*distl a c e) (l*distl' a b c d e f)
  mk .*-distribr (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*distr a c e) (l*distr' a b c d e f)
R[ε] .snd .CRing-on.*-commutes {a , b} {c , d} =
  ap₂ _,_ (l*comm a c) (l*comm' a b c d)
```

<!--
```agda
private module Rε = CRing-on (R[ε] .snd)
```
-->

The infinitesimal itself is the element $\epsilon = 0 + 1\epsilon$,
and it squares to zero — the equation that in physics is an
approximation, and here is a definition.

```agda
εᴿ : ⌞ R[ε] ⌟
εᴿ = R.0r , R.1r

ε² : εᴿ Rε.* εᴿ ≡ Rε.0r
ε² = ap₂ _,_ lε₁ lε₂
```

$R[\epsilon]$ is an $R$-algebra: $R$ includes as the constants, and
there is an **augmentation** $R[\epsilon] \to R$ which forgets the
infinitesimal part — "evaluation at $\epsilon = 0$". The composite is
the identity: the constants have no infinitesimal part to forget.

```agda
ι-dual : CR.Hom R R[ε]
ι-dual .∫Hom.fst a = a , R.0r
ι-dual .∫Hom.snd .pres-id = refl
ι-dual .∫Hom.snd .pres-+ x y = ap₂ _,_ refl lι+
ι-dual .∫Hom.snd .pres-* x y = ap₂ _,_ refl (lι* x y)

aug-dual : CR.Hom R[ε] R
aug-dual .∫Hom.fst = fst
aug-dual .∫Hom.snd .pres-id = refl
aug-dual .∫Hom.snd .pres-+ x y = refl
aug-dual .∫Hom.snd .pres-* x y = refl

aug-ι : aug-dual CR.∘ ι-dual ≡ CR.id
aug-ι = ∫Hom-path _ refl prop!
```

## The universal property {defines="universal-property-of-dual-numbers"}

$R[\epsilon]$ is the universal $R$-algebra containing a square-zero
element: an algebra map out of $R[\epsilon]$ is exactly the choice of
a square-zero element of the codomain, the image of $\epsilon$. This
is what makes the formal dual of $R[\epsilon]$ the *walking tangent
vector*: maps from it into a space are single tangent vectors, and the
universal property below is the engine of the Kock–Lawvere theorem.

```agda
module _ {C : CRing ℓ} (ψ : CR.Hom R C)
         (d : ⌞ C ⌟) (dd : C .snd .CRing-on._*_ d d ≡ C .snd .CRing-on.0r)
  where

  private
    module C = CRing-on (C .snd)
    module ψ = is-ring-hom (ψ .∫Hom.snd)
    module Cr = Algebra.Ring.Reasoning
      (C .fst , C .snd .CRing-on.has-ring-on)

    ψf : ⌞ R ⌟ → ⌞ C ⌟
    ψf = ψ .∫Hom.fst
```

The underlying function sends $a + b\epsilon$ to $\psi(a) + d\psi(b)$;
that this is a ring homomorphism is a computation in $C$ whose only
interesting step is the disappearance of the $d^2$ term.

<!--
```agda
    +-inner
      : ∀ w x y z
      → (w C.+ x) C.+ (y C.+ z) ≡ (w C.+ y) C.+ (x C.+ z)
    +-inner w x y z =
      (w C.+ x) C.+ (y C.+ z)   ≡˘⟨ C.+-associative ⟩
      w C.+ (x C.+ (y C.+ z))   ≡⟨ ap (w C.+_) C.+-associative ⟩
      w C.+ ((x C.+ y) C.+ z)   ≡⟨ ap (w C.+_) (ap (C._+ z) C.+-commutes) ⟩
      w C.+ ((y C.+ x) C.+ z)   ≡˘⟨ ap (w C.+_) C.+-associative ⟩
      w C.+ (y C.+ (x C.+ z))   ≡⟨ C.+-associative ⟩
      (w C.+ y) C.+ (x C.+ z)   ∎

    pull-d : ∀ u v → u C.* (d C.* v) ≡ d C.* (u C.* v)
    pull-d u v =
      u C.* (d C.* v)   ≡⟨ C.*-associative ⟩
      (u C.* d) C.* v   ≡⟨ ap (C._* v) C.*-commutes ⟩
      (d C.* u) C.* v   ≡˘⟨ C.*-associative ⟩
      d C.* (u C.* v)   ∎

    kill-dd : ∀ u v → (d C.* u) C.* (d C.* v) ≡ C.0r
    kill-dd u v =
      (d C.* u) C.* (d C.* v)   ≡˘⟨ C.*-associative ⟩
      d C.* (u C.* (d C.* v))   ≡⟨ ap (d C.*_) (pull-d u v) ⟩
      d C.* (d C.* (u C.* v))   ≡⟨ C.*-associative ⟩
      (d C.* d) C.* (u C.* v)   ≡⟨ ap (C._* (u C.* v)) dd ⟩
      C.0r C.* (u C.* v)        ≡⟨ Cr.*-zerol ⟩
      C.0r                      ∎
```
-->

```agda
  ε-extendᶠ : ⌞ R[ε] ⌟ → ⌞ C ⌟
  ε-extendᶠ (a , b) = ψ .∫Hom.fst a C.+ d C.* ψ .∫Hom.fst b

  ε-extend : CR.Hom R[ε] C
  ε-extend .∫Hom.fst = ε-extendᶠ
```

<details>
<summary>The homomorphism proofs are unenlightening equational
reasoning.</summary>

```agda
  ε-extend .∫Hom.snd .pres-id =
      ap₂ C._+_ ψ.pres-id (ap (d C.*_) ψ.pres-0 ∙ Cr.*-zeror)
    ∙ C.+-idr
  ε-extend .∫Hom.snd .pres-+ (a , b) (c , e) =
      ap₂ C._+_ (ψ.pres-+ a c)
        (ap (d C.*_) (ψ.pres-+ b e) ∙ C.*-distribl)
    ∙ +-inner _ _ _ _
  ε-extend .∫Hom.snd .pres-* (a , b) (c , e) = sym $
    (ψf a C.+ d C.* ψf b) C.* (ψf c C.+ d C.* ψf e)
      ≡⟨ C.*-distribl ⟩
    (ψf a C.+ d C.* ψf b) C.* ψf c C.+
    (ψf a C.+ d C.* ψf b) C.* (d C.* ψf e)
      ≡⟨ ap₂ C._+_ C.*-distribr C.*-distribr ⟩
    (ψf a C.* ψf c C.+ (d C.* ψf b) C.* ψf c) C.+
    (ψf a C.* (d C.* ψf e) C.+ (d C.* ψf b) C.* (d C.* ψf e))
      ≡⟨ ap₂ C._+_
           (ap (ψf a C.* ψf c C.+_) (sym C.*-associative))
           (ap₂ C._+_ (pull-d (ψf a) (ψf e)) (kill-dd (ψf b) (ψf e))) ⟩
    (ψf a C.* ψf c C.+ d C.* (ψf b C.* ψf c)) C.+
    (d C.* (ψf a C.* ψf e) C.+ C.0r)
      ≡⟨ ap₂ C._+_ refl C.+-idr ⟩
    (ψf a C.* ψf c C.+ d C.* (ψf b C.* ψf c)) C.+ d C.* (ψf a C.* ψf e)
      ≡˘⟨ C.+-associative ⟩
    ψf a C.* ψf c C.+ (d C.* (ψf b C.* ψf c) C.+ d C.* (ψf a C.* ψf e))
      ≡⟨ ap (ψf a C.* ψf c C.+_) C.+-commutes ⟩
    ψf a C.* ψf c C.+ (d C.* (ψf a C.* ψf e) C.+ d C.* (ψf b C.* ψf c))
      ≡˘⟨ ap (ψf a C.* ψf c C.+_) C.*-distribl ⟩
    ψf a C.* ψf c C.+ d C.* (ψf a C.* ψf e C.+ ψf b C.* ψf c)
      ≡˘⟨ ap₂ C._+_ (ψ.pres-* a c)
            (ap (d C.*_)
              ( ψ.pres-+ (a R.* e) (b R.* c)
              ∙ ap₂ C._+_ (ψ.pres-* a e) (ψ.pres-* b c))) ⟩
    ψf (a R.* c) C.+ d C.* ψf (a R.* e R.+ b R.* c)
      ∎
```

</details>

The two computation rules — restricting to the constants gives back
$\psi$, and $\epsilon$ goes to $d$ — and the uniqueness rule, which
together say that "algebra maps $R[\epsilon] \to C$ are square-zero
elements of $C$":

```agda
  ε-extend-ι : ε-extend CR.∘ ι-dual ≡ ψ
  ε-extend-ι = ∫Hom-path _
    (funext λ a →
      ap (ψ .∫Hom.fst a C.+_) (ap (d C.*_) ψ.pres-0 ∙ Cr.*-zeror)
      ∙ C.+-idr)
    prop!

  ε-extend-ε : ε-extendᶠ εᴿ ≡ d
  ε-extend-ε =
      ap₂ C._+_ ψ.pres-0 (ap (d C.*_) ψ.pres-id ∙ C.*-idr)
    ∙ C.+-idl

  ε-extend-unique
    : (h : CR.Hom R[ε] C)
    → (∀ a → h .∫Hom.fst (a , R.0r) ≡ ψ .∫Hom.fst a)
    → h .∫Hom.fst εᴿ ≡ d
    → h ≡ ε-extend
  ε-extend-unique h hι hε = ∫Hom-path _ (funext go) prop! where
    module h = is-ring-hom (h .∫Hom.snd)

    decompose : ∀ a b → Path ⌞ R[ε] ⌟ (a , b) ((a , R.0r) Rε.+ (εᴿ Rε.* (b , R.0r)))
    decompose a b = ap₂ _,_ p q where
      p : a ≡ a R.+ R.0r R.* b
      p = cring! R
      q : b ≡ R.0r R.+ (R.0r R.* R.0r R.+ R.1r R.* b)
      q = cring! R

    go : ∀ x → h .∫Hom.fst x ≡ ε-extendᶠ x
    go (a , b) =
      h .∫Hom.fst (a , b)
        ≡⟨ ap (h .∫Hom.fst) (decompose a b) ⟩
      h .∫Hom.fst ((a , R.0r) Rε.+ (εᴿ Rε.* (b , R.0r)))
        ≡⟨ h.pres-+ (a , R.0r) (εᴿ Rε.* (b , R.0r)) ⟩
      h .∫Hom.fst (a , R.0r) C.+ h .∫Hom.fst (εᴿ Rε.* (b , R.0r))
        ≡⟨ ap₂ C._+_ (hι a)
             (h.pres-* εᴿ (b , R.0r) ∙ ap₂ C._*_ hε (hι b)) ⟩
      ψ .∫Hom.fst a C.+ d C.* ψ .∫Hom.fst b
        ∎
```
