<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring using (is-ring-hom)

open import Cat.Displayed.Total

import Algebra.Ring.Kahler
import Cat.Reasoning

open is-ring-hom
```
-->

```agda
module Algebra.Ring.Kahler.Exterior {ℓ} (R : CRing ℓ) where
```

<!--
```agda
private
  module CR = Cat.Reasoning (CRings ℓ)
  module R = CRing-on (R .snd)

open Algebra.Ring.Kahler R
```
-->

# The second exterior power of Kähler differentials {defines="kahler-2-forms exterior-derivative"}

The module $\Omega^1_{A/R}$ of [[Kähler differentials|kahler-differentials]]
is the home of $1$-forms; a **Kähler $2$-form** $\Omega^2_{A/R}$ is
built the same way, from wedges $\mathrm{d}a \wedge \mathrm{d}b$ of
generators, subject to bilinearity, the Leibniz rule in each slot,
vanishing on the constants from $R$, and — the feature that
distinguishes the exterior power from a mere tensor square —
**antisymmetry**: $\mathrm{d}a \wedge \mathrm{d}b = -\mathrm{d}b
\wedge \mathrm{d}a$, forcing $\mathrm{d}a \wedge \mathrm{d}a = 0$.
Over a general ring neither of these follows from the other — $x
\equiv -x$ does not imply $x \equiv 0$ — so both are taken as
generating relations.

```agda
module _ (A : CRing ℓ) (φ : CR.Hom R A) where
  private module A = CRing-on (A .snd)

  data Ω² : Type ℓ where
    _d∧d_ : ⌞ A ⌟ → ⌞ A ⌟ → Ω²
    _·²_  : ⌞ A ⌟ → Ω² → Ω²
    _+²_  : Ω² → Ω² → Ω²
    0²    : Ω²
    -²_   : Ω² → Ω²

    +²-idl    : ∀ x → 0² +² x ≡ x
    +²-invr   : ∀ x → x +² (-² x) ≡ 0²
    +²-assoc  : ∀ x y z → x +² (y +² z) ≡ (x +² y) +² z
    +²-comm   : ∀ x y → x +² y ≡ y +² x
    ·²-distl  : ∀ a x y → a ·² (x +² y) ≡ (a ·² x) +² (a ·² y)
    ·²-distr  : ∀ a b x → (a A.+ b) ·² x ≡ (a ·² x) +² (b ·² x)
    ·²-assoc  : ∀ a b x → a ·² (b ·² x) ≡ (a A.* b) ·² x
    ·²-idl    : ∀ x → A.1r ·² x ≡ x

    d∧d-+l      : ∀ a b c → (a A.+ b) d∧d c ≡ (a d∧d c) +² (b d∧d c)
    d∧d-+r      : ∀ a b c → a d∧d (b A.+ c) ≡ (a d∧d b) +² (a d∧d c)
    d∧d-leibl   : ∀ a b c → (a A.* b) d∧d c ≡ (a ·² (b d∧d c)) +² (b ·² (a d∧d c))
    d∧d-leibr   : ∀ a b c → a d∧d (b A.* c) ≡ (b ·² (a d∧d c)) +² (c ·² (a d∧d b))
    d∧d-constl  : ∀ r b → φ .∫Hom.fst r d∧d b ≡ 0²
    d∧d-constr  : ∀ a r → a d∧d (φ .∫Hom.fst r) ≡ 0²
    d∧d-antisym : ∀ a b → a d∧d b ≡ -² (b d∧d a)
    d∧d-sq      : ∀ a → a d∧d a ≡ 0²
    squash²     : is-set Ω²
```

<details>
<summary>The eliminator into families of propositions is derived by
reflection, as usual.</summary>

```agda
  Ω²-elim-prop
    : ∀ {ℓ'} (B : Ω² → Type ℓ')
    → (∀ x → is-prop (B x))
    → (∀ a b → B (a d∧d b))
    → (∀ a x → B x → B (a ·² x))
    → (∀ x → B x → ∀ y → B y → B (x +² y))
    → B 0²
    → (∀ x → B x → B (-² x))
    → ∀ x → B x
  unquoteDef Ω²-elim-prop = make-elim-with (default-elim-visible into 1)
    Ω²-elim-prop (quote Ω²)
```

</details>

## Derived module laws

<!--
```agda
module _ {A : CRing ℓ} {φ : CR.Hom R A} where
  private module A = CRing-on (A .snd)

  +²-idr : ∀ (x : Ω² A φ) → x +² 0² ≡ x
  +²-idr x = +²-comm x 0² ∙ +²-idl x

  +²-invl : ∀ (x : Ω² A φ) → (-² x) +² x ≡ 0²
  +²-invl x = +²-comm (-² x) x ∙ +²-invr x

  ·²-absorb : ∀ (a : ⌞ A ⌟) → (a ·² 0²) ≡ 0² {A = A} {φ}
  ·²-absorb a =
    a ·² 0²                                       ≡˘⟨ +²-idr (a ·² 0²) ⟩
    (a ·² 0²) +² 0²                               ≡˘⟨ ap ((a ·² 0²) +²_) (+²-invr (a ·² 0²)) ⟩
    (a ·² 0²) +² ((a ·² 0²) +² (-² (a ·² 0²)))   ≡⟨ +²-assoc _ _ _ ⟩
    ((a ·² 0²) +² (a ·² 0²)) +² (-² (a ·² 0²))   ≡˘⟨ ap (_+² (-² (a ·² 0²))) (·²-distl a 0² 0²) ⟩
    (a ·² (0² +² 0²)) +² (-² (a ·² 0²))          ≡⟨ ap (λ e → (a ·² e) +² (-² (a ·² 0²))) (+²-idl 0²) ⟩
    (a ·² 0²) +² (-² (a ·² 0²))                  ≡⟨ +²-invr (a ·² 0²) ⟩
    0²                                            ∎
```
-->

The wedge of a function differential $\mathrm{d}a$ against an
arbitrary $1$-form $\omega$ is defined by recursion on $\omega$: on
generators it is the wedge just introduced, and it distributes over
the module structure of $\Omega^1_{A/R}$.

```agda
module _ {A : CRing ℓ} {φ : CR.Hom R A} where
  private module A = CRing-on (A .snd)

  wedge : ⌞ A ⌟ → Ω¹ A φ → Ω² A φ
  wedge a (dₖ b) = a d∧d b
  wedge a (b ·ω ω) = b ·² wedge a ω
  wedge a (ω +ω ω') = wedge a ω +² wedge a ω'
  wedge a 0ω = 0²
  wedge a (-ω ω) = -² wedge a ω

  wedge a (+ω-idl x i) = +²-idl (wedge a x) i
  wedge a (+ω-invr x i) = +²-invr (wedge a x) i
  wedge a (+ω-assoc x y z i) =
    +²-assoc (wedge a x) (wedge a y) (wedge a z) i
  wedge a (+ω-comm x y i) = +²-comm (wedge a x) (wedge a y) i
  wedge a (·ω-distl b x y i) =
    ·²-distl b (wedge a x) (wedge a y) i
  wedge a (·ω-distr b c x i) =
    ·²-distr b c (wedge a x) i
  wedge a (·ω-assoc b c x i) =
    ·²-assoc b c (wedge a x) i
  wedge a (·ω-idl x i) = ·²-idl (wedge a x) i
  wedge a (d-+ b c i) = d∧d-+r a b c i
  wedge a (d-leibniz b c i) = d∧d-leibr a b c i
  wedge a (d-const r i) = d∧d-constr a r i
  wedge a (squashω x y p q i j) = squash²
    (wedge a x) (wedge a y) (λ i → wedge a (p i)) (λ i → wedge a (q i)) i j
```

Additivity of `wedge`{.Agda} in the $1$-form argument is
definitional — it is exactly the `+ω`{.Agda} clause of the recursion.

```agda
  wedge-+ : ∀ a ω ω' → wedge a (ω +ω ω') ≡ wedge a ω +² wedge a ω'
  wedge-+ a ω ω' = refl
```

## Algebraic lemmas for the exterior derivative

A short packet of group- and module-theoretic facts about $\Omega^2$
feeds directly into the module-law clauses of the exterior derivative
below, plus additivity, the Leibniz rule, and unit-vanishing for
`wedge`{.Agda} in its scalar slot — all three proved by induction on
the $1$-form argument, reducing to the corresponding law of
$\mathrm{d}{\wedge}\mathrm{d}$ at the generators.

<!--
```agda
module _ {A : CRing ℓ} {φ : CR.Hom R A} where
  private module A = CRing-on (A .snd)

  +²-interchange
    : ∀ (p q r s : Ω² A φ)
    → (p +² q) +² (r +² s) ≡ (p +² r) +² (q +² s)
  +²-interchange p q r s =
    (p +² q) +² (r +² s)   ≡˘⟨ +²-assoc p q (r +² s) ⟩
    p +² (q +² (r +² s))   ≡⟨ ap (p +²_) (+²-assoc q r s) ⟩
    p +² ((q +² r) +² s)   ≡⟨ ap (λ e → p +² (e +² s)) (+²-comm q r) ⟩
    p +² ((r +² q) +² s)   ≡˘⟨ ap (p +²_) (+²-assoc r q s) ⟩
    p +² (r +² (q +² s))   ≡⟨ +²-assoc p r (q +² s) ⟩
    (p +² r) +² (q +² s)   ∎

  +²-inv-unique : ∀ (x y : Ω² A φ) → x +² y ≡ 0² → y ≡ -² x
  +²-inv-unique x y p =
    y                     ≡˘⟨ +²-idl y ⟩
    0² +² y               ≡˘⟨ ap (_+² y) (+²-invl x) ⟩
    ((-² x) +² x) +² y    ≡⟨ sym (+²-assoc (-² x) x y) ⟩
    (-² x) +² (x +² y)    ≡⟨ ap ((-² x) +²_) p ⟩
    (-² x) +² 0²          ≡⟨ +²-idr (-² x) ⟩
    -² x                  ∎

  neg-+² : ∀ (p q : Ω² A φ) → -² (p +² q) ≡ (-² p) +² (-² q)
  neg-+² p q = sym (+²-inv-unique (p +² q) ((-² p) +² (-² q))
    ( +²-interchange p q (-² p) (-² q)
    ∙ ap₂ _+²_ (+²-invr p) (+²-invr q)
    ∙ +²-idl 0² ))

  ·²-negr : ∀ (a : ⌞ A ⌟) (x : Ω² A φ) → a ·² (-² x) ≡ -² (a ·² x)
  ·²-negr a x = +²-inv-unique (a ·² x) (a ·² (-² x))
    (sym (·²-distl a x (-² x)) ∙ ap (a ·²_) (+²-invr x) ∙ ·²-absorb a)

  wedge-+l : ∀ a b ω → wedge (a A.+ b) ω ≡ wedge a ω +² wedge b ω
  wedge-+l a b = Ω¹-elim-prop A φ
    (λ ω → wedge (a A.+ b) ω ≡ wedge a ω +² wedge b ω)
    (λ _ → squash² _ _)
    (λ c → d∧d-+l a b c)
    (λ c ω ih → ap (c ·²_) ih ∙ ·²-distl c (wedge a ω) (wedge b ω))
    (λ ω ihω ω' ihω' →
        ap₂ _+²_ ihω ihω'
      ∙ +²-interchange (wedge a ω) (wedge b ω) (wedge a ω') (wedge b ω'))
    (sym (+²-idl 0²))
    (λ ω ih →
        ap -²_ ih
      ∙ neg-+² (wedge a ω) (wedge b ω))

  wedge-leib : ∀ a b ω → wedge (a A.* b) ω ≡ (a ·² wedge b ω) +² (b ·² wedge a ω)
  wedge-leib a b = Ω¹-elim-prop A φ
    (λ ω → wedge (a A.* b) ω ≡ (a ·² wedge b ω) +² (b ·² wedge a ω))
    (λ _ → squash² _ _)
    (λ c → d∧d-leibl a b c)
    (λ c ω ih →
        ap (c ·²_) ih
      ∙ ·²-distl c (a ·² wedge b ω) (b ·² wedge a ω)
      ∙ ap₂ _+²_ (·²-assoc c a (wedge b ω) ∙ ap (_·² wedge b ω) (A.*-commutes {c} {a}) ∙ sym (·²-assoc a c (wedge b ω)))
                 (·²-assoc c b (wedge a ω) ∙ ap (_·² wedge a ω) (A.*-commutes {c} {b}) ∙ sym (·²-assoc b c (wedge a ω))))
    (λ ω ihω ω' ihω' →
        ap₂ _+²_ ihω ihω'
      ∙ +²-interchange (a ·² wedge b ω) (b ·² wedge a ω) (a ·² wedge b ω') (b ·² wedge a ω')
      ∙ ap₂ _+²_ (sym (·²-distl a (wedge b ω) (wedge b ω'))) (sym (·²-distl b (wedge a ω) (wedge a ω'))))
    ( sym (+²-idl 0²)
    ∙ ap₂ _+²_ (sym (·²-absorb a)) (sym (·²-absorb b)))
    (λ ω ih →
        ap -²_ ih
      ∙ neg-+² (a ·² wedge b ω) (b ·² wedge a ω)
      ∙ ap₂ _+²_ (sym (·²-negr a (wedge b ω))) (sym (·²-negr b (wedge a ω))))

  wedge-one : ∀ ω → wedge A.1r ω ≡ 0² {A = A} {φ}
  wedge-one = Ω¹-elim-prop A φ
    (λ ω → wedge A.1r ω ≡ 0²)
    (λ _ → squash² _ _)
    one-base
    (λ c ω ih → ap (c ·²_) ih ∙ ·²-absorb c)
    (λ ω ihω ω' ihω' → ap₂ _+²_ ihω ihω' ∙ +²-idl 0²)
    refl
    (λ ω ih → ap -²_ ih ∙ neg-+²-zero)
    where
    one-image : φ .∫Hom.fst R.1r ≡ A.1r
    one-image = is-ring-hom.pres-id (φ .∫Hom.snd)

    one-base : ∀ b → A.1r d∧d b ≡ 0²
    one-base b =
      A.1r d∧d b               ≡˘⟨ (λ i → one-image i d∧d b) ⟩
      φ .∫Hom.fst R.1r d∧d b   ≡⟨ d∧d-constl R.1r b ⟩
      0²                       ∎

    neg-+²-zero : -² 0² {A = A} {φ} ≡ 0²
    neg-+²-zero = sym (+²-inv-unique 0² 0² (+²-idl 0²))
```
-->

