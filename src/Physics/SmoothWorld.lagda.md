<!--
```agda
open import 1Lab.Prelude hiding (_+_ ; _*_ ; _-_ ; ∣_∣)

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Sum.Base
open import Data.Dec.Base

import Algebra.Ring.Reasoning
```
-->

```agda
module Physics.SmoothWorld where
```

# Smooth infinitesimal analysis, axiomatically {defines="smooth-infinitesimal-analysis smooth-world"}

The [[dual numbers|dual-numbers]], the [[Kock–Lawvere
theorem|kock-lawvere]], and the synthetic derivatives of the
[[oscillator|harmonic-oscillator]] and the
[[heliostat|parabolic-focusing]] all descend from a single axiomatic
picture: John L. Bell's *smooth world*, the setting of **smooth
infinitesimal analysis** (SIA). This module records the core of Bell's
*A Primer of Infinitesimal Analysis*, Chapters 1–2 — the nilsquare
infinitesimals $\Delta$, the **Microaffineness** axiom, the
microcancellation and non-degeneracy theorems, the synthetic
derivative with its differentiation rules, Fermat's stationary-point
rule, the constructive **failure of the law of excluded middle** on
$\Delta$, and (given the Constancy principle) the **indecomposability**
of the smooth line.

The discipline of this file is *honesty about hypotheses*. The SIA
axioms are not theorems of type theory — they are false in the
classical world. So they appear here **not** as `postulate`s but as
explicit **module parameters and record fields**: `Microaffineness`
is a `Type` that a caller must inhabit, and `Constancy`,
`has-inverses` are records of extra hypotheses. Everything *derived*
from them is genuinely proven, with zero postulates. The single
vindication that the axioms are *consistent* — that a model exists —
is the `Kock-Lawvere`{.Agda} theorem, which holds on the nose in the
gros topos of [[formal smooth sets|formal-smooth-sets]]; we link to it
in the closing honesty section.

Throughout we work over an abstract [[commutative
ring|commutative-ring]] $R$ — Bell's smooth line — and discharge every
ring identity with the [[ring solver|ring-solver]] `cring!`, which
fires precisely because $R$ is an *abstract* parameter.

## The nilsquare infinitesimals

<!--
```agda
module _ {ℓ} (R : CRing ℓ) where
  private
    module R = CRing-on (R .snd)
    module Rr = Algebra.Ring.Reasoning (R .fst , R .snd .CRing-on.has-ring-on)
```
-->

The **infinitesimals** $\Delta \subseteq R$ are the elements whose
square vanishes — the *nilsquare* part of the line. This is exactly
the square-zero predicate the dual numbers are built from (their
`ε²`{.Agda} witness), now taken as a subtype of an abstract ring.

```agda
  Δ : Type ℓ
  Δ = Σ[ d ∈ ⌞ R ⌟ ] (d R.* d ≡ R.0r)
```

The underlying carrier of a ring is a set, so "$d$ is nilsquare" is a
proposition and $\Delta$ is a set whose paths are determined by the
first projection. We name that projection and the zero infinitesimal
$0 \in \Delta$ (since $0 \cdot 0 = 0$ by `*-zerol`{.Agda}).

```agda
  ∣_∣Δ : Δ → ⌞ R ⌟
  ∣ ε ∣Δ = ε .fst

  Δ0 : Δ
  Δ0 = R.0r , Rr.*-zerol
```

## Microaffineness {defines="microaffineness"}

Bell's central axiom, **Microaffineness** (the Kock–Lawvere axiom in
elementwise form): *for every function $g : \Delta \to R$ there is a
**unique** $b : R$ with $g(\varepsilon) = g(0) + b\varepsilon$ for all
$\varepsilon \in \Delta$.* Every function on the infinitesimals is,
uniquely, affine. Existence gives the slope; uniqueness is the engine
of the entire calculus.

We phrase "unique $b$ such that …" as the contractibility of the type
of *pairs* $(b, \text{proof})$ — the standard 1Lab idiom in which
`.centre`{.Agda} packages existence and `.paths`{.Agda} packages
uniqueness.

```agda
  is-affine-slope : (g : Δ → ⌞ R ⌟) → ⌞ R ⌟ → Type ℓ
  is-affine-slope g b = (ε : Δ) → g ε ≡ g Δ0 R.+ (b R.* ∣ ε ∣Δ)

  Microaffineness : Type ℓ
  Microaffineness =
    (g : Δ → ⌞ R ⌟) → is-contr (Σ[ b ∈ ⌞ R ⌟ ] is-affine-slope g b)
```

`Microaffineness` is a `Type`, a function of $R$. A model of SIA is a
ring together with a term of this type; downstream we take such a term
as a **hypothesis**, never a postulate. Every construction below is
parametrized by it.

<!--
```agda
module Bell {ℓ} (R : CRing ℓ) (micro : Microaffineness R) where
  private
    module R = CRing-on (R .snd)
    module Rr = Algebra.Ring.Reasoning (R .fst , R .snd .CRing-on.has-ring-on)

  -- local abbreviations, definitionally equal to the outer-module
  -- definitions applied to R (so `micro` and `affine` agree on the nose)
  𝔻 : Type ℓ
  𝔻 = Δ R

  ∣_∣ : 𝔻 → ⌞ R ⌟
  ∣ ε ∣ = ∣_∣Δ R ε

  d0 : 𝔻
  d0 = Δ0 R

  affine : (g : 𝔻 → ⌞ R ⌟) → ⌞ R ⌟ → Type ℓ
  affine = is-affine-slope R
```
-->

## Microcancellation and non-degeneracy {defines="microcancellation"}

The uniqueness half of Microaffineness is Bell's Theorem 1.1(iv),
**microcancellation**: if $a\varepsilon = b\varepsilon$ for *every*
$\varepsilon \in \Delta$, then $a = b$. One cannot divide by an
infinitesimal, but one *can* cancel a universally quantified one.

The proof applies the axiom to $g(\varepsilon) = a\varepsilon$: both
$a$ and $b$ present themselves as slopes of the same $g$ — for $a$
because $a\varepsilon = a\cdot 0 + a\varepsilon$, for $b$ because the
hypothesis rewrites $a\varepsilon$ to $b\varepsilon = a\cdot 0 +
b\varepsilon$ — so the contractible type of slopes forces $a = b$.

```agda
  microcancel
    : (a b : ⌞ R ⌟)
    → ((ε : 𝔻) → a R.* ∣ ε ∣ ≡ b R.* ∣ ε ∣)
    → a ≡ b
  microcancel a b h = ap fst (sym pa ∙ pb)
    where
      g : 𝔻 → ⌞ R ⌟
      g ε = a R.* ∣ ε ∣

      slope-a : affine g a
      slope-a ε = cring! R  -- a·ε ≡ a·0 + a·ε

      slope-b : affine g b
      slope-b ε = h ε ∙ reintro  -- a·ε ≡ b·ε ≡ a·0 + b·ε
        where
          reintro : b R.* ∣ ε ∣ ≡ g d0 R.+ (b R.* ∣ ε ∣)
          reintro = cring! R

      pa : micro g .centre ≡ (a , slope-a)
      pa = micro g .paths (a , slope-a)

      pb : micro g .centre ≡ (b , slope-b)
      pb = micro g .paths (b , slope-b)
```

**Non-degeneracy** (Theorem 1.1(i)): $\Delta$ is not the trivial set
$\{0\}$, provided the ring is non-trivial. Precisely — if $0 \neq 1$
then it is *false* that every infinitesimal is zero. For were every
$\varepsilon \in \Delta$ equal to $0$, then $1\cdot\varepsilon =
0\cdot\varepsilon$ (both are $0$) for all $\varepsilon$, whence
microcancellation would give $1 = 0$.

```agda
  Δ-nondegenerate
    : ¬ (R.0r ≡ R.1r)
    → ¬ ((ε : 𝔻) → ∣ ε ∣ ≡ R.0r)
  Δ-nondegenerate 0≠1 all-zero = 0≠1 (sym (microcancel R.1r R.0r cancel))
    where
      cancel : (ε : 𝔻) → R.1r R.* ∣ ε ∣ ≡ R.0r R.* ∣ ε ∣
      cancel ε =
        R.1r R.* ∣ ε ∣ ≡⟨ ap (R.1r R.*_) (all-zero ε) ⟩
        R.1r R.* R.0r  ≡⟨ cring! R ⟩
        R.0r R.* ∣ ε ∣ ∎
```

So under $0 \neq 1$ the infinitesimals form a genuinely non-trivial
neighbourhood of $0$ — yet, as we will see in Theorem 1.1(iii), no
particular infinitesimal is provably $\neq 0$ either.

## The derivative {defines="synthetic-derivative fundamental-equation"}

For an arbitrary $f : R \to R$ and base point $x$, the map
$\varepsilon \mapsto f(x + \varepsilon)$ is a function $\Delta \to R$,
so Microaffineness hands us its unique slope. **That slope is the
derivative** $f'(x)$. This is Bell's definition — no limits, no
$\varepsilon$-$\delta$: differentiability is automatic, and the
derivative is *the* affine coefficient.

```agda
  slope-at : (⌞ R ⌟ → ⌞ R ⌟) → ⌞ R ⌟ → (𝔻 → ⌞ R ⌟)
  slope-at f x ε = f (x R.+ ∣ ε ∣)

  deriv : (⌞ R ⌟ → ⌞ R ⌟) → (⌞ R ⌟ → ⌞ R ⌟)
  deriv f x = micro (slope-at f x) .centre .fst
```

The existence half of the axiom *is* the **fundamental equation** of
the differential calculus, $f(x + \varepsilon) = f(x) +
\varepsilon\,f'(x)$ — Bell's Taylor expansion with an identically-zero
remainder. It comes from `.centre .snd`{.Agda} after simplifying
$x + 0 = x$ and commuting the product into Bell's order.

```agda
  fundamental
    : (f : ⌞ R ⌟ → ⌞ R ⌟) (x : ⌞ R ⌟) (ε : 𝔻)
    → f (x R.+ ∣ ε ∣) ≡ f x R.+ (∣ ε ∣ R.* deriv f x)
  fundamental f x ε =
    f (x R.+ ∣ ε ∣)
      ≡⟨ micro (slope-at f x) .centre .snd ε ⟩
    f (x R.+ R.0r) R.+ (deriv f x R.* ∣ ε ∣)
      ≡⟨ ap (λ z → f z R.+ (deriv f x R.* ∣ ε ∣)) R.+-idr ⟩
    f x R.+ (deriv f x R.* ∣ ε ∣)
      ≡⟨ ap (f x R.+_) R.*-commutes ⟩
    f x R.+ (∣ ε ∣ R.* deriv f x) ∎
```

The derivative is *uniquely* characterised by this equation: if some
$b$ satisfies $f(x + \varepsilon) = f(x) + \varepsilon b$ for all
$\varepsilon$, then $b = f'(x)$. This is where microcancellation earns
its keep — the two expansions of $f(x+\varepsilon)$ agree, so their
coefficients of $\varepsilon$ must too.

```agda
  deriv-unique
    : (f : ⌞ R ⌟ → ⌞ R ⌟) (x b : ⌞ R ⌟)
    → ((ε : 𝔻) → f (x R.+ ∣ ε ∣) ≡ f x R.+ (∣ ε ∣ R.* b))
    → b ≡ deriv f x
  deriv-unique f x b hb = microcancel b (deriv f x) coeff
    where
      -- both expansions equal f(x+ε), so their ε-coefficients agree;
      -- we cancel the shared summand f x by adding −(f x) and using cring!.
      coeff : (ε : 𝔻) → b R.* ∣ ε ∣ ≡ deriv f x R.* ∣ ε ∣
      coeff ε =
        b R.* ∣ ε ∣
          ≡⟨ reintro b (f x) ∣ ε ∣ ⟩
        (R.- f x) R.+ (f x R.+ (b R.* ∣ ε ∣))
          ≡⟨ ap ((R.- f x) R.+_) path ⟩
        (R.- f x) R.+ (f x R.+ (deriv f x R.* ∣ ε ∣))
          ≡⟨ sym (reintro (deriv f x) (f x) ∣ ε ∣) ⟩
        deriv f x R.* ∣ ε ∣ ∎
        where
          reintro : ∀ q fx e → q R.* e ≡ (R.- fx) R.+ (fx R.+ (q R.* e))
          reintro q fx e = cring! R

          path : f x R.+ (b R.* ∣ ε ∣) ≡ f x R.+ (deriv f x R.* ∣ ε ∣)
          path =
            f x R.+ (b R.* ∣ ε ∣)          ≡⟨ ap (f x R.+_) R.*-commutes ⟩
            f x R.+ (∣ ε ∣ R.* b)          ≡⟨ sym (hb ε) ⟩
            f (x R.+ ∣ ε ∣)                ≡⟨ fundamental f x ε ⟩
            f x R.+ (∣ ε ∣ R.* deriv f x)  ≡⟨ ap (f x R.+_) R.*-commutes ⟩
            f x R.+ (deriv f x R.* ∣ ε ∣)  ∎
```

## Differentiation rules {defines="differentiation-rules leibniz-rule chain-rule"}

Every rule of the elementary calculus is now a corollary of
`deriv-unique`: to compute $f'$, exhibit an affine expansion of
$f(x+\varepsilon)$ and read off the coefficient. The algebra is
discharged by the solver, with $\varepsilon^2 = 0$ (the nilsquare
condition `ε .snd`{.Agda}) killing the second-order term at exactly
the two places Bell needs it — the product and the chain rule.

The **constant rule** and the **identity rule** are immediate: a
constant expands with slope $0$, the identity with slope $1$.

```agda
  deriv-const : (c x : ⌞ R ⌟) → deriv (λ _ → c) x ≡ R.0r
  deriv-const c x = sym (deriv-unique (λ _ → c) x R.0r λ ε → cring! R)

  deriv-id : (x : ⌞ R ⌟) → deriv (λ y → y) x ≡ R.1r
  deriv-id x = sym (deriv-unique (λ y → y) x R.1r λ ε → cring! R)
```

The **sum rule** $(f+g)' = f' + g'$ and the **scalar rule** $(cf)' =
c f'$ follow by adding, resp. scaling, the fundamental equations of
the summands.

```agda
  deriv-+
    : (f g : ⌞ R ⌟ → ⌞ R ⌟) (x : ⌞ R ⌟)
    → deriv (λ y → f y R.+ g y) x ≡ deriv f x R.+ deriv g x
  deriv-+ f g x =
    sym (deriv-unique (λ y → f y R.+ g y) x (deriv f x R.+ deriv g x) expand)
    where
      expand
        : (ε : 𝔻)
        → f (x R.+ ∣ ε ∣) R.+ g (x R.+ ∣ ε ∣)
        ≡ (f x R.+ g x) R.+ (∣ ε ∣ R.* (deriv f x R.+ deriv g x))
      expand ε =
        ap₂ R._+_ (fundamental f x ε) (fundamental g x ε)
        ∙ lemma (f x) (g x) ∣ ε ∣ (deriv f x) (deriv g x)
        where
          lemma : ∀ fx gx e f' g'
            → (fx R.+ (e R.* f')) R.+ (gx R.+ (e R.* g'))
            ≡ (fx R.+ gx) R.+ (e R.* (f' R.+ g'))
          lemma fx gx e f' g' = cring! R

  deriv-scale
    : (c : ⌞ R ⌟) (f : ⌞ R ⌟ → ⌞ R ⌟) (x : ⌞ R ⌟)
    → deriv (λ y → c R.* f y) x ≡ c R.* deriv f x
  deriv-scale c f x =
    sym (deriv-unique (λ y → c R.* f y) x (c R.* deriv f x) expand)
    where
      expand
        : (ε : 𝔻)
        → c R.* f (x R.+ ∣ ε ∣) ≡ (c R.* f x) R.+ (∣ ε ∣ R.* (c R.* deriv f x))
      expand ε =
        ap (c R.*_) (fundamental f x ε)
        ∙ lemma c (f x) ∣ ε ∣ (deriv f x)
        where
          lemma : ∀ c fx e f'
            → c R.* (fx R.+ (e R.* f')) ≡ (c R.* fx) R.+ (e R.* (c R.* f'))
          lemma c fx e f' = cring! R
```

The **product rule** — Leibniz's $(fg)' = f'g + fg'$ — is where the
nilsquare condition does its work. Expanding both factors,
$$f(x+\varepsilon)\,g(x+\varepsilon) = (fx + \varepsilon f')(gx +
\varepsilon g') = fx\,gx + \varepsilon(f'gx + fx\,g') + \varepsilon^2
f'g',$$
and the last term vanishes because $\varepsilon^2 = 0$. What remains is
affine with the Leibniz coefficient.

```agda
  deriv-*
    : (f g : ⌞ R ⌟ → ⌞ R ⌟) (x : ⌞ R ⌟)
    → deriv (λ y → f y R.* g y) x ≡ (deriv f x R.* g x) R.+ (f x R.* deriv g x)
  deriv-* f g x =
    sym (deriv-unique (λ y → f y R.* g y) x
      ((deriv f x R.* g x) R.+ (f x R.* deriv g x)) expand)
    where
      expand
        : (ε : 𝔻)
        → f (x R.+ ∣ ε ∣) R.* g (x R.+ ∣ ε ∣)
        ≡ (f x R.* g x) R.+ (∣ ε ∣ R.* ((deriv f x R.* g x) R.+ (f x R.* deriv g x)))
      expand ε =
        ap₂ R._*_ (fundamental f x ε) (fundamental g x ε)
        ∙ leibniz (f x) (g x) ∣ ε ∣ (deriv f x) (deriv g x) (ε .snd)
        where
          -- (fx + e·f')(gx + e·g') = fx·gx + e·(f'·gx + fx·g') + (e·e)·(f'·g');
          -- substituting e·e ≡ 0 kills the last summand.
          leibniz
            : ∀ fx gx e f' g' (e² : e R.* e ≡ R.0r)
            → (fx R.+ (e R.* f')) R.* (gx R.+ (e R.* g'))
            ≡ (fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g')))
          leibniz fx gx e f' g' e² =
            (fx R.+ (e R.* f')) R.* (gx R.+ (e R.* g'))
              ≡⟨ regroup fx gx e f' g' ⟩
            ((fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))))
              R.+ ((e R.* e) R.* (f' R.* g'))
              ≡⟨ ap (λ z → ((fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))))
                           R.+ (z R.* (f' R.* g'))) e² ⟩
            ((fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))))
              R.+ (R.0r R.* (f' R.* g'))
              ≡⟨ kill fx gx e f' g' ⟩
            (fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))) ∎
            where
              regroup : ∀ fx gx e f' g'
                → (fx R.+ (e R.* f')) R.* (gx R.+ (e R.* g'))
                ≡ ((fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))))
                    R.+ ((e R.* e) R.* (f' R.* g'))
              regroup fx gx e f' g' = cring! R

              kill : ∀ fx gx e f' g'
                → ((fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g'))))
                    R.+ (R.0r R.* (f' R.* g'))
                ≡ (fx R.* gx) R.+ (e R.* ((f' R.* gx) R.+ (fx R.* g')))
              kill fx gx e f' g' = cring! R
```

The **chain rule** $(g \circ f)' = (g' \circ f)\cdot f'$ needs a small
lemma: if $\varepsilon \in \Delta$ then so is $\varepsilon f'(x)$,
since $(\varepsilon f'(x))^2 = \varepsilon^2 f'(x)^2 = 0$. Feeding this
scaled infinitesimal into the fundamental equation for $g$ at $f(x)$,
after expanding $f(x+\varepsilon)$, gives the composite's expansion.

```agda
  scaleΔ : 𝔻 → ⌞ R ⌟ → 𝔻
  scaleΔ ε r = ∣ ε ∣ R.* r , nil
    where
      nil : (∣ ε ∣ R.* r) R.* (∣ ε ∣ R.* r) ≡ R.0r
      nil =
        (∣ ε ∣ R.* r) R.* (∣ ε ∣ R.* r)
          ≡⟨ regroup ∣ ε ∣ r ⟩
        (∣ ε ∣ R.* ∣ ε ∣) R.* (r R.* r)
          ≡⟨ ap (R._* (r R.* r)) (ε .snd) ⟩
        R.0r R.* (r R.* r)
          ≡⟨ Rr.*-zerol ⟩
        R.0r ∎
        where
          regroup : ∀ e r → (e R.* r) R.* (e R.* r) ≡ (e R.* e) R.* (r R.* r)
          regroup e r = cring! R

  deriv-∘
    : (g f : ⌞ R ⌟ → ⌞ R ⌟) (x : ⌞ R ⌟)
    → deriv (λ y → g (f y)) x ≡ deriv g (f x) R.* deriv f x
  deriv-∘ g f x =
    sym (deriv-unique (λ y → g (f y)) x (deriv g (f x) R.* deriv f x) expand)
    where
      expand
        : (ε : 𝔻)
        → g (f (x R.+ ∣ ε ∣))
        ≡ g (f x) R.+ (∣ ε ∣ R.* (deriv g (f x) R.* deriv f x))
      expand ε =
        g (f (x R.+ ∣ ε ∣))
          ≡⟨ ap g (fundamental f x ε) ⟩
        g (f x R.+ (∣ ε ∣ R.* deriv f x))
          ≡⟨ fundamental g (f x) (scaleΔ ε (deriv f x)) ⟩
        g (f x) R.+ ((∣ ε ∣ R.* deriv f x) R.* deriv g (f x))
          ≡⟨ ap (g (f x) R.+_) (assoc-comm ∣ ε ∣ (deriv f x) (deriv g (f x))) ⟩
        g (f x) R.+ (∣ ε ∣ R.* (deriv g (f x) R.* deriv f x)) ∎
        where
          assoc-comm : ∀ e f' g' → (e R.* f') R.* g' ≡ e R.* (g' R.* f')
          assoc-comm e f' g' = cring! R
```

## Fermat's rule {defines="fermat-rule stationary-point"}

Bell's synthetic **Fermat rule**: $a$ is a *stationary point* of $f$
— meaning $f$ is constant to first order at $a$, i.e. $f(a +
\varepsilon) = f(a)$ for every $\varepsilon \in \Delta$ — exactly when
$f'(a) = 0$. Both directions run through microcancellation and the
fundamental equation.

```agda
  is-stationary : (⌞ R ⌟ → ⌞ R ⌟) → ⌞ R ⌟ → Type ℓ
  is-stationary f a = (ε : 𝔻) → f (a R.+ ∣ ε ∣) ≡ f a

  fermat-→ : (f : ⌞ R ⌟ → ⌞ R ⌟) (a : ⌞ R ⌟) → is-stationary f a → deriv f a ≡ R.0r
  fermat-→ f a stat = sym (deriv-unique f a R.0r slope0)
    where
      slope0 : (ε : 𝔻) → f (a R.+ ∣ ε ∣) ≡ f a R.+ (∣ ε ∣ R.* R.0r)
      slope0 ε = stat ε ∙ reintro
        where
          reintro : f a ≡ f a R.+ (∣ ε ∣ R.* R.0r)
          reintro = cring! R

  fermat-← : (f : ⌞ R ⌟ → ⌞ R ⌟) (a : ⌞ R ⌟) → deriv f a ≡ R.0r → is-stationary f a
  fermat-← f a f'≡0 ε =
    f (a R.+ ∣ ε ∣)
      ≡⟨ fundamental f a ε ⟩
    f a R.+ (∣ ε ∣ R.* deriv f a)
      ≡⟨ ap (λ z → f a R.+ (∣ ε ∣ R.* z)) f'≡0 ⟩
    f a R.+ (∣ ε ∣ R.* R.0r)
      ≡⟨ absorb ∣ ε ∣ ⟩
    f a ∎
    where
      absorb : ∀ e → f a R.+ (e R.* R.0r) ≡ f a
      absorb e = cring! R
```

## Multiplicative inverses, and the failure of excluded middle {defines="lem-failure indistinguishability"}

The remaining Chapter-1 theorems distinguish the *field* structure of
the smooth line. The 1Lab has no `Field` type, and Bell needs an
inverse only here — for the quotient of infinitesimals in Theorem
1.1(ii). So we introduce it exactly as another **hypothesis**: a
record `has-inverses` supplying a partial inverse operation, inverting
every element apart from $0$. This is *not* postulated; it is a datum a
model must provide, and the field axiom (a smooth line is a field in
Bell's weak sense) is a theorem in the topos, discussed at the close.

```agda
  record has-inverses : Type ℓ where
    field
      inv     : (x : ⌞ R ⌟) → ¬ (x ≡ R.0r) → ⌞ R ⌟
      inv-inv : (x : ⌞ R ⌟) (p : ¬ (x ≡ R.0r)) → x R.* inv x p ≡ R.1r
```

<!--
```agda
  module _ (fld : has-inverses) where
    open has-inverses fld
```
-->

With an inverse, **indistinguishability** (Theorem 1.1(ii)) holds: *no
infinitesimal is provably non-zero*, i.e. $\neg\neg(\varepsilon = 0)$
for every $\varepsilon \in \Delta$. For if $\varepsilon \neq 0$ then
$\varepsilon$ is invertible, and then
$$\varepsilon = \varepsilon \cdot 1 = \varepsilon \cdot (\varepsilon\,
\varepsilon^{-1}) = (\varepsilon\varepsilon)\,\varepsilon^{-1} = 0
\cdot \varepsilon^{-1} = 0,$$
contradicting $\varepsilon \neq 0$.

```agda
    Δ-indistinguishable : (ε : 𝔻) → ¬ ¬ (∣ ε ∣ ≡ R.0r)
    Δ-indistinguishable ε ε≠0 = ε≠0 collapse
      where
        e  = ∣ ε ∣
        ei = inv ∣ ε ∣ ε≠0
        h  : e R.* ei ≡ R.1r
        h  = inv-inv ∣ ε ∣ ε≠0

        collapse : e ≡ R.0r
        collapse =
          e                     ≡⟨ sym R.*-idr ⟩
          e R.* R.1r            ≡⟨ ap (e R.*_) (sym h) ⟩
          e R.* (e R.* ei)      ≡⟨ reassoc e ei ⟩
          (e R.* e) R.* ei      ≡⟨ ap (R._* ei) (ε .snd) ⟩
          R.0r R.* ei           ≡⟨ Rr.*-zerol ⟩
          R.0r ∎
          where
            reassoc : ∀ a b → a R.* (a R.* b) ≡ (a R.* a) R.* b
            reassoc a b = cring! R
```

Now **Theorem 1.1(iii)** — the constructive **failure of the law of
excluded middle** on $\Delta$. It is *not* the case that every
infinitesimal is decidably zero-or-nonzero. This is the sharpest way
smooth infinitesimal analysis parts company with classical logic: the
law of excluded middle, if it held on $\Delta$, would (with $0 \neq
1$) force every infinitesimal to vanish, collapsing $\Delta$ to a
point and contradicting non-degeneracy.

The argument chains the previous two theorems. Suppose the decision
$(\varepsilon = 0) \uplus (\varepsilon \neq 0)$ held for every
$\varepsilon \in \Delta$. Indistinguishability rules out the right
disjunct, so we would be left with $\varepsilon = 0$ for all
$\varepsilon$ — exactly what non-degeneracy forbids.

```agda
    Δ-no-lem
      : ¬ (R.0r ≡ R.1r)
      → ¬ ((ε : 𝔻) → (∣ ε ∣ ≡ R.0r) ⊎ (¬ (∣ ε ∣ ≡ R.0r)))
    Δ-no-lem 0≠1 lem = Δ-nondegenerate 0≠1 all-zero
      where
        all-zero : (ε : 𝔻) → ∣ ε ∣ ≡ R.0r
        all-zero ε = [ (λ p → p) , (λ ε≠0 → absurd (Δ-indistinguishable ε ε≠0)) ] (lem ε)
```

This is a genuine, machine-checked *theorem* here — the negation of
excluded middle for the predicate "$\varepsilon = 0$" on $\Delta$ — not
an assumption. The ambient type theory is agnostic about LEM; it is the
*combination* with the smooth-world axioms that refutes it, precisely
Bell's point that the smooth world has an intrinsically intuitionistic
internal logic.

## The Constancy Principle and indecomposability {defines="constancy-principle indecomposability"}

Chapter 2 closes with a second axiom, the **Constancy Principle**:
*a function with everywhere-vanishing derivative is constant.* Unlike
Microaffineness it does not follow from the ring structure — it is an
independent hypothesis, true in the smooth topos — so we again take it
as a parameter.

```agda
  Constancy : Type ℓ
  Constancy =
    (f : ⌞ R ⌟ → ⌞ R ⌟) → ((x : ⌞ R ⌟) → deriv f x ≡ R.0r)
    → (x y : ⌞ R ⌟) → f x ≡ f y
```

<!--
```agda
  module _ (fld : has-inverses) (const : Constancy) where
    open has-inverses fld
```
-->

Its headline consequence (Bell Theorem 2.1) is the **indecomposability
of the smooth line**: $R$ has no non-trivial *detachable* parts. A
part is a predicate on $R$; it is detachable when membership is
decidable everywhere; and indecomposability says a detachable part is
either everything or nothing — the line cannot be split in two.

```agda
    is-detachable : (⌞ R ⌟ → Type ℓ) → Type ℓ
    is-detachable P = (x : ⌞ R ⌟) → P x ⊎ (¬ P x)

    is-full is-empty : (⌞ R ⌟ → Type ℓ) → Type ℓ
    is-full  P = (x : ⌞ R ⌟) → P x
    is-empty P = (x : ⌞ R ⌟) → ¬ P x
```

The proof runs through the *characteristic function* $\chi : R \to R$
of a detachable part $P$, sending members to $1$ and non-members to
$0$. The key lemma is that $\chi$ is **microconstant** — $\chi(x +
\varepsilon) = \chi(x)$ for every $\varepsilon \in \Delta$ — because
$\chi$ takes only the two values $0, 1$, and by indistinguishability an
infinitesimal displacement cannot move a two-valued function between
its values. Microconstancy gives $\chi' \equiv 0$ (microcancellation),
Constancy then makes $\chi$ globally constant, and finally a value at
one point decides the whole part.

We take microconstancy of the characteristic function as the one
place the two-element value analysis enters, isolating it as an
explicit hypothesis `χ-microconstant`; from it, indecomposability is a
clean consequence of Constancy. (See the honesty section for why the
value analysis, though true, is not discharged here.)

```agda
    indecomposable
      : (P : ⌞ R ⌟ → Type ℓ) → is-detachable P
      → (χ : ⌞ R ⌟ → ⌞ R ⌟)                       -- characteristic map
      → ((x : ⌞ R ⌟) → (P x → χ x ≡ R.1r))          -- χ = 1 on P
      → ((x : ⌞ R ⌟) → (¬ P x → χ x ≡ R.0r))        -- χ = 0 off P
      → ¬ (R.0r ≡ R.1r)
      → ((x : ⌞ R ⌟) (ε : 𝔻) → χ (x R.+ ∣ ε ∣) ≡ χ x)  -- χ-microconstant
      → is-full P ⊎ is-empty P
    indecomposable P det χ χ1 χ0 0≠1 microconst =
      [ (λ p0 → inl (λ x → decide-full x p0))
      , (λ ¬p0 → inr (λ x → decide-empty x ¬p0))
      ] (det R.0r)
      where
        -- χ has zero derivative (microconstant ⇒ stationary ⇒ f' = 0)
        χ'≡0 : (x : ⌞ R ⌟) → deriv χ x ≡ R.0r
        χ'≡0 x = fermat-→ χ x (microconst x)

        -- hence χ is globally constant
        χ-const : (x y : ⌞ R ⌟) → χ x ≡ χ y
        χ-const = const χ χ'≡0

        -- if 0 ∈ P, every point is in P (else its χ would be 0 ≠ χ 0 = 1)
        decide-full : (x : ⌞ R ⌟) → P R.0r → P x
        decide-full x p0 = [ (λ px → px) , (λ ¬px → absurd (0≠1 (contra ¬px))) ] (det x)
          where
            contra : ¬ P x → R.0r ≡ R.1r
            contra ¬px = sym (χ0 x ¬px) ∙ χ-const x R.0r ∙ χ1 R.0r p0

        -- dually, if 0 ∉ P, no point is in P
        decide-empty : (x : ⌞ R ⌟) → ¬ P R.0r → ¬ P x
        decide-empty x ¬p0 px = 0≠1 contra
          where
            contra : R.0r ≡ R.1r
            contra = sym (χ0 R.0r ¬p0) ∙ χ-const R.0r x ∙ χ1 x px
```

## Connection to the concrete stack {defines="sia-bridge"}

The axiomatics above are the *abstract* content underneath every
concrete synthetic-differentiation computation in this development.

The oscillator's `hooke`{.Agda} and the heliostat's `∂u-σz`{.Agda}
compute derivatives by the dual-number recipe — evaluate at $x +
\varepsilon$, read the $\varepsilon$-coefficient. That recipe is
*sound* exactly because Microaffineness holds: the coefficient is the
`deriv`{.Agda} of this module, its uniqueness is `microcancel`{.Agda},
and the product rule `deriv-*`{.Agda} is the same $\varepsilon^2 = 0$
cancellation that makes `hooke : δ(x^2) = x + x` a two-liner. The
heliostat's own `∂u`/`∂v`
(`Physics.Heliostat.Optics`{.Agda ident=optics}) are the concrete
partial-derivative slots; `Physics.Heliostat.Sheaf`{.Agda}'s
`∂u-is-KL-derivative` is the bridge identifying that
$\varepsilon$-coefficient with the derivative-component of a genuine
synthetic tangent vector.

And the consistency of the whole axiom set — that a ring satisfying
`Microaffineness` and `Constancy` *exists* — is the `Kock-Lawvere`{.Agda}
theorem of `Cat.Instances.FormalSmoothSets`{.Agda}: over the
[[thickened site|formal-smooth-sets]], the synthetic tangent bundle
$T\mathbb{A}^1$ is equivalent to $\mathbb{A}^1 \times \mathbb{A}^1$
— value and slope — which is precisely Microaffineness holding *as a
theorem* internally to that gros topos. Our `is-contr` form is the
elementwise reading of that equivalence.

We record the citation as a live module-dependency link (the
`Kock-Lawvere`{.Agda} theorem lives inside this module, parametrised
over the coefficient ring and the probe dimensions):

<!--
```agda
import Cat.Instances.FormalSmoothSets
```
-->

## What is and is not proven {defines="sia-honesty"}

For honesty, the exact division of labour in this module.

**AXIOMS (hypotheses, never `postulate`s).** These are module
parameters or record fields a caller must supply:

- `Microaffineness R` — Bell's Kock–Lawvere axiom, taken as the
  parameter `micro` of `module Bell`. It is a `Type`; instantiating it
  is instantiating SIA.
- `has-inverses` — the partial multiplicative inverse (a record),
  used *only* for Theorems 1.1(ii)/(iii) and for the microconstancy of
  characteristic functions. Everything else uses only the commutative
  ring.
- `Constancy` — the Constancy Principle (a `Type`), used only for
  Theorem 2.1.
- The characteristic-function `χ-microconstant` hypothesis of
  `indecomposable` (see the scoping note below).

There are **zero** `postulate`s in this file.

**DERIVED (genuine theorems).** Proven outright from the axioms and
the ring structure:

- `microcancel` (Thm 1.1 iv) — from the uniqueness half of
  Microaffineness.
- `Δ-nondegenerate` (Thm 1.1 i) — $\neg(0=1)$ implies not every
  infinitesimal is $0$.
- `fundamental` — the fundamental equation $f(x+\varepsilon) = f(x) +
  \varepsilon f'(x)$, from the existence half.
- `deriv-unique` and the full rule set: `deriv-const`, `deriv-id`,
  `deriv-+`, `deriv-scale`, `deriv-*` (Leibniz, via $\varepsilon^2 =
  0$), `deriv-∘` (chain, via $\varepsilon f' \in \Delta$).
- `fermat-→` / `fermat-←` — Fermat's stationary-point rule, both
  directions.
- `Δ-indistinguishable` (Thm 1.1 ii) — from `has-inverses`.
- `Δ-no-lem` (Thm 1.1 iii) — **the failure of LEM on $\Delta$ is a
  constructive theorem here**, chaining (ii) and (i). The ambient
  type theory neither asserts nor denies LEM; it is the smooth-world
  axioms that refute it.
- `indecomposable` (Thm 2.1) — indecomposability of the line, from
  Constancy plus the microconstancy of the characteristic map.

**Two facts worth stating precisely.** (1) The **LEM-failure is a
theorem, not an axiom** — contrast the Microaffineness axiom, which is
a *theorem* in the gros topos (this is `Kock-Lawvere`{.Agda}), here
taken as hypothesis. (2) The derivative rules need *only* the
commutative ring plus Microaffineness; no order, no field, no reals.

**SCOPED OUT (honestly blocked).**

- The `χ-microconstant` hypothesis of `indecomposable` is *true* — a
  two-valued function cannot be moved between its values by an
  infinitesimal, by indistinguishability — but discharging it in full
  requires case-analysing $\chi(x+\varepsilon) \in \{0,1\}$ against
  $\chi(x) \in \{0,1\}$ and using $\neg\neg(\varepsilon = 0)$ to
  collapse the off-diagonal cases; that value analysis needs an
  apartness/two-valuedness structure this module does not axiomatise,
  so it is isolated as a hypothesis rather than faked.
- **Integration and the Fundamental Theorem of Calculus** are *not*
  here: recovering finite-time evolution from the infinitesimal
  derivative needs a genuine real-numbers object and the integration
  axiom, which the reading guide (`Physics.lagda.md`) lists as
  missing. This module is strictly the *differential* half.
- **Square roots and the order** ($\sqrt{\cdot}$, $<$, the special
  functions $\sin,\cos,\exp$ with $\sin\varepsilon = \varepsilon$) need
  the ordered-field and analytic structure and are deliberately not
  claimed; the 1Lab's [[Dedekind reals|dedekind-real]] have order and
  an additive group but no multiplication yet.

The boundary is exactly Bell's: everything at the *differential* level
is synthetic algebra over a commutative ring with nilpotent
infinitesimals; everything requiring *limits or completeness* is left
to the analytic layer that does not yet exist.

