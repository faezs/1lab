<!--
```agda
open import 1Lab.Prelude hiding (_+_ ; _*_ ; _-_ ; ∣_∣)

open import Algebra.Ring.Commutative

open import Data.Sum.Base

open import Physics.SmoothWorld
```
-->

```agda
module Physics.SmoothWorld.Indecomposable where
```

# Discharging microconstancy: indecomposability of the smooth line {defines="microconstancy-theorem"}

`Physics.SmoothWorld`{.Agda}'s `Bell.indecomposable`{.Agda} — Bell's
Theorem 2.1, that the smooth line has no non-trivial *detachable* parts
— was proven there behind one honest hypothesis: that the
characteristic function $\chi$ of a detachable part is **microconstant**,
$\chi(x + \varepsilon) = \chi(x)$ for every nilsquare $\varepsilon$.
The honesty section of that module flags this as *true but not
discharged*, because closing it requires case-analysing $\chi(x +
\varepsilon) \in \{0,1\}$ against $\chi(x) \in \{0,1\}$ and collapsing
the off-diagonal cases with $\neg\neg(\varepsilon = 0)$.

This module carries out exactly that value analysis and **discharges the
hypothesis into a theorem**, using nothing new: only the
already-proven `Δ-indistinguishable`{.Agda} (Theorem 1.1(ii), from
`has-inverses`), the detachability decision, the two defining equations
of $\chi$, and $0 \neq 1$ — all of which are already threaded through
`indecomposable`{.Agda}. No new axiom, no `postulate`. We then re-derive
a **hypothesis-free** indecomposability result as a pure application.

We re-open `module Bell`{.Agda} over the same ring and Microaffineness
axiom; we do **not** edit `SmoothWorld.lagda.md`{.Agda}. After the open,
the names living in Bell's anonymous `(fld)` and `(fld)(const)`
submodules — `Δ-indistinguishable`{.Agda}, `indecomposable`{.Agda},
`is-full`{.Agda}, `is-empty`{.Agda} — appear generalised over their
parameters.

<!--
```agda
module _ {ℓ} (R : CRing ℓ) (micro : Microaffineness R) where
  private
    module R = CRing-on (R .snd)
  open Bell R micro
```
-->

## Microconstancy of a two-valued map

The crux. Given a detachable predicate $P$ with characteristic map
$\chi$ (value $1$ on $P$, value $0$ off it), an infinitesimal
displacement cannot change $\chi$'s value. We decide both $\chi(x)$ and
$\chi(x + \varepsilon)$ via detachability, giving four cases. The two
**matching** cases ($P$ holds at both points, or fails at both) give the
equality directly — both sides are the same literal, $1$ or $0$. The two
**mismatched** cases are impossible: if, say, $P(x + \varepsilon)$ but
$\neg P(x)$, then were $\varepsilon = 0$ we would have $x + \varepsilon
= x$ and hence $\chi(x + \varepsilon) = \chi(x)$, i.e. $1 = 0$,
contradicting $0 \neq 1$. So $\varepsilon \neq 0$ — which
`Δ-indistinguishable`{.Agda} forbids for a nilsquare infinitesimal. The
resulting `absurd`{.Agda} proves the (never-inhabited) mismatched
equality, $\llbracket R \rrbracket$ being a set.

We inline the detachability type $(x) \to P\,x \uplus \neg P\,x$ rather
than Bell's `is-detachable`{.Agda}, which — living in the `(const)`
submodule — carries a spurious `Constancy` parameter that this lemma
does not need (it depends only on `fld`).

```agda
  χ-microconstant-thm
    : (fld : has-inverses)
    → (P : ⌞ R ⌟ → Type ℓ) → ((x : ⌞ R ⌟) → P x ⊎ ¬ P x)
    → (χ : ⌞ R ⌟ → ⌞ R ⌟)
    → (∀ x → P x → χ x ≡ R.1r) → (∀ x → ¬ P x → χ x ≡ R.0r)
    → ¬ (R.0r ≡ R.1r)
    → (x : ⌞ R ⌟) (ε : 𝔻) → χ (x R.+ ∣ ε ∣) ≡ χ x
  χ-microconstant-thm fld P det χ χ1 χ0 0≠1 x ε
    with det x | det (x R.+ ∣ ε ∣)
  -- matching cases: same literal on both sides
  ... | inl px  | inl pxε  = χ1 (x R.+ ∣ ε ∣) pxε ∙ sym (χ1 x px)
  ... | inr npx | inr npxε = χ0 (x R.+ ∣ ε ∣) npxε ∙ sym (χ0 x npx)
  -- mismatch  P x , ¬ P (x+ε):  ε ≡ 0 would force  1 ≡ 0
  ... | inl px  | inr npxε = absurd (Δ-indistinguishable fld ε ε≠0)
    where
      ε≠0 : ¬ (∣ ε ∣ ≡ R.0r)
      ε≠0 h = 0≠1
        ( sym (χ0 (x R.+ ∣ ε ∣) npxε)
        ∙ ap χ (ap (x R.+_) h ∙ R.+-idr)
        ∙ χ1 x px )
  -- mismatch  ¬ P x , P (x+ε):  ε ≡ 0 would force  0 ≡ 1
  ... | inr npx | inl pxε = absurd (Δ-indistinguishable fld ε ε≠0)
    where
      ε≠0 : ¬ (∣ ε ∣ ≡ R.0r)
      ε≠0 h = 0≠1
        ( sym
          ( sym (χ1 (x R.+ ∣ ε ∣) pxε)
          ∙ ap χ (ap (x R.+_) h ∙ R.+-idr)
          ∙ χ0 x npx ) )
```

## Hypothesis-free indecomposability

With microconstancy now a theorem, `Bell.indecomposable`{.Agda} applies
with its final hypothesis supplied by `χ-microconstant-thm`{.Agda}. The
result is Theorem 2.1 with **no** remaining microconstancy assumption:
every detachable part of the smooth line is full or empty, given only
the field structure, the Constancy Principle, and $0 \neq 1$.

```agda
  indecomposable-thm
    : (fld : has-inverses) (const : Constancy)
    → (P : ⌞ R ⌟ → Type ℓ) → ((x : ⌞ R ⌟) → P x ⊎ ¬ P x)
    → (χ : ⌞ R ⌟ → ⌞ R ⌟)
    → (∀ x → P x → χ x ≡ R.1r) → (∀ x → ¬ P x → χ x ≡ R.0r)
    → ¬ (R.0r ≡ R.1r)
    → is-full fld const P ⊎ is-empty fld const P
  indecomposable-thm fld const P det χ χ1 χ0 0≠1 =
    indecomposable fld const P det χ χ1 χ0 0≠1
      (χ-microconstant-thm fld P det χ χ1 χ0 0≠1)
```

This closes gap G4: the `χ-microconstant` datum that
`SmoothWorld.lagda.md`{.Agda} carries as an explicit hypothesis is, over
any ring with `has-inverses`, a genuine consequence of
indistinguishability — no new structure, and zero postulates.
