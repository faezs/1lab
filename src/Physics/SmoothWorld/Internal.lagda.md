<!--
```agda
open import Cat.Prelude

open import Algebra.Ring.Commutative

import Cat.Instances.FormalSmoothSets

open Functor
```
-->

```agda
module Physics.SmoothWorld.Internal {ℓ} (R : CRing ℓ) where
```

# Bell's smooth line, grounded in the model {defines="internal-microaffineness grounded-sia"}

The companion module `Physics.SmoothWorld`{.Agda} develops J. L. Bell's
[[smooth infinitesimal analysis|synthetic-derivative]] *axiomatically*:
it posits the Principle of **Microaffineness** — every map of the
infinitesimals into the line is uniquely affine — as a hypothesis over
an abstract [[commutative ring|commutative-ring]], and derives the
differential calculus. That development is honest but **ungrounded**:
its axiom holds in *no* set-level ring (the point of the blip-function
argument is exactly that arbitrary set-functions are not affine), and
the topos where it *does* hold could not be fed in.

This module supplies the missing grounding. Over the gros topos
`FrmlSmthSet`{.Agda} of [[formal smooth sets|formal-smooth-sets]], the
representable line $\bA^1$ *is* Bell's smooth line, and the
[[Kock–Lawvere|kock-lawvere]] theorem — already **proved** in
`Cat.Instances.FormalSmoothSets`{.Agda} — *is* Bell's Microaffineness
axiom, holding as a theorem. We read it that way, and extract from it,
directly, the two pillars of Bell's Chapter 1: **microcancellation**
and the **fundamental equation** of the calculus. No axiom is assumed;
every result below is `Kock-Lawvere`{.Agda} or its being an
equivalence.

<!--
```agda
open Cat.Instances.FormalSmoothSets R
```
-->

## The smooth line and its tangents, at a stage

A generalized element of a formal smooth set at a probe $\bA^{n}_{k}$ is
a plot — a section of the presheaf. We name the two that matter: the
**points** of the line $\bA^1$, and its **tangents** — the plots of the
[[tangent bundle|formal-sets]] $T\bA^1 = \operatorname{Maps}(\bD,
\bA^1)$, the maps *of the infinitesimal disk into the line*. It is
these disk-maps, not arbitrary set-functions, that are Bell's smooth
functions on the microneighbourhood; that distinction is the whole
reason the grounding works.

```agda
Pt : Nat → Nat → Type ℓ
Pt n k = ∣ 𝔸¹ .F₀ (𝔸 n k) ∣

Tangent : Nat → Nat → Type ℓ
Tangent n k = ∣ T 𝔸¹ .F₀ (𝔸 n k) ∣
```

## Microaffineness, as a theorem

`Kock-Lawvere`{.Agda}, at each probe, is an equivalence between the
tangents at that stage and pairs (value, slope) of points. Read as
Bell reads it: **a disk-map into the line is, uniquely, a value together
with a derivative** — his Principle of Microaffineness, now a theorem
of the model rather than a posited axiom.

```agda
KL : ∀ n k → Tangent n k ≃ (Pt n k × Pt n k)
KL n k = Kock-Lawvere n k

value deriv : ∀ n k → Tangent n k → Pt n k
value n k τ = KL n k .fst τ .fst
deriv n k τ = KL n k .fst τ .snd

tangent : ∀ n k → Pt n k → Pt n k → Tangent n k
tangent n k v b = Equiv.from (KL n k) (v , b)
```

The **fundamental equation** of the differential calculus,
$f(x+\varepsilon) = f(x) + \varepsilon\,f'(x)$, is Bell's Taylor
expansion with an identically-zero remainder. Here it is exactly the
statement that a tangent is *reconstructed* from its value and
derivative — the unit of the Kock–Lawvere equivalence. There is no
approximation and no limit: the disk-map and the affine map with those
data are *equal*.

```agda
fundamental : ∀ n k (τ : Tangent n k)
  → τ ≡ tangent n k (value n k τ) (deriv n k τ)
fundamental n k τ = sym (Equiv.η (KL n k) τ)
```

## Microcancellation, as injectivity

Bell's Theorem 1.1(iv), **microcancellation** — one cannot divide by an
infinitesimal, but a universally-quantified one may be cancelled — is,
in the model, precisely the **injectivity** of the Kock–Lawvere
equivalence: two tangents with the same value and the same derivative
are the same tangent. The uniqueness that Bell extracts from his axiom
is the uniqueness built into an equivalence.

```agda
microcancel : ∀ n k (τ σ : Tangent n k)
  → value n k τ ≡ value n k σ
  → deriv n k τ ≡ deriv n k σ
  → τ ≡ σ
microcancel n k τ σ pv pd = Equiv.injective (KL n k) (ap₂ _,_ pv pd)
```

## The unique slope

Assembling the two, we recover Bell's Microaffineness in its native
form — the *unique-existence* of the slope. For every tangent there is
a **unique** derivative reconstructing it, i.e. the type of slopes
witnessing the fundamental equation is contractible. The centre is the
Kock–Lawvere derivative; uniqueness runs the counit through the
value/derivative projection.

```agda
unique-slope : ∀ n k (τ : Tangent n k)
  → is-contr (Σ[ b ∈ Pt n k ] (τ ≡ tangent n k (value n k τ) b))
unique-slope n k τ .centre = deriv n k τ , fundamental n k τ
unique-slope n k τ .paths (b , p) =
  Σ-prop-path (λ _ → hlevel 1) slope-eq
  where
    to-eq : KL n k .fst τ ≡ (value n k τ , b)
    to-eq = ap (KL n k .fst) p ∙ Equiv.ε (KL n k) (value n k τ , b)

    slope-eq : deriv n k τ ≡ b
    slope-eq = ap snd to-eq
```

## What is grounded, and what is not

**Grounded, zero postulates.** For the representable line $\bA^1$ over
the gros topos, Bell's **Microaffineness** holds as a theorem
(`KL`{.Agda}/`unique-slope`{.Agda}) — it *is* `Kock-Lawvere`{.Agda},
whose own proof rests on the walking-square-zero property of the dual
numbers (`Cat.Instances.FormalSmoothSets`{.Agda}). **Microcancellation**
is its injectivity, and the **fundamental equation** is its unit. This
is the model-side vindication that `Physics.SmoothWorld`{.Agda} promised
but could only assume: the smooth line, its tangents, and the exactness
of its first-order Taylor expansion, exhibited in a topos where they are
theorems.

**Not grounded — and the boundary is sharp.** The abstract
`Physics.SmoothWorld`{.Agda} quantifies its Microaffineness over
*arbitrary set-functions* out of the nilsquares of a bare ring. That is
a strictly **stronger, and false-in-general, statement**: Bell's
consistency depends on his function arrow being the *smooth*
(internal-hom) one — the disk-maps $T\bA^1$ used here — not
`ring → ring`. `Kock-Lawvere`{.Agda} discharges the smooth version; the
set-level version over a concrete function ring is not a theorem, and
conflating the two is the error this module exists to avoid.

The full internal calculus for *line endomorphisms* $f : \bA^1 \to
\bA^1$ — `deriv f`, the Leibniz and chain rules at the internal-hom
level — is **not** reached here. It needs machinery the 1Lab does not
have: an internal **ring-object** structure $+, \cdot, 0, 1$ on $\bA^1$
(constructible from the polynomial API, but unbuilt), and — the genuine
blocker — the characterization of smooth self-maps as polynomials,
$[\bA^1,\bA^1](U) \simeq \cO(U)[t]$, which requires general
representable products $\bA^{n}_{k} \times \bA^{m}_{j}$, i.e. the
**tensor product of $R$-algebras** $R[X \uplus Y] \simeq R[X] \otimes_R
R[Y]$. Only the bespoke $\times\bD$ product is shipped (via the
dual-number universal property) — exactly enough for the derivative and
Microaffineness, and no more. Nor is there any **internal-language /
Kripke–Joyal forcing** in the 1Lab (the sole syntactic doctrine is
*regular* logic, without $\forall$ or $\Rightarrow$); we reason with
generalized elements directly, which suffices for every result above and
is blocked at exactly the $\forall(f : \bA^1 \to \bA^1)$ statement the
tensor product already blocks. Those are the three well-posed projects —
the algebra tensor, the ring-object, the forcing relation — between here
and Bell's calculus internalized in full.
