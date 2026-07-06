<!--
```agda
open import Cat.Prelude

open import Cat.Diagram.Sieve

import Cat.Reasoning
```
-->

```agda
module Physics.SmoothWorld.Forcing {ℓ} (C : Precategory ℓ ℓ) where
```

<!--
```agda
private module Cr = Cat.Reasoning C
```
-->


# Computing with the internal logic that exists {defines="internal-logic-fragment"}

Before building the first-order layer, we drive the machinery already
present. The internal logic of a presheaf topos $\rm{PSh}(\cC)$ — and
in particular of the smooth site $\rm{ThCartSp}$ where synthetic
differential geometry lives — has as its object of truth-values the
[[subobject classifier|subobject-classifier-presheaf]] $\Omega$, which
`Cat.Instances.Presheaf.Omega`{.Agda} builds as the presheaf of
[[sieves|sieve]]. A truth value at a stage $c$ is a sieve on $c$; the
internal connectives are operations on sieves.

We compute with them here, over an arbitrary base $\cC$ (instantiate at
`ThCartSp`{.Agda} for the smooth line's own logic). What is present is
exactly the **regular fragment**: the top truth value and finite — even
arbitrary — meets.

The internal **true** is the maximal sieve, and internal **conjunction**
is the pointwise meet of sieves; arbitrary conjunction is the
intersection over any index.

```agda
⊤ᵢ : ∀ {c} → Sieve C c
⊤ᵢ = maximal'

_∧ᵢ_ : ∀ {c} → Sieve C c → Sieve C c → Sieve C c
_∧ᵢ_ = _∩S_

⋀ᵢ : ∀ {c} {I : Type ℓ} → (I → Sieve C c) → Sieve C c
⋀ᵢ = intersect
```

These *compute* as an internal Heyting-meet-semilattice: conjunction is
idempotent and commutative, and the maximal sieve is its unit. Each is a
one-line consequence of the corresponding law for the propositional
truth-value object $\Omega$, transported across `Sieve-path`{.Agda}
(extensionality for sieves).

```agda
∧ᵢ-idem : ∀ {c} (S : Sieve C c) → (S ∧ᵢ S) ≡ S
∧ᵢ-idem S = ext λ f → Ω-ua fst (λ x → x , x)

∧ᵢ-comm : ∀ {c} (S T : Sieve C c) → (S ∧ᵢ T) ≡ (T ∧ᵢ S)
∧ᵢ-comm S T = ext λ f → Ω-ua (λ (x , y) → y , x) (λ (x , y) → y , x)

∧ᵢ-unit : ∀ {c} (S : Sieve C c) → (S ∧ᵢ ⊤ᵢ) ≡ S
∧ᵢ-unit S = ext λ f → Ω-ua fst (λ x → x , tt)
```

## Building the missing brick: implication

That is the whole of what `Cat.Diagram.Sieve`{.Agda} ships. The first
connective *past* the regular fragment — and the one everything else is
downstream of — is **implication**, which is not there. So we build it.
Its sieve is the standard one: an arrow $f$ forces $S \Rightarrow T$
when, at *every* later stage $g$, membership $fg \in S$ entails $fg \in
T$. That "for all future stages $g$" is precisely the hereditary,
right-adjoint content shared by $\Rightarrow$ and $\forall$, and is why
the regular fragment — with only the left adjoint $\exists$ and finite
meets — omits it. The propositional truncation `elΩ`{.Agda} packages the
$\Pi$ of implications as a truth value, and closure under precomposition
is a reassociation.

```agda
_⇒ᵢ_ : ∀ {c} → Sieve C c → Sieve C c → Sieve C c
(S ⇒ᵢ T) .arrows {y} f =
  elΩ (∀ {z} (g : Cr.Hom z y) → (f Cr.∘ g) ∈ S → (f Cr.∘ g) ∈ T)
(S ⇒ᵢ T) .closed {f = f} hf q = inc λ g mem →
  subst (_∈ T) (Cr.assoc f q g)
    (□-out! hf (q Cr.∘ g) (subst (_∈ S) (sym (Cr.assoc f q g)) mem))
```

The load-bearing fact is that this really is the **Heyting
implication** — the right adjoint to conjunction — i.e. the two-way rule
$$ (R \wedge S) \subseteq T \quad\Longleftrightarrow\quad R \subseteq (S
\Rightarrow T). $$
We prove both directions. **Currying** transports a joint entailment
into the implication, precomposing the hypothesis with each future
stage; **uncurrying** reads it back out by evaluating the implication at
the identity.

```agda
⇒ᵢ-curry : ∀ {c} (R S T : Sieve C c) → (R ∧ᵢ S) ⊆ T → R ⊆ (S ⇒ᵢ T)
⇒ᵢ-curry R S T adj h hR = inc λ g sg → adj (h Cr.∘ g) (R .closed hR g , sg)

⇒ᵢ-uncurry : ∀ {c} (R S T : Sieve C c) → R ⊆ (S ⇒ᵢ T) → (R ∧ᵢ S) ⊆ T
⇒ᵢ-uncurry R S T adj h (hR , hS) =
  subst (_∈ T) (Cr.idr h)
    (□-out! (adj h hR) Cr.id (subst (_∈ S) (sym (Cr.idr h)) hS))
```

## The second brick: universal quantification

The other hereditary connective — and the one Bell's axiom leads with —
is the **universal quantifier**, Lawvere's *right adjoint to
substitution*. Substitution is pullback of sieves, `pullback`{.Agda}
($f^*$); the quantifier $\forall_f$ sends a predicate $T$ over the domain
to the largest predicate over the codomain whose pullback lands in $T$.
Its sieve is the "for all pullback data" formula: an arrow $h$ forces
$\forall_f T$ when, for every future stage $g$ and every lift $k$ across
$f$ — every $k$ with $fk = hg$ — the lift lies in $T$. The same
hereditary shape as implication: a universally-quantified membership,
closed by reassociation. The body quantifies over hom-sets, so — as with
`⇒ᵢ`{.Agda} — `elΩ`{.Agda} resizes it to a truth value.

```agda
∀[_] : ∀ {u v} → Cr.Hom v u → Sieve C v → Sieve C u
(∀[ f ] T) .arrows {y} h =
  elΩ (∀ {z} (g : Cr.Hom z y) (k : Cr.Hom z _) → f Cr.∘ k ≡ h Cr.∘ g → k ∈ T)
(∀[ f ] T) .closed {f = p} hp q = inc λ g k eq →
  □-out! hp (q Cr.∘ g) k (eq ∙ sym (Cr.assoc p q g))
```

And it is genuinely the quantifier: the **adjunction** $f^* R \subseteq
T \Leftrightarrow R \subseteq \forall_f T$, both directions. Forward,
each lift's membership is obtained by precomposing the hypothesis with
the stage and transporting along the lift equation; backward, evaluate at
the identity lift.

```agda
∀[]-adj-→ : ∀ {u v} (f : Cr.Hom v u) (R : Sieve C u) (T : Sieve C v)
  → pullback f R ⊆ T → R ⊆ ∀[ f ] T
∀[]-adj-→ f R T adj h h∈R = inc λ g k eq →
  adj k (subst (_∈ R) (sym eq) (R .closed h∈R g))

∀[]-adj-← : ∀ {u v} (f : Cr.Hom v u) (R : Sieve C u) (T : Sieve C v)
  → R ⊆ ∀[ f ] T → pullback f R ⊆ T
∀[]-adj-← f R T adj k fk∈R =
  □-out! (adj (f Cr.∘ k) fk∈R) Cr.id k (sym (Cr.idr (f Cr.∘ k)))
```

## Both hereditary bricks, in hand

With `_⇒ᵢ_`{.Agda} adjoint to `_∧ᵢ_`{.Agda} and `∀[_]`{.Agda} adjoint to
`pullback`{.Agda} (substitution), the two right-adjoint connectives the
regular fragment lacked — implication and universal quantification — are
now built over sieves, **each with its universal property machine-
checked**. Together with `⊤ᵢ`/`∧ᵢ`/`⋀ᵢ` and the `∃`/`=` already in the
regular doctrine, this is the full first-order signature of the internal
logic of any presheaf topos, at the semantic level of the subobject
classifier — including over the smooth site $\rm{ThCartSp}$.

What remains is packaging, not new ideas: assembling `∀[_]`{.Agda} and
the Heyting fibres into a **first-order hyperdoctrine** extending
`Regular-hyperdoctrine`{.Agda} (whose `∃`, `∧`, `=` are done), and
extending `Cat.Displayed.Doctrine`'s `Formula`{.Agda} grammar and its
soundness proof with the two new connectives. With `∀` and `⇒` present,
Bell's Microaffineness $\forall(g : \Delta \to R)\,\exists!\,b\,
\forall\varepsilon\,\dots$ becomes a formula the doctrine can interpret
and *force* over the smooth site — completing the internalization that
the abstract `Physics.SmoothWorld`{.Agda} and the grounded
`Physics.SmoothWorld.Internal`{.Agda} pointed toward.
