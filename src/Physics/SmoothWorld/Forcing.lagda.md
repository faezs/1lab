<!--
```agda
open import Cat.Prelude

open import Cat.Diagram.Sieve
```
-->

```agda
module Physics.SmoothWorld.Forcing {ℓ} (C : Precategory ℓ ℓ) where
```

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

## The wall, concretely

That is the whole of what computes. There is no operation on sieves —
in `Cat.Diagram.Sieve`{.Agda} or anywhere — for internal
**implication** $\Rightarrow$, **universal quantification** $\forall$,
or **disjunction** $\vee$. Semantically these exist (sieves on an object
form a frame, a complete Heyting algebra), but they are *unbuilt*: the
implication $(S \Rightarrow T)(c)$ would send $c$ to the sieve
$\{\,f : d \to c \mid \forall (g : e \to d),\; fg \in S \Rightarrow fg
\in T\,\}$ — the very "for all future stages $g$" that makes
$\Rightarrow$ and $\forall$ the *hereditary*, right-adjoint connectives,
and that the regular fragment (needing only the left adjoint $\exists$
and finite meets) deliberately avoids.

So the internal logic one can *run* today is exactly $\{\top, \wedge,
\bigwedge, \exists, =\}$ — enough to state that a plot lies in a
subobject, or that two plots agree, or an existential; not enough to
state Bell's Microaffineness $\forall(g : \Delta \to R)\, \exists!\,b\,
\forall\varepsilon\,\dots$, whose $\forall$ and $\exists!$ (an
$\exists$ with a $\forall\dots\Rightarrow$ uniqueness clause) fall
outside it. The missing sieve-level $\Rightarrow$/$\forall$ — equivalently
the Heyting completion of the sieve frame and the right adjoint to
substitution — is the first concrete thing the first-order layer must
supply, and it is exactly what one would build next.
