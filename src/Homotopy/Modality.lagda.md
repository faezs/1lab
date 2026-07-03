<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Truncation

open is-iso
```
-->

```agda
module Homotopy.Modality where
```

# Modalities {defines="modality reflective-subuniverse modal-type lex-modality"}

In a homotopy type theory — whose types are, semantically, the
objects of an ∞-topos — a **modality** is the internal incarnation
of a *reflective sub-∞-topos*: an idempotent monad $\bigcirc$ on the
universe, equipped with enough elimination structure to reflect
every type into its subuniverse of **modal types**. This is the
theory of Rijke, Shulman and Spitters [@RSS:Modalities]. Following
them, we package a modality as a reflection operator and unit, an
elimination rule into $\bigcirc$-ed families, and the requirement
that path types of reflected types are themselves modal — from
which the full universal property, idempotence, and closure of the
modal types under identity and $\Sigma$ are all *theorems*.

```agda
record Modality ℓ : Type (lsuc ℓ) where
  no-eta-equality
  field
    ○_ : Type ℓ → Type ℓ
    η  : {A : Type ℓ} → A → ○ A

    ○-elim
      : {A : Type ℓ} {B : ○ A → Type ℓ}
      → ((a : A) → ○ (B (η a)))
      → (x : ○ A) → ○ (B x)

    ○-elim-β
      : {A : Type ℓ} {B : ○ A → Type ℓ}
      → (f : (a : A) → ○ (B (η a))) (a : A)
      → ○-elim {B = B} f (η a) ≡ f a

    ≡-modal
      : {A : Type ℓ} {x y : ○ A} → is-equiv (η {x ≡ y})
```

A type is **modal** when its unit is an equivalence: it already
lives in the subuniverse. Being modal is a proposition, so the
modal types form a genuine subuniverse.

```agda
  is-modal : Type ℓ → Type ℓ
  is-modal A = is-equiv (η {A})

  is-modal-is-prop : (A : Type ℓ) → is-prop (is-modal A)
  is-modal-is-prop A = is-equiv-is-prop η
```

<!--
```agda
  private variable
    A B : Type ℓ

  ○-path-out : {x y : ○ A} → ○ (x ≡ y) → x ≡ y
  ○-path-out = equiv→inverse ≡-modal
```
-->

Non-dependent recursion and functoriality are special cases of the
eliminator.

```agda
  ○-rec : (A → ○ B) → ○ A → ○ B
  ○-rec {B = B} f = ○-elim {B = λ _ → B} f

  ○-map : (A → B) → ○ A → ○ B
  ○-map f = ○-rec (λ a → η (f a))
```

## Idempotence

The reflection of any type is modal. The multiplication is
recursion on the identity; that it is inverse to the unit is the
computation rule in one direction, and in the other is proven by
eliminating into the *path* family — which is exactly what the
`≡-modal`{.Agda} axiom licenses. This pattern — a path between
inhabitants of a reflected type may be constructed on units — 
recurs in every proof below.

```agda
  ○-modal : is-modal (○ A)
  ○-modal {A} = is-iso→is-equiv λ where
      .from → μ
      .linv → μ-η
      .rinv x → ○-path-out
        (○-elim {B = λ x → η (μ x) ≡ x} (λ a → η (ap η (μ-η a))) x)
    where
      μ : ○ (○ A) → ○ A
      μ = ○-rec (λ x → x)

      μ-η : ∀ x → μ (η x) ≡ x
      μ-η = ○-elim-β {B = λ _ → A} (λ x → x)
```

## The universal property

Eliminating into a family of *modal* types — rather than a family
of reflections — is where the subuniverse's universal property
lives: any map out of $A$ into a modal family extends along the
unit.

```agda
  ○-elim-modal
    : {B : ○ A → Type ℓ}
    → (bm : ∀ x → is-modal (B x))
    → ((a : A) → B (η a))
    → (x : ○ A) → B x
  ○-elim-modal {B = B} bm f x =
    equiv→inverse (bm x) (○-elim {B = B} (λ a → η (f a)) x)

  ○-elim-modal-β
    : {B : ○ A → Type ℓ}
    → (bm : ∀ x → is-modal (B x)) (f : (a : A) → B (η a))
    → ∀ a → ○-elim-modal bm f (η a) ≡ f a
  ○-elim-modal-β {B = B} bm f a =
      ap (equiv→inverse (bm (η a))) (○-elim-β (λ a → η (f a)) a)
    ∙ equiv→unit (bm (η a)) (f a)
```

## Closure properties

Modal types are closed under identity: paths between points of a
modal type are again modal. The inverse to the unit goes through
the injectivity of the (equivalence) unit of $A$, and the triangle
identity is naturality of the unit-inverse homotopy.

```agda
  modal-identity
    : is-modal A → {x y : A} → is-modal (x ≡ y)
  modal-identity {A} m {x} {y} = is-iso→is-equiv λ where
      .from → ν
      .linv → ν-η
      .rinv w → ○-path-out
        (○-elim {B = λ w → η (ν w) ≡ w} (λ p → η (ap η (ν-η p))) w)
    where
      inv : ○ A → A
      inv = equiv→inverse m

      u : ∀ a → inv (η a) ≡ a
      u = equiv→unit m

      inj : η x ≡ η y → x ≡ y
      inj q = sym (u x) ∙ ap inv q ∙ u y

      ν : ○ (x ≡ y) → x ≡ y
      ν w = inj (○-path-out (○-map (ap η) w))

      inj-η : ∀ (p : x ≡ y) → inj (ap η p) ≡ p
      inj-η p =
          ap (sym (u x) ∙_) (sym (homotopy-natural u p))
        ∙ ∙-assoc (sym (u x)) (u x) p
        ∙ ap (_∙ p) (∙-invl (u x))
        ∙ ∙-idl p

      ν-η : ∀ p → ν (η p) ≡ p
      ν-η p =
          ap (λ w → inj (○-path-out w)) (○-elim-β (λ p → η (ap η p)) p)
        ∙ ap inj (equiv→unit ≡-modal (ap η p))
        ∙ inj-η p
```

They are also closed under $\Sigma$ — the theorem that makes the
modal types a *$\Sigma$-closed* reflective subuniverse, i.e. makes
the reflection a modality in the semantic sense.

```agda
  modal-Σ
    : {B : A → Type ℓ}
    → is-modal A → (∀ a → is-modal (B a))
    → is-modal (Σ A B)
  modal-Σ {A} {B} am bm = is-iso→is-equiv λ where
      .from → g
      .linv → g-η
      .rinv x → ○-path-out
        (○-elim {B = λ x → η (g x) ≡ x} (λ p → η (ap η (g-η p))) x)
    where
      a₀ : ○ (Σ A B) → A
      a₀ = ○-elim-modal (λ _ → am) fst

      a₀-β : ∀ p → a₀ (η p) ≡ p .fst
      a₀-β = ○-elim-modal-β (λ _ → am) fst

      b₀ : ∀ x → B (a₀ x)
      b₀ = ○-elim-modal (λ x → bm (a₀ x))
        (λ p → subst B (sym (a₀-β p)) (p .snd))

      b₀-β : ∀ p → b₀ (η p) ≡ subst B (sym (a₀-β p)) (p .snd)
      b₀-β = ○-elim-modal-β (λ x → bm (a₀ x))
        (λ p → subst B (sym (a₀-β p)) (p .snd))

      g : ○ (Σ A B) → Σ A B
      g x = a₀ x , b₀ x

      g-η : ∀ p → g (η p) ≡ p
      g-η p = Σ-pathp (a₀-β p) $ to-pathp $
          ap (subst B (a₀-β p)) (b₀-β p)
        ∙ transport⁻transport (ap B (sym (a₀-β p))) (p .snd)

  modal-× : is-modal A → is-modal B → is-modal (A × B)
  modal-× am bm = modal-Σ am (λ _ → bm)
```

## Left exactness

A modality is **left exact** when it preserves path spaces: the
canonical comparison from the reflection of a path type to paths in
the reflection is an equivalence. Semantically, the (accessible)
lex modalities are exactly the reflections onto **sub-∞-topoi**:
left exactness of the reflector is what makes the reflective
subuniverse a topos rather than a mere localisation.

```agda
  ○-ap : {x y : A} → ○ (x ≡ y) → η x ≡ η y
  ○-ap = ○-path-out ∘ ○-map (ap η)

record is-lex {ℓ} (M : Modality ℓ) : Type (lsuc ℓ) where
  open Modality M
  field
    lex : {A : Type ℓ} {x y : A} → is-equiv (○-ap {A = A} {x} {y})
```

## The truncation modalities

The $n$-truncations are modalities — the tower of reflections
presenting, internally, the tower of $n$-topoi inside the ambient
∞-topos. Their modal types are the $n$-types. They are the
canonical *non*-lex examples: truncation destroys precisely the
identifications a lex reflector would have to preserve.

```agda
private
  inc-is-equiv
    : ∀ {ℓ} {A : Type ℓ} {n}
    → is-hlevel A (suc n) → is-equiv (inc {A = A} {n = suc n})
  inc-is-equiv {A = A} {n} hl = is-iso→is-equiv λ where
    .from   → n-Tr-rec hl (λ a → a)
    .linv a → refl
    .rinv   → n-Tr-elim _
      (λ x → Path-is-hlevel (suc n) (n-Tr-is-hlevel n))
      (λ a → refl)

Truncation : ∀ {ℓ} (n : Nat) → Modality ℓ
Truncation n .Modality.○_ A = n-Tr A (suc n)
Truncation n .Modality.η = inc
Truncation n .Modality.○-elim {B = B} f =
  n-Tr-elim _ (λ x → n-Tr-is-hlevel n) f
Truncation n .Modality.○-elim-β f a = refl
Truncation n .Modality.≡-modal =
  inc-is-equiv (Path-is-hlevel (suc n) (n-Tr-is-hlevel n))
```

At $n = 0$ this is (up to the usual reindexing) the propositional
truncation, reflecting onto the subuniverse of propositions: the
(0,1)-topos inside the ∞-topos, internally.

## The open modality

For a proposition $P$, the exponential $A \mapsto (P \to A)$ is a
modality, and a *left exact* one: it presents the **open
sub-∞-topos** determined by the open $P$ of the terminal object.
All the structure is inherited pointwise, using that any two proofs
of $P$ are identified.

```agda
Open : ∀ {ℓ} (P : Type ℓ) → is-prop P → Modality ℓ
Open P pprop .Modality.○_ A = P → A
Open P pprop .Modality.η a _ = a
Open P pprop .Modality.○-elim {A} {B} f x p =
  transport (λ i → B (fix p i)) (f (x p) p)
  where
    fix : ∀ p → Path (P → A) (λ _ → x p) x
    fix p i p' = x (pprop p p' i)
Open P pprop .Modality.○-elim-β {A} {B} f a = funext λ p →
  transport-refl (f a p)
Open P pprop .Modality.≡-modal {A} {x} {y} = is-iso→is-equiv λ where
    .from h → funext λ p → happly (h p) p
    .linv q → refl
    .rinv h → funext λ p →
      ap funext (funext λ p' →
        ap (λ w → happly (h w) p') (pprop p' p))
```

Left exactness: a path between constant functions out of $P$ is the
same thing as a $P$-indexed family of paths, which is what the
reflection of the path type already is. The comparison map agrees
with this evident equivalence.

```agda
Open-is-lex
  : ∀ {ℓ} (P : Type ℓ) (pprop : is-prop P) → is-lex (Open P pprop)
Open-is-lex P pprop .is-lex.lex {A} {x} {y} =
  subst is-equiv (sym (funext ○-ap≡e)) e-is-equiv
  where
    module O = Modality (Open P pprop)

    e : (P → x ≡ y) → Path (P → A) (λ _ → x) (λ _ → y)
    e w i p = w p i

    e-is-equiv : is-equiv e
    e-is-equiv = is-iso→is-equiv λ where
      .from q p i → q i p
      .linv w → refl
      .rinv q → refl

    square : ∀ (w : P → x ≡ y) p → e w ≡ ap O.η (w p)
    square w p j i p' = w (pprop p' p j) i

    ○-ap≡e : ∀ w → O.○-ap w ≡ e w
    ○-ap≡e w =
        ap O.○-path-out (sym unit-path)
      ∙ equiv→unit O.≡-modal (e w)
      where
        unit-path : O.η (e w) ≡ O.○-map (ap O.η) w
        unit-path = funext λ p →
          square w p ∙ sym (transport-refl (ap O.η (w p)))
```

## ∞-topoi, internally

This module is the seed of "∞-topos theory proper" in the 1Lab, in
its *internal* form. The type theory itself is the internal
language of an ∞-topos, with [[univalence]] playing the role of the
object classifier — the descent property by which Rezk and Lurie
*characterise* ∞-topoi among presentable ∞-categories. Reflective
subuniverses and lex modalities are then, internally, the
localisations and sub-∞-topoi of the ambient one: the truncation
tower gives the $n$-topoi, and the open modality above (with its
closed complement) gives the recollement of open and closed
subtopoi. What the internal language does not see is the
*presentation* of a particular gros ∞-topos — constructing the
∞-category of ∞-sheaves on a site by simplicially localising
simplicial presheaves requires external ∞-category theory
(quasicategories, or complete Segal objects), which remains outside
the 1Lab's current scope.
