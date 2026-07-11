<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Displayed.Total
open import Cat.Functor.Hom
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

import Algebra.ChainComplex.Moore
import Cat.Reasoning

open Chain-complex
open Chain-map
open Functor
open _=>_
open _⊣_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Unit where
```

# The Dold–Kan unit

The [[inverse Dold–Kan construction|dold-kan]] presents $\Gamma(C)_n$
as chain maps $N\bZ[\Delta^n] \to C$. This makes the **unit** of the
correspondence essentially formal: an $n$-simplex $a$ of a
simplicial abelian group $A$ has a Yoneda character $\Delta^n \to A$,
which transposes across the free–forget adjunction to a map of
simplicial abelian groups $\bZ[\Delta^n] \to A$; applying the Moore
complex functor gives a chain map $N\bZ[\Delta^n] \to NA$, that is,
an $n$-simplex of $\Gamma(NA)$. Every verification below reduces, by
the injectivity of adjunct transposition, to an evaluation at the
generators.

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
  module ChC = Cat.Reasoning (Ch lzero)

  adj : Free-abelian-functor {lzero} ⊣ Ab↪Sets
  adj = Free-abelian⊣Forget

  gen : {T : Set lzero} → ⌞ T ⌟ → ⌞ Free-abelian-functor .F₀ T ⌟
  gen {T} = adj .unit .η T

  free-ext
    : (T : Set lzero) (B : Abelian-group lzero)
      {f g : Ab lzero .Precategory.Hom (Free-abelian-functor .F₀ T) B}
    → (∀ x → f .fst (gen {T} x) ≡ g .fst (gen {T} x))
    → f ≡ g
  free-ext T B p = Equiv.injective
    (_ , L-adjunct-is-equiv adj {a = T} {b = B}) (funext p)

  ev-gen
    : (T : Set lzero) (B : Abelian-group lzero)
      (f : ⌞ T ⌟ → ⌞ B ⌟) (x : ⌞ T ⌟)
    → R-adjunct adj {a = T} {b = B} f .fst (gen {T} x) ≡ f x
  ev-gen T B f x = happly (L-R-adjunct adj {a = T} {b = B} f) x

  gen-natural
    : (T T' : Set lzero) (f : ⌞ T ⌟ → ⌞ T' ⌟) (x : ⌞ T ⌟)
    → Free-abelian-functor .F₁ {T} {T'} f .fst (gen {T} x) ≡ gen {T'} (f x)
  gen-natural T T' f x = sym (happly (adj .unit .is-natural T T' f) x)
```
-->

## The transposed character

```agda
module _ (A : Functor (Δ ^op) (Ab lzero)) where
  private
    module A = Functor A
    module An (n : Nat) = Abelian-group-on (A.₀ n .snd)

  χ : ∀ {n} → ⌞ A.₀ n ⌟ → Δ[ n ] => (Ab↪Sets F∘ A)
  χ a .η m h = A.₁ h .fst a
  χ a .is-natural m m' g = funext λ h →
    happly (ap ∫Hom.fst (A.F-∘ g h)) a

  â : ∀ {n} → ⌞ A.₀ n ⌟ → ℤ⟨ Δ[ n ] ⟩ => A
  â {n} a .η m = R-adjunct adj {a = Δ[ n ] .F₀ m} {b = A.₀ m} (χ a .η m)
  â {n} a .is-natural m m' g = free-ext (Δ[ n ] .F₀ m) (A.₀ m') λ h →
      ap (â a .η m' .fst) (gen-natural (Δ[ n ] .F₀ m) (Δ[ n ] .F₀ m') (Δ[ n ] .F₁ g) h)
    ∙ ev-gen (Δ[ n ] .F₀ m') (A.₀ m') (χ a .η m') (h ∘Δ g)
    ∙ happly (ap ∫Hom.fst (A.F-∘ g h)) a
    ∙ ap (A.₁ g .fst) (sym (ev-gen (Δ[ n ] .F₀ m) (A.₀ m) (χ a .η m) h))
```

## The unit

```agda
  dk-unit : A => Γ (MC.Moore A)
  dk-unit .η n .fst a = moore-map (â a)
  dk-unit .η n .snd .is-group-hom.pres-⋆ a b =
    Chain-map-path λ k → ext λ x p →
      Σ-prop-path (MC.norm-is-prop A k)
        (happly (ap ∫Hom.fst (add-lemma k)) x)
    where
    add-lemma
      : ∀ k
      → â (An._*_ n a b) .η k
      ≡ Abelian-group-on._*_ (Abelian-group-on-hom (ℤ⟨ Δ[ n ] ⟩ .F₀ k) (A.₀ k))
          (â a .η k) (â b .η k)
    add-lemma k = free-ext (Δ[ n ] .F₀ k) (A.₀ k) λ h →
        ev-gen (Δ[ n ] .F₀ k) (A.₀ k) (χ (An._*_ n a b) .η k) h
      ∙ is-group-hom.pres-⋆ (A.₁ h .snd) a b
      ∙ ap₂ (An._*_ k)
          (sym (ev-gen (Δ[ n ] .F₀ k) (A.₀ k) (χ a .η k) h))
          (sym (ev-gen (Δ[ n ] .F₀ k) (A.₀ k) (χ b .η k) h))
  dk-unit .is-natural n n' g = ext λ a →
      ap moore-map (sym (compose-lemma a))
    ∙ moore-map-∘ (â a) (Free-abelian-functor ▸ Δmap-nt g)
    where
    compose-lemma
      : (a : ⌞ A.₀ n ⌟)
      → â a ∘nt (Free-abelian-functor ▸ Δmap-nt g)
      ≡ â (A.₁ g .fst a)
    compose-lemma a = Nat-path λ k → free-ext (Δ[ n' ] .F₀ k) (A.₀ k)
      {f = (â a ∘nt (Free-abelian-functor ▸ Δmap-nt g)) .η k}
      {g = â (A.₁ g .fst a) .η k}
      λ h →
        ap (â a .η k .fst) (gen-natural (Δ[ n' ] .F₀ k) (Δ[ n ] .F₀ k) (Δmap-nt g .η k) h)
      ∙ ev-gen (Δ[ n ] .F₀ k) (A.₀ k) (χ a .η k) (g ∘Δ h)
      ∙ happly (ap ∫Hom.fst (A.F-∘ h g)) a
      ∙ sym (ev-gen (Δ[ n' ] .F₀ k) (A.₀ k) (χ (A.₁ g .fst a) .η k) h)
```

The unit is the easy half of the Dold–Kan correspondence's data;
that it is an *isomorphism* is proven downstream, from the
normalization operator's fixing of normalized chains and killing of
degenerate ones.
