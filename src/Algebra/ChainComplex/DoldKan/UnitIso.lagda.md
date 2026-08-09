<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Naturality

open import Algebra.ChainComplex.DoldKan.Normalization
open import Algebra.ChainComplex.DoldKan.CounitIso
open import Algebra.ChainComplex.DoldKan.Unit
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin

import Algebra.ChainComplex.Moore
import Cat.Reasoning
import Data.Nat as Nat

open Chain-complex
open Chain-map
open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.UnitIso where
```

# The unit is an isomorphism

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
  module ChC = Cat.Reasoning (Ch lzero)
```
-->

## The Moore functor reflects isomorphisms

If the Moore image of a simplicial map is invertible, the map
itself is: injectivity because an element with trivial image has
all faces trivial by induction, hence is normalized and seen by the
Moore level; surjectivity because a target splits into its
normalized part — hit through the Moore inverse — and a degenerate
part, hit by induction one level down through the degeneracies.

```agda
module _ {A B : Functor (Δ ^op) (Ab lzero)} (f : A => B)
         (Nf-inv : ChC.is-invertible (moore-map f))
  where
  private
    module A' = Functor A
    module B' = Functor B
    module An (n : Nat) = Abelian-group-on (A'.₀ n .snd)
    module Bn (n : Nat) = Abelian-group-on (B'.₀ n .snd)

    gC : Chain-map (MC.Moore B) (MC.Moore A)
    gC = Nf-inv .ChC.is-invertible.inv

    invl-pt
      : (n : Nat) (yp : ⌞ MC.Moore B .ob n ⌟)
      → moore-map f .map n .∫Hom.fst (gC .map n .∫Hom.fst yp) ≡ yp
    invl-pt n yp = ap (λ w → w .map n .∫Hom.fst yp)
      (Nf-inv .ChC.is-invertible.inverses .ChC.Inverses.invl)

    invr-pt
      : (n : Nat) (xp : ⌞ MC.Moore A .ob n ⌟)
      → gC .map n .∫Hom.fst (moore-map f .map n .∫Hom.fst xp) ≡ xp
    invr-pt n xp = ap (λ w → w .map n .∫Hom.fst xp)
      (Nf-inv .ChC.is-invertible.inverses .ChC.Inverses.invr)

  moore-reflects-inj
    : (n : Nat) (a : ⌞ A'.₀ n ⌟)
    → f .η n .∫Hom.fst a ≡ Bn.1g n → a ≡ An.1g n
  moore-reflects-inj zero a e = ap fst
    ( sym (invr-pt 0 (a , lift tt))
    ∙ ap (gC .map 0 .∫Hom.fst)
        (Σ-prop-path (MC.norm-is-prop B 0) e)
    ∙ is-group-hom.pres-id (gC .map 0 .∫Hom.snd))
  moore-reflects-inj (suc n) a e = a≡Ta ∙ Ta≡1
    where
    faces
      : (i : Fin (suc (suc n)))
      → A'.₁ (δ i) .∫Hom.fst a ≡ An.1g n
    faces i = moore-reflects-inj n (A'.₁ (δ i) .∫Hom.fst a)
      ( happly (ap ∫Hom.fst (f .is-natural (suc n) n (δ i))) a
      ∙ ap (B'.₁ (δ i) .∫Hom.fst) e
      ∙ is-group-hom.pres-id (B'.₁ (δ i) .∫Hom.snd))

    p : (i : Fin (suc n)) → A'.₁ (δ (fsuc i)) .∫Hom.fst a ≡ An.1g n
    p i = faces (fsuc i)

    a≡Ta : a ≡ Tsub A (suc n) .∫Hom.fst a .fst
    a≡Ta = sym (ap fst (Tsub-fix A (suc n) (a , p)))

    NfTa≡1
      : moore-map f .map (suc n) .∫Hom.fst
          (Tsub A (suc n) .∫Hom.fst a)
      ≡ Abelian-group-on.1g (MC.Moore B .ob (suc n) .snd)
    NfTa≡1 = Σ-prop-path (MC.norm-is-prop B (suc n))
      ( Tsub-natural f (suc n) a
      ∙ ap (λ v → Tsub B (suc n) .∫Hom.fst v .fst) e
      ∙ ap fst (is-group-hom.pres-id (Tsub B (suc n) .∫Hom.snd)))

    Ta≡1 : Tsub A (suc n) .∫Hom.fst a .fst ≡ An.1g (suc n)
    Ta≡1 = ap fst
      ( sym (invr-pt (suc n) (Tsub A (suc n) .∫Hom.fst a))
      ∙ ap (gC .map (suc n) .∫Hom.fst) NfTa≡1
      ∙ is-group-hom.pres-id (gC .map (suc n) .∫Hom.snd))

  moore-reflects-surj
    : (n : Nat) (b : ⌞ B'.₀ n ⌟)
    → Σ[ a ∈ ⌞ A'.₀ n ⌟ ] (f .η n .∫Hom.fst a ≡ b)
  moore-reflects-surj zero b =
      gC .map 0 .∫Hom.fst (b , lift tt) .fst
    , ap fst (invl-pt 0 (b , lift tt))
  moore-reflects-surj (suc n) b = a-total , fa-path
    where
    Tb : ⌞ MC.Moore B .ob (suc n) ⌟
    Tb = Tsub B (suc n) .∫Hom.fst b

    a-norm : ⌞ MC.Moore A .ob (suc n) ⌟
    a-norm = gC .map (suc n) .∫Hom.fst Tb

    fa-norm : f .η (suc n) .∫Hom.fst (a-norm .fst) ≡ Tb .fst
    fa-norm = ap fst (invl-pt (suc n) Tb)

    D-elt : ⌞ B'.₀ (suc n) ⌟
    D-elt = Bn._*_ (suc n) b (Bn._⁻¹ (suc n) (Tb .fst))

    deg-pre
      : (j : Nat) (v : ⌞ B'.₀ (suc n) ⌟) → Deg B {n} j v
      → Σ[ u ∈ ⌞ A'.₀ (suc n) ⌟ ] (f .η (suc n) .∫Hom.fst u ≡ v)
    deg-pre zero v (y , q) =
        A'.₁ (σ fzero) .∫Hom.fst (moore-reflects-surj n y .fst)
      , ( happly (ap ∫Hom.fst (f .is-natural n (suc n) (σ fzero)))
            (moore-reflects-surj n y .fst)
        ∙ ap (B'.₁ (σ fzero) .∫Hom.fst) (moore-reflects-surj n y .snd)
        ∙ sym q)
    deg-pre (suc j) v (b₀ , y , x' , rep' , q) =
        An._*_ (suc n) (deg-pre j x' rep' .fst)
          (A'.₁ (σ (fin (suc j) ⦃ b₀ ⦄)) .∫Hom.fst
            (moore-reflects-surj n y .fst))
      , ( is-group-hom.pres-⋆ (f .η (suc n) .∫Hom.snd) _ _
        ∙ ap₂ (Bn._*_ (suc n))
            (deg-pre j x' rep' .snd)
            ( happly (ap ∫Hom.fst
                  (f .is-natural n (suc n) (σ (fin (suc j) ⦃ b₀ ⦄))))
                (moore-reflects-surj n y .fst)
            ∙ ap (B'.₁ (σ (fin (suc j) ⦃ b₀ ⦄)) .∫Hom.fst)
                (moore-reflects-surj n y .snd))
        ∙ sym q)

    a-total : ⌞ A'.₀ (suc n) ⌟
    a-total = An._*_ (suc n) (a-norm .fst)
      (deg-pre n D-elt (Tsub-diff B n b) .fst)

    fa-path : f .η (suc n) .∫Hom.fst a-total ≡ b
    fa-path =
        is-group-hom.pres-⋆ (f .η (suc n) .∫Hom.snd) _ _
      ∙ ap₂ (Bn._*_ (suc n)) fa-norm
          (deg-pre n D-elt (Tsub-diff B n b) .snd)
      ∙ ap (Bn._*_ (suc n) (Tb .fst))
          (Bn.commutes (suc n) {x = b} {y = Bn._⁻¹ (suc n) (Tb .fst)})
      ∙ Bn.associative (suc n)
          {x = Tb .fst} {y = Bn._⁻¹ (suc n) (Tb .fst)} {z = b}
      ∙ ap (λ z → Bn._*_ (suc n) z b)
          (Bn.inverser (suc n) {x = Tb .fst})
      ∙ Bn.idl (suc n) {x = b}
```

## The unit is an isomorphism

Applying the reflection to the unit itself — whose Moore image is
invertible by the triangle — makes the unit a natural isomorphism.
**Both comparison maps of the Dold–Kan correspondence are
isomorphisms.**

```agda
module _ (A : Functor (Δ ^op) (Ab lzero)) where
  private
    module A' = Functor A
    module ΓA (n : Nat) =
      Abelian-group-on (Γ (MC.Moore A) .F₀ n .snd)

    η-inj = moore-reflects-inj (dk-unit A) (Nη-invertible A)
    η-surj = moore-reflects-surj (dk-unit A) (Nη-invertible A)

    η-inj'
      : (n : Nat) (u v : ⌞ A'.₀ n ⌟)
      → dk-unit A .η n .∫Hom.fst u ≡ dk-unit A .η n .∫Hom.fst v
      → u ≡ v
    η-inj' n u v e =
        sym (An.idr n {x = u})
      ∙ ap (An._*_ n u) (sym (An.inversel n {x = v}))
      ∙ An.associative n {x = u} {y = An._⁻¹ n v} {z = v}
      ∙ ap (λ z → An._*_ n z v) diff-kill
      ∙ An.idl n {x = v}
      where
      module An (n : Nat) = Abelian-group-on (A'.₀ n .snd)

      diff-kill : An._*_ n u (An._⁻¹ n v) ≡ An.1g n
      diff-kill = η-inj n (An._*_ n u (An._⁻¹ n v))
        ( is-group-hom.pres-⋆ (dk-unit A .η n .∫Hom.snd) u (An._⁻¹ n v)
        ∙ ap₂ (ΓA._*_ n)
            e
            (is-group-hom.pres-inv (dk-unit A .η n .∫Hom.snd) {x = v})
        ∙ ΓA.inverser n {x = dk-unit A .η n .∫Hom.fst v})

    inv-hom
      : (n : Nat)
      → Ab lzero .Precategory.Hom (Γ (MC.Moore A) .F₀ n) (A'.₀ n)
    inv-hom n .∫Hom.fst φ = η-surj n φ .fst
    inv-hom n .∫Hom.snd .is-group-hom.pres-⋆ φ ψ = η-inj' n _ _
      ( η-surj n (ΓA._*_ n φ ψ) .snd
      ∙ sym ( is-group-hom.pres-⋆ (dk-unit A .η n .∫Hom.snd) _ _
            ∙ ap₂ (ΓA._*_ n) (η-surj n φ .snd) (η-surj n ψ .snd)))

  dk-unit-iso : A ≅ⁿ Γ (MC.Moore A)
  dk-unit-iso = to-natural-iso mk
    where
    mk : make-natural-iso A (Γ (MC.Moore A))
    mk .make-natural-iso.eta n = dk-unit A .η n
    mk .make-natural-iso.inv n = inv-hom n
    mk .make-natural-iso.eta∘inv n = ext λ φ → η-surj n φ .snd
    mk .make-natural-iso.inv∘eta n = ext λ a → η-inj' n _ _
      (η-surj n (dk-unit A .η n .∫Hom.fst a) .snd)
    mk .make-natural-iso.natural x y g =
      sym (dk-unit A .is-natural x y g)
```
