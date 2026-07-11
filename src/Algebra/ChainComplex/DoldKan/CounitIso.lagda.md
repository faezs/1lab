<!--
```agda
open import Cat.Instances.Simplex.Factorisation
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.Simplex.Classify
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Adjoint
open import Cat.Functor.Compose

open import Algebra.ChainComplex.DoldKan.Normalization
open import Algebra.ChainComplex.DoldKan.Fundamental
open import Algebra.ChainComplex.DoldKan.Operator
open import Algebra.ChainComplex.DoldKan.Boundary
open import Algebra.ChainComplex.DoldKan.Counit
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin
open import Data.Sum

import Algebra.ChainComplex.Moore
import Cat.Reasoning
import Data.Nat as Nat

open Chain-complex
open Chain-map
open Functor
open _=>_
open _⊣_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.CounitIso where
```

# Towards the counit isomorphism

The [[Dold–Kan counit|dold-kan]] evaluates a normalized simplicial
map at the fundamental class. To see that this is an isomorphism we
corestrict the [[normalization operator|moore-complex]] to the
Moore subgroup — its image is normalized by construction — and use
it to reduce every question about a chain map's values to its
values on free generators, where the [[classification of
operators|kahler-differentials]] takes over.

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
```
-->

## Corestricting the operator

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  private
    module Ab' = Precategory (Ab lzero)
    module Nsub (n : Nat) =
      Abelian-group-on (MC.Moore G .ob n .snd)

  Tsub : (j : Nat) → Ab'.Hom (G.₀ j) (MC.Moore G .ob j)
  Tsub zero .∫Hom.fst x = x , lift tt
  Tsub zero .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G 0) refl
  Tsub (suc zero) .∫Hom.fst x =
    T₁ G .∫Hom.fst x , λ i → T₁-normalized G x i
  Tsub (suc zero) .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G 1)
      (is-group-hom.pres-⋆ (T₁ G .∫Hom.snd) x y)
  Tsub (suc (suc m₀)) .∫Hom.fst x =
      T-op G .∫Hom.fst x
    , λ i → T-normalized G x (fsuc i) (Nat.s≤s Nat.0≤x)
  Tsub (suc (suc m₀)) .∫Hom.snd .is-group-hom.pres-⋆ x y =
    Σ-prop-path (MC.norm-is-prop G (suc (suc m₀)))
      (is-group-hom.pres-⋆ (T-op G .∫Hom.snd) x y)
```

On elements that are already normalized — in particular on the
Moore subgroup itself — the corestriction is the identity.

```agda
  Tsub-fix
    : (j : Nat) (x : ⌞ MC.Moore G .ob j ⌟)
    → Tsub j .∫Hom.fst (x .fst) ≡ x
  Tsub-fix zero x = Σ-prop-path (MC.norm-is-prop G 0) refl
  Tsub-fix (suc zero) x = Σ-prop-path (MC.norm-is-prop G 1)
    (T₁-fix G (x .fst) (x .snd))
  Tsub-fix (suc (suc m₀)) x =
    Σ-prop-path (MC.norm-is-prop G (suc (suc m₀)))
      (T-fix G (x .fst) ge-form)
    where
    ge-form : ∀ i → 1 Nat.≤ i .lower
            → d i (x .fst) ≡ Gr.1g (suc m₀)
    ge-form i ge =
        ap (λ w → d w (x .fst))
          (fin-ap {n = λ _ → suc (suc (suc m₀))}
            {x = i} {y = fsuc (pred-eq .fst)}
            (pred-eq .snd))
      ∙ x .snd (pred-eq .fst)
      where
      pred-eq : Σ[ i₁ ∈ Fin (suc (suc m₀)) ]
                  (i .lower ≡ suc (i₁ .lower))
      pred-eq = go (i .lower) refl ge (i .Fin.bounded)
        where
        go : (l : Nat) → l ≡ i .lower → 1 Nat.≤ l
           → suc (i .lower) Nat.≤ suc (suc (suc m₀))
           → Σ[ i₁ ∈ Fin (suc (suc m₀)) ]
               (i .lower ≡ suc (i₁ .lower))
        go zero p ge' bd = absurd (Nat.¬suc≤0 ge')
        go (suc l) p ge' bd =
            fin l ⦃ Nat.≤-peel (subst (λ z → suc z Nat.≤ suc (suc (suc m₀))) (sym p) bd) ⦄
          , sym p
```

## Generators under the operator

Over the linearised standard simplices the classification bites: a
generator with an adjacent collision is degenerate, so the operator
kills it, and a generator missing a positive value is a pushforward
along the corresponding coface, with which the operator commutes.

<!--
```agda
private
  adj : Free-abelian-functor {lzero} ⊣ Ab↪Sets
  adj = Free-abelian⊣Forget

  gen : {T : Set lzero} → ⌞ T ⌟ → ⌞ Free-abelian-functor .F₀ T ⌟
  gen {T} = adj .unit .η T

  gen-natural
    : (T T' : Set lzero) (f : ⌞ T ⌟ → ⌞ T' ⌟) (x : ⌞ T ⌟)
    → Free-abelian-functor .F₁ {T} {T'} f .fst (gen {T} x)
    ≡ gen {T'} (f x)
  gen-natural T T' f x = sym (happly (adj .unit .is-natural T T' f) x)

  free-ext
    : (T : Set lzero) (B : Abelian-group lzero)
      {f g : Ab lzero .Precategory.Hom (Free-abelian-functor .F₀ T) B}
    → (∀ x → f .∫Hom.fst (gen {T} x) ≡ g .∫Hom.fst (gen {T} x))
    → f ≡ g
  free-ext T B p = Equiv.injective
    (_ , L-adjunct-is-equiv adj {a = T} {b = B}) (funext p)

  T₁-natural
    : {G G' : Functor (Δ ^op) (Ab lzero)} (nt : G => G')
    → (x : ⌞ G .F₀ 1 ⌟)
    → nt .η 1 .∫Hom.fst (T₁ G .∫Hom.fst x)
    ≡ T₁ G' .∫Hom.fst (nt .η 1 .∫Hom.fst x)
  T₁-natural {G} {G'} nt x =
      is-group-hom.pres-⋆ (nt .η 1 .∫Hom.snd) x _
    ∙ ap (G1'._*_ (nt .η 1 .∫Hom.fst x))
        ( is-group-hom.pres-inv (nt .η 1 .∫Hom.snd)
        ∙ ap G1'._⁻¹
            ( happly (ap ∫Hom.fst (nt .is-natural 0 1 (σ fzero)))
                (G .F₁ (δ (fsuc fzero)) .∫Hom.fst x)
            ∙ ap (G' .F₁ (σ fzero) .∫Hom.fst)
                (happly (ap ∫Hom.fst (nt .is-natural 1 0 (δ (fsuc fzero)))) x)))
    where
    module G1' = Abelian-group-on (G' .F₀ 1 .snd)
```
-->

```agda
module _ (k : Nat) where
  private
    Gk : Functor (Δ ^op) (Ab lzero)
    Gk = ℤ⟨ Δ[ k ] ⟩

    module Nk (n : Nat) =
      Abelian-group-on (MC.Moore Gk .ob n .snd)

  open Simplicial-operators Gk

  genΔ : {j : Nat} → Δ-map j k → ⌞ Gk .F₀ j ⌟
  genΔ {j} α = gen {Δ[ k ] .F₀ j} α

  private
    module CK {j' : Nat} (α : Δ-map (suc j') k) (t : Fin (suc j'))
              (coll : α .Δ-map.map (weaken t) ≡ α .Δ-map.map (fsuc t))
      where
      γ : Δ-map j' k
      γ = collision-factor α t coll .fst

      path1 : s t (genΔ γ) ≡ genΔ α
      path1 =
          gen-natural (Δ[ k ] .F₀ j') (Δ[ k ] .F₀ (suc j'))
            (Δ[ k ] .F₁ (σ t)) γ
        ∙ ap (gen {Δ[ k ] .F₀ (suc j')})
            (collision-factor α t coll .snd)

      rep : Deg Gk {j'} (t .lower) (genΔ α)
      rep = subst (Deg Gk {j'} (t .lower)) path1
        (deg-single Gk (t .lower) (t .Fin.bounded) (genΔ γ))

  collision-kill
    : {j' : Nat} (α : Δ-map (suc j') k) (t : Fin (suc j'))
    → (coll : α .Δ-map.map (weaken t) ≡ α .Δ-map.map (fsuc t))
    → Tsub Gk (suc j') .∫Hom.fst (genΔ α) ≡ Nk.1g (suc j')
  collision-kill {zero} α t coll =
    Σ-prop-path (MC.norm-is-prop Gk 1)
      (T₁-kill Gk (genΔ α) (t .lower) (CK.rep α t coll))
  collision-kill {suc m₀} α t coll =
    Σ-prop-path (MC.norm-is-prop Gk (suc (suc m₀)))
      (T-kill Gk (genΔ α) (t .lower) (CK.rep α t coll))
```

A generator missing a positive value is the pushforward, along the
coface skipping that value, of the corresponding generator one
dimension down — and the operator commutes with pushforwards, being
natural in the simplicial group.

```agda
module _ (k' : Nat) where
  private
    Gk : Functor (Δ ^op) (Ab lzero)
    Gk = ℤ⟨ Δ[ suc k' ] ⟩

    G' : Functor (Δ ^op) (Ab lzero)
    G' = ℤ⟨ Δ[ k' ] ⟩

  push-Tsub
    : {j : Nat} (α : Δ-map j (suc k')) (i' : Fin (suc k'))
    → (miss : ∀ x → ¬ (α .Δ-map.map x ≡ fsuc i'))
    → Tsub Gk j .∫Hom.fst (genΔ (suc k') α)
    ≡ NΔ-map (δ (fsuc i')) .map j .∫Hom.fst
        (Tsub G' j .∫Hom.fst (genΔ k' (miss-factor α (fsuc i') miss .fst)))
  push-Tsub {j} α i' miss =
    Σ-prop-path (MC.norm-is-prop Gk j) raw-path
    where
    β : Δ-map j k'
    β = miss-factor α (fsuc i') miss .fst

    pushα : G' => Gk
    pushα = Free-abelian-functor ▸ Δmap-nt (δ (fsuc i'))

    gen-push : pushα .η j .∫Hom.fst (genΔ k' β) ≡ genΔ (suc k') α
    gen-push =
        gen-natural (Δ[ k' ] .F₀ j) (Δ[ suc k' ] .F₀ j)
          (Δmap-nt (δ (fsuc i')) .η j) β
      ∙ ap (gen {Δ[ suc k' ] .F₀ j})
          (miss-factor α (fsuc i') miss .snd)

    nat-raw
      : (v : ⌞ G' .F₀ j ⌟)
      → pushα .η j .∫Hom.fst (Tsub G' j .∫Hom.fst v .fst)
      ≡ Tsub Gk j .∫Hom.fst (pushα .η j .∫Hom.fst v) .fst
    nat-raw v = go j v where
      go : (j : Nat) (v : ⌞ G' .F₀ j ⌟)
         → pushα .η j .∫Hom.fst (Tsub G' j .∫Hom.fst v .fst)
         ≡ Tsub Gk j .∫Hom.fst (pushα .η j .∫Hom.fst v) .fst
      go zero v = refl
      go (suc zero) v = T₁-natural pushα v
      go (suc (suc m₀)) v =
          ap (pushα .η (suc (suc m₀)) .∫Hom.fst)
            (T-desc-agree G' (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) v)
        ∙ normalize-desc-natural pushα (suc (suc m₀)) 1 refl
            (Nat.s≤s Nat.0≤x) v
        ∙ sym (T-desc-agree Gk (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x)
            (pushα .η (suc (suc m₀)) .∫Hom.fst v))

    raw-path
      : Tsub Gk j .∫Hom.fst (genΔ (suc k') α) .fst
      ≡ NΔ-map (δ (fsuc i')) .map j .∫Hom.fst
          (Tsub G' j .∫Hom.fst (genΔ k' β)) .fst
    raw-path =
        ap (λ w → Tsub Gk j .∫Hom.fst w .fst) (sym gen-push)
      ∙ sym (nat-raw (genΔ k' β))
```
