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

  ev-gen
    : (T : Set lzero) (B : Abelian-group lzero)
      (f : ⌞ T ⌟ → ⌞ B ⌟) (x : ⌞ T ⌟)
    → R-adjunct adj {a = T} {b = B} f .∫Hom.fst (gen {T} x) ≡ f x
  ev-gen T B f x = happly (L-R-adjunct adj {a = T} {b = B} f) x

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

The difference between an element and its corestricted
normalization is degenerate, uniformly in the level.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  private
    module Gm (n : Nat) = Abelian-group-on (G.₀ n .snd)

    inv-distr' : {n : Nat} (x y : ⌞ G.₀ n ⌟)
               → Gm._⁻¹ n (Gm._*_ n x y)
               ≡ Gm._*_ n (Gm._⁻¹ n x) (Gm._⁻¹ n y)
    inv-distr' {n} x y = sym unique
      where
      cancel : Gm._*_ n (Gm._*_ n x y)
                 (Gm._*_ n (Gm._⁻¹ n x) (Gm._⁻¹ n y)) ≡ Gm.1g n
      cancel =
          sym (Gm.associative n)
        ∙ ap (Gm._*_ n x)
            ( Gm.associative n
            ∙ ap (λ z → Gm._*_ n z (Gm._⁻¹ n y)) (Gm.commutes n)
            ∙ sym (Gm.associative n)
            ∙ ap (Gm._*_ n (Gm._⁻¹ n x)) (Gm.inverser n)
            ∙ Gm.idr n)
        ∙ Gm.inverser n
      unique : Gm._*_ n (Gm._⁻¹ n x) (Gm._⁻¹ n y)
             ≡ Gm._⁻¹ n (Gm._*_ n x y)
      unique =
          sym (Gm.idl n)
        ∙ ap (λ z → Gm._*_ n z (Gm._*_ n (Gm._⁻¹ n x) (Gm._⁻¹ n y)))
            (sym (Gm.inversel n))
        ∙ sym (Gm.associative n)
        ∙ ap (Gm._*_ n (Gm._⁻¹ n (Gm._*_ n x y))) cancel
        ∙ Gm.idr n

    inv-inv' : {n : Nat} (x : ⌞ G.₀ n ⌟)
             → Gm._⁻¹ n (Gm._⁻¹ n x) ≡ x
    inv-inv' {n} x =
        sym (Gm.idr n)
      ∙ ap (Gm._*_ n (Gm._⁻¹ n (Gm._⁻¹ n x))) (sym (Gm.inversel n))
      ∙ Gm.associative n
      ∙ ap (λ z → Gm._*_ n z x) (Gm.inversel n)
      ∙ Gm.idl n

  Tsub-diff
    : (m : Nat) (x : ⌞ G.₀ (suc m) ⌟)
    → Deg G {m} m
        (Gm._*_ (suc m) x
          (Gm._⁻¹ (suc m) (Tsub G (suc m) .∫Hom.fst x .fst)))
  Tsub-diff zero x = subst (Deg G {0} 0) (sym path)
    (deg-single G 0 (Nat.s≤s Nat.0≤x) (d (fsuc fzero) x))
    where
    S : ⌞ G.₀ 1 ⌟
    S = s fzero (d (fsuc fzero) x)

    path : Gm._*_ 1 x (Gm._⁻¹ 1 (Gm._*_ 1 x (Gm._⁻¹ 1 S))) ≡ S
    path =
        ap (Gm._*_ 1 x) (inv-distr' x (Gm._⁻¹ 1 S))
      ∙ ap (λ z → Gm._*_ 1 x (Gm._*_ 1 (Gm._⁻¹ 1 x) z)) (inv-inv' S)
      ∙ Gm.associative 1
      ∙ ap (λ z → Gm._*_ 1 z S) (Gm.inverser 1)
      ∙ Gm.idl 1
  Tsub-diff (suc m₀) x =
    T-diff G (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) x
```

The corestriction is natural in the simplicial abelian group, and
sends the generating simplex to the fundamental class.

```agda
Tsub-natural
  : {G G' : Functor (Δ ^op) (Ab lzero)} (nt : G => G')
  → (j : Nat) (v : ⌞ G .F₀ j ⌟)
  → nt .η j .∫Hom.fst (Tsub G j .∫Hom.fst v .fst)
  ≡ Tsub G' j .∫Hom.fst (nt .η j .∫Hom.fst v) .fst
Tsub-natural nt zero v = refl
Tsub-natural nt (suc zero) v = T₁-natural nt v
Tsub-natural {G} {G'} nt (suc (suc m₀)) v =
    ap (nt .η (suc (suc m₀)) .∫Hom.fst)
      (T-desc-agree G (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) v)
  ∙ normalize-desc-natural nt (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x) v
  ∙ sym (T-desc-agree G' (suc (suc m₀)) 1 refl (Nat.s≤s Nat.0≤x)
      (nt .η (suc (suc m₀)) .∫Hom.fst v))

Tsub-id
  : (k : Nat)
  → Tsub ℤ⟨ Δ[ k ] ⟩ k .∫Hom.fst (genΔ k (Δ .Precategory.id))
  ≡ fundamental k
Tsub-id zero = Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ 0 ] ⟩ 0) refl
Tsub-id (suc zero) = Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ 1 ] ⟩ 1) refl
Tsub-id (suc (suc m₀)) =
  Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc (suc m₀) ] ⟩ (suc (suc m₀)))
    (T-desc-agree ℤ⟨ Δ[ suc (suc m₀) ] ⟩ (suc (suc m₀)) 1 refl
      (Nat.s≤s Nat.0≤x) (genΔ (suc (suc m₀)) (Δ .Precategory.id)))
```

## Injectivity of the counit

A normalized simplicial map that vanishes on the fundamental class
vanishes everywhere: reduce any value to values on generators by
the corestriction, then classify the generator. Collisions die by
degeneracy, missed positive values by the normalization field, the
identity by hypothesis — and the bottom coface by the boundary
formula, whose positive terms the normalization field kills and
whose chain square the hypothesis closes.

<!--
```agda
private
  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)

  weaken-lower : ∀ {n} (x : Fin n) → weaken x .lower ≡ x .lower
  weaken-lower x with fin-view x
  ... | zero  = refl
  ... | suc i = ap suc (weaken-lower i)

  Fin1-path : (a b : Fin 1) → a ≡ b
  Fin1-path a b = fin-ap {n = λ _ → 1}
    ( Nat.≤-antisym (Nat.≤-peel (a .Fin.bounded)) Nat.0≤x
    ∙ sym (Nat.≤-antisym (Nat.≤-peel (b .Fin.bounded)) Nat.0≤x))

  zero-hom' : {X Y : Abelian-group lzero} → Ab lzero .Precategory.Hom X Y
  zero-hom' {X} {Y} .∫Hom.fst _ = Abelian-group-on.1g (Y .snd)
  zero-hom' {X} {Y} .∫Hom.snd .is-group-hom.pres-⋆ _ _ =
    sym (Abelian-group-on.idl (Y .snd))
```
-->

<!--
```agda
private
  module AbL (A : Abelian-group lzero) where
    private module M = Abelian-group-on (A .snd)

    ab-inv-distr
      : (x y : ⌞ A ⌟) → M._⁻¹ (M._*_ x y) ≡ M._*_ (M._⁻¹ x) (M._⁻¹ y)
    ab-inv-distr x y = sym unique
      where
      cancel : M._*_ (M._*_ x y) (M._*_ (M._⁻¹ x) (M._⁻¹ y)) ≡ M.1g
      cancel =
          sym (M.associative
            {x = x} {y = y} {z = M._*_ (M._⁻¹ x) (M._⁻¹ y)})
        ∙ ap (M._*_ x)
            ( M.associative {x = y} {y = M._⁻¹ x} {z = M._⁻¹ y}
            ∙ ap (λ z → M._*_ z (M._⁻¹ y))
                (M.commutes {x = y} {y = M._⁻¹ x})
            ∙ sym (M.associative {x = M._⁻¹ x} {y = y} {z = M._⁻¹ y})
            ∙ ap (M._*_ (M._⁻¹ x)) (M.inverser {x = y})
            ∙ M.idr {x = M._⁻¹ x})
        ∙ M.inverser {x = x}
      unique : M._*_ (M._⁻¹ x) (M._⁻¹ y) ≡ M._⁻¹ (M._*_ x y)
      unique =
          sym (M.idl {x = M._*_ (M._⁻¹ x) (M._⁻¹ y)})
        ∙ ap (λ z → M._*_ z (M._*_ (M._⁻¹ x) (M._⁻¹ y)))
            (sym (M.inversel {x = M._*_ x y}))
        ∙ sym (M.associative
            {x = M._⁻¹ (M._*_ x y)} {y = M._*_ x y}
            {z = M._*_ (M._⁻¹ x) (M._⁻¹ y)})
        ∙ ap (M._*_ (M._⁻¹ (M._*_ x y))) cancel
        ∙ M.idr {x = M._⁻¹ (M._*_ x y)}

    ab-inv-inv : (x : ⌞ A ⌟) → M._⁻¹ (M._⁻¹ x) ≡ x
    ab-inv-inv x =
        sym (M.idr {x = M._⁻¹ (M._⁻¹ x)})
      ∙ ap (M._*_ (M._⁻¹ (M._⁻¹ x))) (sym (M.inversel {x = x}))
      ∙ M.associative {x = M._⁻¹ (M._⁻¹ x)} {y = M._⁻¹ x} {z = x}
      ∙ ap (λ z → M._*_ z x) (M.inversel {x = M._⁻¹ x})
      ∙ M.idl {x = x}

    ab-decomp
      : (x t : ⌞ A ⌟)
      → t ≡ M._*_ (M._⁻¹ (M._*_ x (M._⁻¹ t))) x
    ab-decomp x t = sym
      ( ap (λ z → M._*_ z x) (ab-inv-distr x (M._⁻¹ t))
      ∙ ap (λ z → M._*_ (M._*_ (M._⁻¹ x) z) x) (ab-inv-inv t)
      ∙ ap (λ z → M._*_ z x) (M.commutes {x = M._⁻¹ x} {y = t})
      ∙ sym (M.associative {x = t} {y = M._⁻¹ x} {z = x})
      ∙ ap (M._*_ t) (M.inversel {x = x})
      ∙ M.idr {x = t})
```
-->

```agda
module _ (C : Chain-complex lzero) where
  private
    module Cc (n : Nat) = Abelian-group-on (C .ob n .snd)
    module ΓC = Functor (Γ C)
    module MΓ (n : Nat) =
      Abelian-group-on (MC.Moore (Γ C) .ob n .snd)
```

The boundary step, isolated: if the evaluation vanishes, so does
the value on the pushforward of the fundamental class along the
bottom coface.

```agda
  head-vanish
    : (k' : Nat) (φn : ⌞ MC.Moore (Γ C) .ob (suc k') ⌟)
    → dk-counit-level C (suc k') .∫Hom.fst φn ≡ Cc.1g (suc k')
    → φn .fst .map k' .∫Hom.fst
        (NΔ-map (δ fzero) .map k' .∫Hom.fst (fundamental k'))
    ≡ Cc.1g k'
  head-vanish k' (φ , nrm) hyp = sym split' ∙ comm-chain
    where
    eq₁ : 1 Nat.+ suc k' ≡ suc (suc k')
    eq₁ = sym (Nat.+-sucr 0 (suc k')) ∙ refl

    tail₁ : ⌞ NΔ (suc k') .ob k' ⌟
    tail₁ =
        Σalt k' (suc k') 1 eq₁
      , Σnorm k' (suc k') 1 eq₁

    head-elem : ⌞ NΔ (suc k') .ob k' ⌟
    head-elem = NΔ-map (δ fzero) .map k' .∫Hom.fst (fundamental k')

    split'
      : φ .map k' .∫Hom.fst
          (Σalt k' (suc (suc k')) 0 refl , Σnorm k' (suc (suc k')) 0 refl)
      ≡ φ .map k' .∫Hom.fst head-elem
    split' =
        ap (φ .map k' .∫Hom.fst)
          (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc k' ] ⟩ k') refl)
      ∙ is-group-hom.pres-⋆ (φ .map k' .∫Hom.snd) head-elem
          (Abelian-group-on._⁻¹ (NΔ (suc k') .ob k' .snd) tail₁)
      ∙ ap (Cc._*_ k' (φ .map k' .∫Hom.fst head-elem))
          ( is-group-hom.pres-inv (φ .map k' .∫Hom.snd) {x = tail₁}
          ∙ ap (Cc._⁻¹ k')
              (kill C k' (φ , nrm) (suc k') 1 eq₁ (Nat.s≤s Nat.0≤x))
          ∙ (sym (Cc.idl k') ∙ Cc.inverser k'))
      ∙ Cc.idr k'

    comm-chain
      : φ .map k' .∫Hom.fst
          (Σalt k' (suc (suc k')) 0 refl , Σnorm k' (suc (suc k')) 0 refl)
      ≡ Cc.1g k'
    comm-chain =
        ap (φ .map k' .∫Hom.fst)
          (Σ-prop-path (MC.norm-is-prop ℤ⟨ Δ[ suc k' ] ⟩ k')
            (sym (∂-fundamental k')))
      ∙ φ .comm k' (fundamental (suc k'))
      ∙ ap (C .∂ᶜ k' .∫Hom.fst) hyp
      ∙ is-group-hom.pres-id (C .∂ᶜ k' .∫Hom.snd)
```

The theorem.

```agda
  counit-inj
    : (k : Nat) (φn : ⌞ MC.Moore (Γ C) .ob k ⌟)
    → dk-counit-level C k .∫Hom.fst φn ≡ Cc.1g k
    → φn ≡ MΓ.1g k
  counit-inj k (φ , nrm) hyp =
    Σ-prop-path (MC.norm-is-prop (Γ C) k)
      (Chain-map-path λ j → ext λ x p →
          ap (φ .map j .∫Hom.fst)
            (sym (Tsub-fix ℤ⟨ Δ[ k ] ⟩ j (x , p)))
        ∙ ap (λ w → w .∫Hom.fst x) (vanish j))
    where
    Φ : (j : Nat) → Ab lzero .Precategory.Hom
          (ℤ⟨ Δ[ k ] ⟩ .F₀ j) (C .ob j)
    Φ j = Ab lzero .Precategory._∘_ (φ .map j) (Tsub ℤ⟨ Δ[ k ] ⟩ j)

    gen-case
      : (j : Nat) (α : Δ-map j k)
      → φ .map j .∫Hom.fst
          (Tsub ℤ⟨ Δ[ k ] ⟩ j .∫Hom.fst (genΔ k α))
      ≡ Cc.1g j
    gen-case = go k φ nrm hyp
      where
      go : (k : Nat) (φ : Chain-map (NΔ k) C)
           (nrm : MC.norm (Γ C) k φ)
         → φ .map k .∫Hom.fst (fundamental k) ≡ Cc.1g k
         → (j : Nat) (α : Δ-map j k)
         → φ .map j .∫Hom.fst
             (Tsub ℤ⟨ Δ[ k ] ⟩ j .∫Hom.fst (genΔ k α))
         ≡ Cc.1g j
      go zero φ nrm hyp zero α =
          ap (λ w → φ .map 0 .∫Hom.fst
                (Tsub ℤ⟨ Δ[ 0 ] ⟩ 0 .∫Hom.fst (genΔ 0 w)))
            (Δ-map-path (λ x → Fin1-path _ _))
        ∙ ap (φ .map 0 .∫Hom.fst) (Tsub-id 0)
        ∙ hyp
      go zero φ nrm hyp (suc j') α =
          ap (φ .map (suc j') .∫Hom.fst)
            (collision-kill 0 α fzero (Fin1-path _ _))
        ∙ is-group-hom.pres-id (φ .map (suc j') .∫Hom.snd)
      go (suc k') φ nrm hyp j α with classify α
      ... | cls-coll t c = coll-helper j α t c
        where
        coll-helper
          : (j : Nat) (α : Δ-map j (suc k')) (t : Fin j)
          → α .Δ-map.map (weaken t) ≡ α .Δ-map.map (fsuc t)
          → φ .map j .∫Hom.fst
              (Tsub ℤ⟨ Δ[ suc k' ] ⟩ j .∫Hom.fst (genΔ (suc k') α))
          ≡ Cc.1g j
        coll-helper zero α t c = absurd (Fin-absurd t)
        coll-helper (suc j') α t c =
            ap (φ .map (suc j') .∫Hom.fst)
              (collision-kill (suc k') α t c)
          ∙ is-group-hom.pres-id (φ .map (suc j') .∫Hom.snd)
      ... | cls-miss i' m =
          ap (φ .map j .∫Hom.fst) (push-Tsub k' α i' m)
        ∙ happly
            (ap (λ w → w .map j .∫Hom.fst)
              (nrm i'))
            (Tsub ℤ⟨ Δ[ k' ] ⟩ j .∫Hom.fst
              (genΔ k' (miss-factor α (fsuc i') m .fst)))
      ... | cls-id jk lid = subst
          (λ n → (β : Δ-map n (suc k'))
               → (∀ x → β .Δ-map.map x .lower ≡ x .lower)
               → φ .map n .∫Hom.fst
                   (Tsub ℤ⟨ Δ[ suc k' ] ⟩ n .∫Hom.fst (genΔ (suc k') β))
               ≡ Cc.1g n)
          (sym jk) univ α lid
        where
        univ : (β : Δ-map (suc k') (suc k'))
             → (∀ x → β .Δ-map.map x .lower ≡ x .lower)
             → φ .map (suc k') .∫Hom.fst
                 (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc k') .∫Hom.fst (genΔ (suc k') β))
             ≡ Cc.1g (suc k')
        univ β lidβ =
            ap (λ w → φ .map (suc k') .∫Hom.fst
                  (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc k') .∫Hom.fst (genΔ (suc k') w)))
              (Δ-map-path λ x → fin-ap {n = λ _ → suc (suc k')} (lidβ x))
          ∙ ap (φ .map (suc k') .∫Hom.fst) (Tsub-id (suc k'))
          ∙ hyp
      ... | cls-δ⁰ kj lsuc = subst
          (λ n → (β : Δ-map n (suc k'))
               → (∀ x → β .Δ-map.map x .lower ≡ suc (x .lower))
               → φ .map n .∫Hom.fst
                   (Tsub ℤ⟨ Δ[ suc k' ] ⟩ n .∫Hom.fst (genΔ (suc k') β))
               ≡ Cc.1g n)
          (ap Nat.pred kj) univ' α lsuc
        where
        univ' : (β : Δ-map k' (suc k'))
              → (∀ x → β .Δ-map.map x .lower ≡ suc (x .lower))
              → φ .map k' .∫Hom.fst
                  (Tsub ℤ⟨ Δ[ suc k' ] ⟩ k' .∫Hom.fst (genΔ (suc k') β))
              ≡ Cc.1g k'
        univ' β lsucβ =
            ap (φ .map k' .∫Hom.fst) arg-path
          ∙ head-vanish k' (φ , nrm) hyp
          where
          pushα₀ : ℤ⟨ Δ[ k' ] ⟩ => ℤ⟨ Δ[ suc k' ] ⟩
          pushα₀ = Free-abelian-functor ▸ Δmap-nt (δ fzero)

          β≡δ₀ : β ≡ δ fzero
          β≡δ₀ = Δ-map-path λ x →
            fin-ap {n = λ _ → suc (suc k')} (lsucβ x)

          push-path
            : pushα₀ .η k' .∫Hom.fst (genΔ k' (Δ .Precategory.id))
            ≡ genΔ (suc k') β
          push-path =
              gen-natural (Δ[ k' ] .F₀ k') (Δ[ suc k' ] .F₀ k')
                (Δmap-nt (δ fzero) .η k') (Δ .Precategory.id)
            ∙ ap (gen {Δ[ suc k' ] .F₀ k'})
                (Δ-map-path (λ x → refl) ∙ sym β≡δ₀)

          arg-path
            : Tsub ℤ⟨ Δ[ suc k' ] ⟩ k' .∫Hom.fst (genΔ (suc k') β)
            ≡ NΔ-map (δ fzero) .map k' .∫Hom.fst (fundamental k')
          arg-path = Σ-prop-path
            (MC.norm-is-prop ℤ⟨ Δ[ suc k' ] ⟩ k')
            ( ap (λ w → Tsub ℤ⟨ Δ[ suc k' ] ⟩ k' .∫Hom.fst w .fst)
                (sym push-path)
            ∙ sym (Tsub-natural pushα₀ k' (genΔ k' (Δ .Precategory.id)))
            ∙ ap (pushα₀ .η k' .∫Hom.fst) (ap fst (Tsub-id k')))

    vanish : (j : Nat) → Φ j ≡ zero-hom'
    vanish j = free-ext (Δ[ k ] .F₀ j) (C .ob j) (gen-case j)
```

## The prescription

For surjectivity we build, from a chain element, the normalized
simplicial map evaluating to it: on generators, the identity gets
the element, the bottom coface its boundary, and everything else
dies. Determinacy of the classification makes the prescription
well-defined, and the vanishing cases are closed under the
degeneracy and coface structure.

```agda
  module Surj (k' : Nat) (c : ⌞ C .ob (suc k') ⌟) where
    private
      kk : Nat
      kk = suc k'

      Gkk : Functor (Δ ^op) (Ab lzero)
      Gkk = ℤ⟨ Δ[ kk ] ⟩

    w : (j : Nat) → Δ-map j kk → ⌞ C .ob j ⌟
    w j α with classify α
    ... | cls-miss _ _ = Cc.1g j
    ... | cls-coll _ _ = Cc.1g j
    ... | cls-id jk lid = subst (λ n → ⌞ C .ob n ⌟) (sym jk) c
    ... | cls-δ⁰ kj lsuc =
      subst (λ n → ⌞ C .ob n ⌟) (ap Nat.pred kj)
        (C .∂ᶜ k' .∫Hom.fst c)

    ψ : (j : Nat) → Ab lzero .Precategory.Hom (Gkk .F₀ j) (C .ob j)
    ψ j = R-adjunct adj {a = Δ[ kk ] .F₀ j} {b = C .ob j} (w j)

    ψ-gen : (j : Nat) (α : Δ-map j kk)
          → ψ j .∫Hom.fst (genΔ kk α) ≡ w j α
    ψ-gen j α = ev-gen (Δ[ kk ] .F₀ j) (C .ob j) (w j) α

    w-coll
      : (j' : Nat) (α : Δ-map (suc j') kk) (t : Fin (suc j'))
      → α .Δ-map.map (weaken t) ≡ α .Δ-map.map (fsuc t)
      → w (suc j') α ≡ Cc.1g (suc j')
    w-coll j' α t coll with classify α
    ... | cls-miss _ _ = refl
    ... | cls-coll _ _ = refl
    ... | cls-id jk lid = absurd (Nat.¬sucx≤x (t .lower)
      (subst (λ z → suc (t .lower) Nat.≤ z) (sym e) Nat.≤-refl))
      where
      e : t .lower ≡ suc (t .lower)
      e = sym (weaken-lower t)
        ∙ sym (lid (weaken t))
        ∙ ap Fin.lower coll
        ∙ lid (fsuc t)
    ... | cls-δ⁰ kj lsuc = absurd (Nat.¬sucx≤x (suc (t .lower))
      (subst (λ z → suc (suc (t .lower)) Nat.≤ z) (sym e) Nat.≤-refl))
      where
      e : suc (t .lower) ≡ suc (suc (t .lower))
      e = sym (ap suc (weaken-lower t))
        ∙ sym (lsuc (weaken t))
        ∙ ap Fin.lower coll
        ∙ lsuc (fsuc t)
```

The prescription vanishes on every degeneracy image and on every
pushforward along a positive coface — the closure properties that
make it a normalized chain map.

```agda
    private
      squish-collapse
        : ∀ {n} (t : Fin (suc n))
        → squish t (weaken t) ≡ squish t (fsuc t)
      squish-collapse {zero} t with fin-view t
      ... | zero = refl
      ... | suc t' = absurd (Fin-absurd t')
      squish-collapse {suc n'} t with fin-view t
      ... | zero = refl
      ... | suc t' = ap fsuc (squish-collapse t')

    σ-collides
      : {j' : Nat} (ν : Δ-map j' kk) (t : Fin (suc j'))
      → (ν ∘Δ σ t) .Δ-map.map (weaken t)
      ≡ (ν ∘Δ σ t) .Δ-map.map (fsuc t)
    σ-collides ν t = ap (ν .Δ-map.map) (squish-collapse t)

    w-miss
      : (j : Nat) (α : Δ-map j kk) (i' : Fin (suc k'))
      → (∀ x → ¬ (α .Δ-map.map x ≡ fsuc i'))
      → w j α ≡ Cc.1g j
    w-miss j α i' m with classify α
    ... | cls-miss _ _ = refl
    ... | cls-coll _ _ = refl
    ... | cls-id jk lid = absurd (m x hit)
      where
      bx : suc (suc (i' .lower)) Nat.≤ suc j
      bx = subst (λ n → suc (suc (i' .lower)) Nat.≤ suc n) (sym jk)
        (Nat.s≤s (i' .Fin.bounded))
      x : Fin (suc j)
      x = fin (suc (i' .lower)) ⦃ bx ⦄
      hit : α .Δ-map.map x ≡ fsuc i'
      hit = fin-ap {n = λ _ → suc kk} (lid x)
    ... | cls-δ⁰ kj lsuc = absurd (m x hit)
      where
      bx : suc (i' .lower) Nat.≤ suc j
      bx = subst (λ n → suc (i' .lower) Nat.≤ n) (ap suc (ap Nat.pred kj))
        (i' .Fin.bounded)
      x : Fin (suc j)
      x = fin (i' .lower) ⦃ bx ⦄
      hit : α .Δ-map.map x ≡ fsuc i'
      hit = fin-ap {n = λ _ → suc kk} (lsuc x)

    ψ-s
      : (j' : Nat) (t : Fin (suc j'))
      → Ab lzero .Precategory._∘_ (ψ (suc j')) (Gkk .F₁ (σ t))
      ≡ zero-hom'
    ψ-s j' t = free-ext (Δ[ kk ] .F₀ j') (C .ob (suc j')) λ ν →
        ap (ψ (suc j') .∫Hom.fst)
          (gen-natural (Δ[ kk ] .F₀ j') (Δ[ kk ] .F₀ (suc j'))
            (Δ[ kk ] .F₁ (σ t)) ν)
      ∙ ψ-gen (suc j') (ν ∘Δ σ t)
      ∙ w-coll j' (ν ∘Δ σ t) t (σ-collides ν t)

    ψ-deg
      : (m j : Nat) (v : ⌞ Gkk .F₀ (suc m) ⌟)
      → Deg Gkk {m} j v
      → ψ (suc m) .∫Hom.fst v ≡ Cc.1g (suc m)
    ψ-deg m zero v (y , p) =
        ap (ψ (suc m) .∫Hom.fst) p
      ∙ ap (λ h → h .∫Hom.fst y) (ψ-s m fzero)
    ψ-deg m (suc j) v (b , y , x' , rep' , p) =
        ap (ψ (suc m) .∫Hom.fst) p
      ∙ is-group-hom.pres-⋆ (ψ (suc m) .∫Hom.snd) x' _
      ∙ ap₂ (Cc._*_ (suc m))
          (ψ-deg m j x' rep')
          (ap (λ h → h .∫Hom.fst y) (ψ-s m (fin (suc j) ⦃ b ⦄)))
      ∙ Cc.idl (suc m)

    ψ-push
      : (j : Nat) (i : Fin (suc k'))
      → Ab lzero .Precategory._∘_ (ψ j)
          ((Free-abelian-functor ▸ Δmap-nt (δ (fsuc i))) .η j)
      ≡ zero-hom'
    ψ-push j i = free-ext (Δ[ k' ] .F₀ j) (C .ob j) λ ν →
        ap (ψ j .∫Hom.fst)
          (gen-natural (Δ[ k' ] .F₀ j) (Δ[ kk ] .F₀ j)
            (Δmap-nt (δ (fsuc i)) .η j) ν)
      ∙ ψ-gen j (δ (fsuc i) ∘Δ ν)
      ∙ w-miss j (δ (fsuc i) ∘Δ ν) i
          (λ x e → skip-skips (fsuc i) (ν .Δ-map.map x) e)
```

Evaluating the prescription at the fundamental class returns the
chosen element: the operator's correction is degenerate, so only
the generating simplex contributes, and on it the classification is
forced into its identity case.

```agda
    private
      module Gkm (n : Nat) = Abelian-group-on (Gkk .F₀ n .snd)

      ginv-distr : (x y : ⌞ Gkk .F₀ kk ⌟)
                 → Gkm._⁻¹ kk (Gkm._*_ kk x y)
                 ≡ Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)
      ginv-distr x y = sym unique
        where
        cancel : Gkm._*_ kk (Gkm._*_ kk x y)
                   (Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)) ≡ Gkm.1g kk
        cancel =
            sym (Gkm.associative kk
              {x = x} {y = y}
              {z = Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)})
          ∙ ap (Gkm._*_ kk x)
              ( Gkm.associative kk
                  {x = y} {y = Gkm._⁻¹ kk x} {z = Gkm._⁻¹ kk y}
              ∙ ap (λ z → Gkm._*_ kk z (Gkm._⁻¹ kk y))
                  (Gkm.commutes kk {x = y} {y = Gkm._⁻¹ kk x})
              ∙ sym (Gkm.associative kk
                  {x = Gkm._⁻¹ kk x} {y = y} {z = Gkm._⁻¹ kk y})
              ∙ ap (Gkm._*_ kk (Gkm._⁻¹ kk x)) (Gkm.inverser kk {x = y})
              ∙ Gkm.idr kk {x = Gkm._⁻¹ kk x})
          ∙ Gkm.inverser kk {x = x}
        unique : Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)
               ≡ Gkm._⁻¹ kk (Gkm._*_ kk x y)
        unique =
            sym (Gkm.idl kk)
          ∙ ap (λ z → Gkm._*_ kk z (Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)))
              (sym (Gkm.inversel kk {x = Gkm._*_ kk x y}))
          ∙ sym (Gkm.associative kk
              {x = Gkm._⁻¹ kk (Gkm._*_ kk x y)}
              {y = Gkm._*_ kk x y}
              {z = Gkm._*_ kk (Gkm._⁻¹ kk x) (Gkm._⁻¹ kk y)})
          ∙ ap (Gkm._*_ kk (Gkm._⁻¹ kk (Gkm._*_ kk x y))) cancel
          ∙ Gkm.idr kk

      ginv-inv : (x : ⌞ Gkk .F₀ kk ⌟)
               → Gkm._⁻¹ kk (Gkm._⁻¹ kk x) ≡ x
      ginv-inv x =
          sym (Gkm.idr kk)
        ∙ ap (Gkm._*_ kk (Gkm._⁻¹ kk (Gkm._⁻¹ kk x)))
            (sym (Gkm.inversel kk {x = x}))
        ∙ Gkm.associative kk
            {x = Gkm._⁻¹ kk (Gkm._⁻¹ kk x)} {y = Gkm._⁻¹ kk x} {z = x}
        ∙ ap (λ z → Gkm._*_ kk z x) (Gkm.inversel kk {x = Gkm._⁻¹ kk x})
        ∙ Gkm.idl kk

    w-id : w kk (Δ .Precategory.id) ≡ c
    w-id with classify (Δ .Precategory.id {kk})
    ... | cls-miss i' m = absurd (m (fsuc i') refl)
    ... | cls-coll t coll = absurd (Nat.¬sucx≤x (t .lower)
      (subst (λ z → suc (t .lower) Nat.≤ z) (sym e') Nat.≤-refl))
      where
      e' : t .lower ≡ suc (t .lower)
      e' = sym (weaken-lower t) ∙ ap Fin.lower coll
    ... | cls-id jk lid =
        ap (λ e' → subst (λ n → ⌞ C .ob n ⌟) (sym e') c)
          (Nat.Nat-is-set kk kk jk refl)
      ∙ transport-refl c
    ... | cls-δ⁰ kj lsuc = absurd (Nat.¬sucx≤x kk
      (subst (λ z → suc kk Nat.≤ z) (sym kj) Nat.≤-refl))

    ev-comp
      : ψ kk .∫Hom.fst
          (Tsub Gkk kk .∫Hom.fst (genΔ kk (Δ .Precategory.id)) .fst)
      ≡ c
    ev-comp =
        ap (ψ kk .∫Hom.fst) traw-path
      ∙ is-group-hom.pres-⋆ (ψ kk .∫Hom.snd) (Gkm._⁻¹ kk D∆) e₀
      ∙ ap₂ (Cc._*_ kk)
          ( is-group-hom.pres-inv (ψ kk .∫Hom.snd) {x = D∆}
          ∙ ap (Cc._⁻¹ kk) (ψ-deg k' k' D∆ (Tsub-diff Gkk k' e₀))
          ∙ (sym (Cc.idl kk) ∙ Cc.inverser kk))
          (ψ-gen kk (Δ .Precategory.id))
      ∙ Cc.idl kk
      ∙ w-id
      where
      e₀ : ⌞ Gkk .F₀ kk ⌟
      e₀ = genΔ kk (Δ .Precategory.id)

      Traw : ⌞ Gkk .F₀ kk ⌟
      Traw = Tsub Gkk kk .∫Hom.fst e₀ .fst

      D∆ : ⌞ Gkk .F₀ kk ⌟
      D∆ = Gkm._*_ kk e₀ (Gkm._⁻¹ kk Traw)

      traw-path : Traw ≡ Gkm._*_ kk (Gkm._⁻¹ kk D∆) e₀
      traw-path = sym
        ( ap (λ z → Gkm._*_ kk z e₀) (ginv-distr e₀ (Gkm._⁻¹ kk Traw))
        ∙ ap (λ z → Gkm._*_ kk (Gkm._*_ kk (Gkm._⁻¹ kk e₀) z) e₀)
            (ginv-inv Traw)
        ∙ ap (λ z → Gkm._*_ kk z e₀)
            (Gkm.commutes kk {x = Gkm._⁻¹ kk e₀} {y = Traw})
        ∙ sym (Gkm.associative kk
            {x = Traw} {y = Gkm._⁻¹ kk e₀} {z = e₀})
        ∙ ap (Gkm._*_ kk Traw) (Gkm.inversel kk {x = e₀})
        ∙ Gkm.idr kk {x = Traw})
```

The bottom coface receives the boundary of the chosen element, and
the alternating tails die: directly for positive cofaces, and
through the bottom pushforward because double-coface composites
still miss a positive value.

```agda
    w-δ⁰ : w k' (δ fzero) ≡ C .∂ᶜ k' .∫Hom.fst c
    w-δ⁰ with classify {k'} {k'} (δ fzero)
    ... | cls-miss i' m = absurd (m i' refl)
    ... | cls-coll t coll = absurd (Nat.¬sucx≤x (t .lower)
      (subst (λ z → suc (t .lower) Nat.≤ z) (sym e') Nat.≤-refl))
      where
      e' : t .lower ≡ suc (t .lower)
      e' = sym (weaken-lower t)
         ∙ ap Fin.lower (skip-injective fzero (weaken t) (fsuc t) coll)
    ... | cls-id jk lid = absurd (Nat.¬sucx≤x k'
      (subst (λ z → suc k' Nat.≤ z) (sym jk) Nat.≤-refl))
    ... | cls-δ⁰ kj lsuc =
        ap (λ e' → subst (λ n → ⌞ C .ob n ⌟) (ap Nat.pred e')
              (C .∂ᶜ k' .∫Hom.fst c))
          (Nat.Nat-is-set kk kk kj refl)
      ∙ transport-refl (C .∂ᶜ k' .∫Hom.fst c)

    ψ-Σalt
      : (fuel j : Nat) (eq : j Nat.+ fuel ≡ suc (suc k'))
      → 1 Nat.≤ j
      → ψ k' .∫Hom.fst (Σalt k' fuel j eq) ≡ Cc.1g k'
    ψ-Σalt zero j eq ge =
      is-group-hom.pres-id (ψ k' .∫Hom.snd)
    ψ-Σalt (suc fuel) zero eq ge = absurd (Nat.¬suc≤0 ge)
    ψ-Σalt (suc fuel) (suc j₁) eq ge =
        is-group-hom.pres-⋆ (ψ k' .∫Hom.snd) head-t tail-inv
      ∙ ap₂ (Cc._*_ k')
          (ap (λ h → h .∫Hom.fst (fundamental k' .fst))
            (ψ-push k' (fin j₁ ⦃ Nat.≤-peel bj ⦄)))
          ( is-group-hom.pres-inv (ψ k' .∫Hom.snd) {x = tail-t}
          ∙ ap (Cc._⁻¹ k')
              (ψ-Σalt fuel (suc (suc j₁))
                (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq) (Nat.s≤s Nat.0≤x))
          ∙ (sym (Cc.idl k') ∙ Cc.inverser k'))
      ∙ Cc.idl k'
      where
      bj : suc j₁ Nat.< suc (suc k')
      bj = subst (suc (suc j₁) Nat.≤_)
             (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq)
             (Nat.s≤s (le-plus (suc j₁) fuel))

      head-t : ⌞ Gkk .F₀ k' ⌟
      head-t = push-nt k' (fin (suc j₁) ⦃ bj ⦄) .η k' .∫Hom.fst
        (fundamental k' .fst)

      tail-t : ⌞ Gkk .F₀ k' ⌟
      tail-t = Σalt k' fuel (suc (suc j₁))
        (sym (Nat.+-sucr (suc j₁) fuel) ∙ eq)

      tail-inv : ⌞ Gkk .F₀ k' ⌟
      tail-inv = Gkm._⁻¹ k' tail-t
```

Evaluating the prescription on the bottom coface generator returns
the boundary of the chosen element; and through the bottom
pushforward the whole alternating sum dies, because double-coface
composites always miss a positive value.

```agda
  ev-δ⁰
    : (k₀ : Nat) (c₀ : ⌞ C .ob (suc k₀) ⌟)
    → Surj.ψ k₀ c₀ k₀ .∫Hom.fst
        (Tsub ℤ⟨ Δ[ suc k₀ ] ⟩ k₀ .∫Hom.fst
          (genΔ (suc k₀) (δ fzero)) .fst)
    ≡ C .∂ᶜ k₀ .∫Hom.fst c₀
  ev-δ⁰ zero c₀ =
      Surj.ψ-gen 0 c₀ 0 (δ fzero)
    ∙ Surj.w-δ⁰ 0 c₀
  ev-δ⁰ (suc m) c₀ =
      ap (Surj.ψ (suc m) c₀ (suc m) .∫Hom.fst)
        (ab-decomp e₀ Traw)
    ∙ is-group-hom.pres-⋆ (Surj.ψ (suc m) c₀ (suc m) .∫Hom.snd)
        (Gm._⁻¹ D∆) e₀
    ∙ ap₂ (Cc._*_ (suc m))
        ( is-group-hom.pres-inv (Surj.ψ (suc m) c₀ (suc m) .∫Hom.snd)
            {x = D∆}
        ∙ ap (Cc._⁻¹ (suc m))
            (Surj.ψ-deg (suc m) c₀ m m D∆ (Tsub-diff Gm' m e₀))
        ∙ (sym (Cc.idl (suc m)) ∙ Cc.inverser (suc m)))
        ( Surj.ψ-gen (suc m) c₀ (suc m) (δ fzero)
        ∙ Surj.w-δ⁰ (suc m) c₀)
    ∙ Cc.idl (suc m)
    where
    Gm' : Functor (Δ ^op) (Ab lzero)
    Gm' = ℤ⟨ Δ[ suc (suc m) ] ⟩

    module Gm = Abelian-group-on (Gm' .F₀ (suc m) .snd)
    open AbL (Gm' .F₀ (suc m)) using (ab-decomp)

    e₀ : ⌞ Gm' .F₀ (suc m) ⌟
    e₀ = genΔ (suc (suc m)) (δ fzero)

    Traw : ⌞ Gm' .F₀ (suc m) ⌟
    Traw = Tsub Gm' (suc m) .∫Hom.fst e₀ .fst

    D∆ : ⌞ Gm' .F₀ (suc m) ⌟
    D∆ = Gm._*_ e₀ (Gm._⁻¹ Traw)

  ψδ₀-Σalt
    : (j : Nat) (c' : ⌞ C .ob (suc (suc j)) ⌟)
      (fuel jv : Nat) (eq : jv Nat.+ fuel ≡ suc (suc j))
    → Surj.ψ (suc j) c' j .∫Hom.fst
        ((Free-abelian-functor ▸ Δmap-nt (δ fzero)) .η j .∫Hom.fst
          (Σalt j fuel jv eq))
    ≡ Cc.1g j
  ψδ₀-Σalt j c' zero jv eq =
      ap (Surj.ψ (suc j) c' j .∫Hom.fst)
        (is-group-hom.pres-id (pushδ₀ .η j .∫Hom.snd))
    ∙ is-group-hom.pres-id (Surj.ψ (suc j) c' j .∫Hom.snd)
    where
    pushδ₀ : ℤ⟨ Δ[ suc j ] ⟩ => ℤ⟨ Δ[ suc (suc j) ] ⟩
    pushδ₀ = Free-abelian-functor ▸ Δmap-nt (δ fzero)
  ψδ₀-Σalt j c' (suc fuel) jv eq =
      ap (Surj.ψ (suc j) c' j .∫Hom.fst)
        (is-group-hom.pres-⋆ (pushδ₀ .η j .∫Hom.snd) head-t tail-inv)
    ∙ is-group-hom.pres-⋆ (Surj.ψ (suc j) c' j .∫Hom.snd)
        (pushδ₀ .η j .∫Hom.fst head-t)
        (pushδ₀ .η j .∫Hom.fst tail-inv)
    ∙ ap₂ (Cc._*_ j)
        head-dies
        ( ap (Surj.ψ (suc j) c' j .∫Hom.fst)
            (is-group-hom.pres-inv (pushδ₀ .η j .∫Hom.snd) {x = tail-t})
        ∙ is-group-hom.pres-inv (Surj.ψ (suc j) c' j .∫Hom.snd)
            {x = pushδ₀ .η j .∫Hom.fst tail-t}
        ∙ ap (Cc._⁻¹ j)
            (ψδ₀-Σalt j c' fuel (suc jv)
              (sym (Nat.+-sucr jv fuel) ∙ eq))
        ∙ (sym (Cc.idl j) ∙ Cc.inverser j))
    ∙ Cc.idl j
    where
    pushδ₀ : ℤ⟨ Δ[ suc j ] ⟩ => ℤ⟨ Δ[ suc (suc j) ] ⟩
    pushδ₀ = Free-abelian-functor ▸ Δmap-nt (δ fzero)

    module Gj = Abelian-group-on (ℤ⟨ Δ[ suc j ] ⟩ .F₀ j .snd)

    bj : jv Nat.< suc (suc j)
    bj = subst (suc jv Nat.≤_)
           (sym (Nat.+-sucr jv fuel) ∙ eq)
           (Nat.s≤s (le-plus jv fuel))

    head-t : ⌞ ℤ⟨ Δ[ suc j ] ⟩ .F₀ j ⌟
    head-t = push-nt j (fin jv ⦃ bj ⦄) .η j .∫Hom.fst
      (fundamental j .fst)

    tail-t : ⌞ ℤ⟨ Δ[ suc j ] ⟩ .F₀ j ⌟
    tail-t = Σalt j fuel (suc jv)
      (sym (Nat.+-sucr jv fuel) ∙ eq)

    tail-inv : ⌞ ℤ⟨ Δ[ suc j ] ⟩ .F₀ j ⌟
    tail-inv = Gj._⁻¹ tail-t

    comp-vanish
      : Ab lzero .Precategory._∘_
          (Ab lzero .Precategory._∘_ (Surj.ψ (suc j) c' j)
            (pushδ₀ .η j))
          (push-nt j (fin jv ⦃ bj ⦄) .η j)
      ≡ zero-hom'
    comp-vanish = free-ext (Δ[ j ] .F₀ j) (C .ob j) λ ν →
        ap (λ v → Surj.ψ (suc j) c' j .∫Hom.fst
              (pushδ₀ .η j .∫Hom.fst v))
          (gen-natural (Δ[ j ] .F₀ j) (Δ[ suc j ] .F₀ j)
            (Δmap-nt (δ (fin jv ⦃ bj ⦄)) .η j) ν)
      ∙ ap (Surj.ψ (suc j) c' j .∫Hom.fst)
          (gen-natural (Δ[ suc j ] .F₀ j) (Δ[ suc (suc j) ] .F₀ j)
            (Δmap-nt (δ fzero) .η j) (δ (fin jv ⦃ bj ⦄) ∘Δ ν))
      ∙ Surj.ψ-gen (suc j) c' j
          (δ fzero ∘Δ (δ (fin jv ⦃ bj ⦄) ∘Δ ν))
      ∙ Surj.w-miss (suc j) c' j
          (δ fzero ∘Δ (δ (fin jv ⦃ bj ⦄) ∘Δ ν))
          (fin jv ⦃ bj ⦄)
          (λ x e → skip-skips (fin jv ⦃ bj ⦄)
            (ν .Δ-map.map x) (fsuc-inj e))

    head-dies
      : Surj.ψ (suc j) c' j .∫Hom.fst
          (pushδ₀ .η j .∫Hom.fst head-t)
      ≡ Cc.1g j
    head-dies = ap (λ h → h .∫Hom.fst (fundamental j .fst)) comp-vanish
```

## The chain square

On generators, the prescription commutes with the boundaries. The
classification drives the argument: collisions die on both sides,
missed positive values die through naturality of the pushforward,
the identity generator reproduces the boundary formula against the
chosen element, and the bottom coface closes with
$\partial \circ \partial = 0$.

```agda
  square
    : (k' : Nat) (c : ⌞ C .ob (suc k') ⌟)
      (j : Nat) (α : Δ-map (suc j) (suc k'))
    → Surj.ψ k' c j .∫Hom.fst
        (ℤ⟨ Δ[ suc k' ] ⟩ .F₁ (δ fzero) .∫Hom.fst
          (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc j) .∫Hom.fst
            (genΔ (suc k') α) .fst))
    ≡ C .∂ᶜ j .∫Hom.fst
        (Surj.ψ k' c (suc j) .∫Hom.fst
          (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc j) .∫Hom.fst
            (genΔ (suc k') α) .fst))
  square k' c j α with classify α
  ... | cls-coll t coll =
      ap (λ v → Surj.ψ k' c j .∫Hom.fst
            (Gkk .F₁ (δ fzero) .∫Hom.fst v)) rawkill
    ∙ ap (Surj.ψ k' c j .∫Hom.fst)
        (is-group-hom.pres-id (Gkk .F₁ (δ fzero) .∫Hom.snd))
    ∙ is-group-hom.pres-id (Surj.ψ k' c j .∫Hom.snd)
    ∙ sym
      ( ap (λ v → C .∂ᶜ j .∫Hom.fst (Surj.ψ k' c (suc j) .∫Hom.fst v))
          rawkill
      ∙ ap (C .∂ᶜ j .∫Hom.fst)
          (is-group-hom.pres-id (Surj.ψ k' c (suc j) .∫Hom.snd))
      ∙ is-group-hom.pres-id (C .∂ᶜ j .∫Hom.snd))
    where
    Gkk : Functor (Δ ^op) (Ab lzero)
    Gkk = ℤ⟨ Δ[ suc k' ] ⟩

    rawkill
      : Tsub Gkk (suc j) .∫Hom.fst (genΔ (suc k') α) .fst
      ≡ Abelian-group-on.1g (Gkk .F₀ (suc j) .snd)
    rawkill = ap fst (collision-kill (suc k') α t coll)
  ... | cls-miss i' m =
      ap (λ v → Surj.ψ k' c j .∫Hom.fst
            (Gkk .F₁ (δ fzero) .∫Hom.fst v)) rawpush
    ∙ ap (Surj.ψ k' c j .∫Hom.fst)
        (sym (happly
          (ap ∫Hom.fst (pushα .is-natural (suc j) j (δ fzero)))
          TB))
    ∙ ap (λ h → h .∫Hom.fst (G' .F₁ (δ fzero) .∫Hom.fst TB))
        (Surj.ψ-push k' c j i')
    ∙ sym
      ( ap (λ v → C .∂ᶜ j .∫Hom.fst (Surj.ψ k' c (suc j) .∫Hom.fst v))
          rawpush
      ∙ ap (C .∂ᶜ j .∫Hom.fst)
          (ap (λ h → h .∫Hom.fst TB) (Surj.ψ-push k' c (suc j) i'))
      ∙ is-group-hom.pres-id (C .∂ᶜ j .∫Hom.snd))
    where
    Gkk : Functor (Δ ^op) (Ab lzero)
    Gkk = ℤ⟨ Δ[ suc k' ] ⟩

    G' : Functor (Δ ^op) (Ab lzero)
    G' = ℤ⟨ Δ[ k' ] ⟩

    pushα : G' => Gkk
    pushα = Free-abelian-functor ▸ Δmap-nt (δ (fsuc i'))

    TB : ⌞ G' .F₀ (suc j) ⌟
    TB = Tsub G' (suc j) .∫Hom.fst
      (genΔ k' (miss-factor α (fsuc i') m .fst)) .fst

    rawpush
      : Tsub Gkk (suc j) .∫Hom.fst (genΔ (suc k') α) .fst
      ≡ pushα .η (suc j) .∫Hom.fst TB
    rawpush = ap fst (push-Tsub k' α i' m)
  ... | cls-id jk lid = subst
      (λ n → (β : Δ-map (suc n) (suc k'))
           → (∀ x → β .Δ-map.map x .lower ≡ x .lower)
           → Surj.ψ k' c n .∫Hom.fst
               (ℤ⟨ Δ[ suc k' ] ⟩ .F₁ (δ fzero) .∫Hom.fst
                 (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc n) .∫Hom.fst
                   (genΔ (suc k') β) .fst))
           ≡ C .∂ᶜ n .∫Hom.fst
               (Surj.ψ k' c (suc n) .∫Hom.fst
                 (Tsub ℤ⟨ Δ[ suc k' ] ⟩ (suc n) .∫Hom.fst
                   (genΔ (suc k') β) .fst)))
      (sym (ap Nat.pred jk)) top α lid
    where
    Gkk : Functor (Δ ^op) (Ab lzero)
    Gkk = ℤ⟨ Δ[ suc k' ] ⟩

    module Gsk = Abelian-group-on (Gkk .F₀ k' .snd)

    eq₁ : 1 Nat.+ suc k' ≡ suc (suc k')
    eq₁ = sym (Nat.+-sucr 0 (suc k')) ∙ refl

    top : (β : Δ-map (suc k') (suc k'))
        → (∀ x → β .Δ-map.map x .lower ≡ x .lower)
        → Surj.ψ k' c k' .∫Hom.fst
            (Gkk .F₁ (δ fzero) .∫Hom.fst
              (Tsub Gkk (suc k') .∫Hom.fst (genΔ (suc k') β) .fst))
        ≡ C .∂ᶜ k' .∫Hom.fst
            (Surj.ψ k' c (suc k') .∫Hom.fst
              (Tsub Gkk (suc k') .∫Hom.fst (genΔ (suc k') β) .fst))
    top β lidβ =
        ap (λ w → Surj.ψ k' c k' .∫Hom.fst
              (Gkk .F₁ (δ fzero) .∫Hom.fst
                (Tsub Gkk (suc k') .∫Hom.fst (genΔ (suc k') w) .fst)))
          β≡id
      ∙ ap (λ v → Surj.ψ k' c k' .∫Hom.fst
              (Gkk .F₁ (δ fzero) .∫Hom.fst v))
          (ap fst (Tsub-id (suc k')))
      ∙ ap (Surj.ψ k' c k' .∫Hom.fst) (∂-fundamental k')
      ∙ is-group-hom.pres-⋆ (Surj.ψ k' c k' .∫Hom.snd) head-t tail-inv
      ∙ ap₂ (Cc._*_ k')
          head-val
          ( is-group-hom.pres-inv (Surj.ψ k' c k' .∫Hom.snd)
              {x = tail-t}
          ∙ ap (Cc._⁻¹ k')
              (Surj.ψ-Σalt k' c (suc k') 1 eq₁ (Nat.s≤s Nat.0≤x))
          ∙ (sym (Cc.idl k') ∙ Cc.inverser k'))
      ∙ Cc.idr k'
      ∙ sym
        ( ap (λ w → C .∂ᶜ k' .∫Hom.fst
                (Surj.ψ k' c (suc k') .∫Hom.fst
                  (Tsub Gkk (suc k') .∫Hom.fst (genΔ (suc k') w) .fst)))
            β≡id
        ∙ ap (C .∂ᶜ k' .∫Hom.fst) (Surj.ev-comp k' c))
      where
      β≡id : β ≡ Δ .Precategory.id
      β≡id = Δ-map-path λ x →
        fin-ap {n = λ _ → suc (suc k')} (lidβ x)

      bj : 0 Nat.< suc (suc k')
      bj = Nat.s≤s Nat.0≤x

      head-t : ⌞ Gkk .F₀ k' ⌟
      head-t = push-nt k' (fin 0 ⦃ bj ⦄) .η k' .∫Hom.fst
        (fundamental k' .fst)

      tail-t : ⌞ Gkk .F₀ k' ⌟
      tail-t = Σalt k' (suc k') 1 eq₁

      tail-inv : ⌞ Gkk .F₀ k' ⌟
      tail-inv = Gsk._⁻¹ tail-t

      head-val
        : Surj.ψ k' c k' .∫Hom.fst head-t ≡ C .∂ᶜ k' .∫Hom.fst c
      head-val =
          ap (Surj.ψ k' c k' .∫Hom.fst)
            ( ap (push-nt k' (fin 0 ⦃ bj ⦄) .η k' .∫Hom.fst)
                (ap fst (sym (Tsub-id k')))
            ∙ Tsub-natural (push-nt k' (fin 0 ⦃ bj ⦄)) k'
                (genΔ k' (Δ .Precategory.id))
            ∙ ap (λ v → Tsub Gkk k' .∫Hom.fst v .fst)
                ( gen-natural (Δ[ k' ] .F₀ k') (Δ[ suc k' ] .F₀ k')
                    (Δmap-nt (δ (fin 0 ⦃ bj ⦄)) .η k')
                    (Δ .Precategory.id)
                ∙ ap (gen {Δ[ suc k' ] .F₀ k'})
                    (Δ-map-path (λ x → refl))))
        ∙ ev-δ⁰ k' c
  ... | cls-δ⁰ kj lsuc = subst
      (λ m → (c' : ⌞ C .ob (suc m) ⌟)
           → (β : Δ-map (suc j) (suc m))
           → (∀ x → β .Δ-map.map x .lower ≡ suc (x .lower))
           → Surj.ψ m c' j .∫Hom.fst
               (ℤ⟨ Δ[ suc m ] ⟩ .F₁ (δ fzero) .∫Hom.fst
                 (Tsub ℤ⟨ Δ[ suc m ] ⟩ (suc j) .∫Hom.fst
                   (genΔ (suc m) β) .fst))
           ≡ C .∂ᶜ j .∫Hom.fst
               (Surj.ψ m c' (suc j) .∫Hom.fst
                 (Tsub ℤ⟨ Δ[ suc m ] ⟩ (suc j) .∫Hom.fst
                   (genΔ (suc m) β) .fst)))
      (sym (ap Nat.pred kj)) top c α lsuc
    where
    top : (c' : ⌞ C .ob (suc (suc j)) ⌟)
          (β : Δ-map (suc j) (suc (suc j)))
        → (∀ x → β .Δ-map.map x .lower ≡ suc (x .lower))
        → Surj.ψ (suc j) c' j .∫Hom.fst
            (ℤ⟨ Δ[ suc (suc j) ] ⟩ .F₁ (δ fzero) .∫Hom.fst
              (Tsub ℤ⟨ Δ[ suc (suc j) ] ⟩ (suc j) .∫Hom.fst
                (genΔ (suc (suc j)) β) .fst))
        ≡ C .∂ᶜ j .∫Hom.fst
            (Surj.ψ (suc j) c' (suc j) .∫Hom.fst
              (Tsub ℤ⟨ Δ[ suc (suc j) ] ⟩ (suc j) .∫Hom.fst
                (genΔ (suc (suc j)) β) .fst))
    top c' β lsucβ =
        ap (λ v → Surj.ψ (suc j) c' j .∫Hom.fst
              (Gj2 .F₁ (δ fzero) .∫Hom.fst v)) traw-push
      ∙ ap (Surj.ψ (suc j) c' j .∫Hom.fst)
          (sym (happly
            (ap ∫Hom.fst (pushδ₀ .is-natural (suc j) j (δ fzero)))
            (fundamental (suc j) .fst)))
      ∙ ap (λ v → Surj.ψ (suc j) c' j .∫Hom.fst
              (pushδ₀ .η j .∫Hom.fst v))
          (∂-fundamental j)
      ∙ ψδ₀-Σalt j c' (suc (suc j)) 0 refl
      ∙ sym
        ( ap (λ v → C .∂ᶜ j .∫Hom.fst
                (Surj.ψ (suc j) c' (suc j) .∫Hom.fst v)) traw-δ₀
        ∙ ap (C .∂ᶜ j .∫Hom.fst) (ev-δ⁰ (suc j) c')
        ∙ C .∂ᶜ-∂ᶜ j c')
      where
      Gj2 : Functor (Δ ^op) (Ab lzero)
      Gj2 = ℤ⟨ Δ[ suc (suc j) ] ⟩

      Gj1 : Functor (Δ ^op) (Ab lzero)
      Gj1 = ℤ⟨ Δ[ suc j ] ⟩

      pushδ₀ : Gj1 => Gj2
      pushδ₀ = Free-abelian-functor ▸ Δmap-nt (δ fzero)

      β≡δ₀ : β ≡ δ fzero
      β≡δ₀ = Δ-map-path λ x →
        fin-ap {n = λ _ → suc (suc (suc j))} (lsucβ x)

      traw-δ₀
        : Tsub Gj2 (suc j) .∫Hom.fst (genΔ (suc (suc j)) β) .fst
        ≡ Tsub Gj2 (suc j) .∫Hom.fst
            (genΔ (suc (suc j)) (δ fzero)) .fst
      traw-δ₀ = ap (λ w → Tsub Gj2 (suc j) .∫Hom.fst
          (genΔ (suc (suc j)) w) .fst) β≡δ₀

      traw-push
        : Tsub Gj2 (suc j) .∫Hom.fst (genΔ (suc (suc j)) β) .fst
        ≡ pushδ₀ .η (suc j) .∫Hom.fst (fundamental (suc j) .fst)
      traw-push =
          traw-δ₀
        ∙ ap (λ v → Tsub Gj2 (suc j) .∫Hom.fst v .fst)
            ( sym ( gen-natural (Δ[ suc j ] .F₀ (suc j))
                      (Δ[ suc (suc j) ] .F₀ (suc j))
                      (Δmap-nt (δ fzero) .η (suc j))
                      (Δ .Precategory.id)
                  ∙ ap (gen {Δ[ suc (suc j) ] .F₀ (suc j)})
                      (Δ-map-path (λ x → refl))))
        ∙ sym (Tsub-natural pushδ₀ (suc j)
            (genΔ (suc j) (Δ .Precategory.id)))
        ∙ ap (pushδ₀ .η (suc j) .∫Hom.fst)
            (ap fst (Tsub-id (suc j)))
```

## The preimage

The prescription assembles into a normalized chain map evaluating
to the chosen element.

```agda
  φ-of
    : (k' : Nat) (c : ⌞ C .ob (suc k') ⌟)
    → ⌞ MC.Moore (Γ C) .ob (suc k') ⌟
  φ-of k' c = chain , nrm
    where
    Gkk : Functor (Δ ^op) (Ab lzero)
    Gkk = ℤ⟨ Δ[ suc k' ] ⟩

    Tsub-raw : (j : Nat) → Ab lzero .Precategory.Hom (Gkk .F₀ j) (Gkk .F₀ j)
    Tsub-raw j .∫Hom.fst x = Tsub Gkk j .∫Hom.fst x .fst
    Tsub-raw j .∫Hom.snd .is-group-hom.pres-⋆ x y =
      ap fst (is-group-hom.pres-⋆ (Tsub Gkk j .∫Hom.snd) x y)

    incl : (j : Nat)
         → Ab lzero .Precategory.Hom (NΔ (suc k') .ob j) (Gkk .F₀ j)
    incl j .∫Hom.fst = fst
    incl j .∫Hom.snd .is-group-hom.pres-⋆ x y = refl

    chain : Chain-map (NΔ (suc k')) C
    chain .map j =
      Ab lzero .Precategory._∘_ (Surj.ψ k' c j) (incl j)
    chain .comm j (x , p) =
        ap (λ v → Surj.ψ k' c j .∫Hom.fst
              (Gkk .F₁ (δ fzero) .∫Hom.fst v))
          (sym (ap fst (Tsub-fix Gkk (suc j) (x , p))))
      ∙ ap (λ h → h .∫Hom.fst x) LR
      ∙ ap (λ v → C .∂ᶜ j .∫Hom.fst (Surj.ψ k' c (suc j) .∫Hom.fst v))
          (ap fst (Tsub-fix Gkk (suc j) (x , p)))
      where
      L R : Ab lzero .Precategory.Hom (Gkk .F₀ (suc j)) (C .ob j)
      L = Ab lzero .Precategory._∘_ (Surj.ψ k' c j)
        (Ab lzero .Precategory._∘_ (Gkk .F₁ (δ fzero)) (Tsub-raw (suc j)))
      R = Ab lzero .Precategory._∘_ (C .∂ᶜ j)
        (Ab lzero .Precategory._∘_ (Surj.ψ k' c (suc j)) (Tsub-raw (suc j)))

      LR : L ≡ R
      LR = free-ext (Δ[ suc k' ] .F₀ (suc j)) (C .ob j)
        (λ α → square k' c j α)

    nrm : MC.norm (Γ C) (suc k') chain
    nrm i = Chain-map-path λ j → ext λ y q →
      ap (λ h → h .∫Hom.fst y) (Surj.ψ-push k' c j i)

  counit-surj
    : (k' : Nat) (c : ⌞ C .ob (suc k') ⌟)
    → dk-counit-level C (suc k') .∫Hom.fst (φ-of k' c) ≡ c
  counit-surj k' c =
      ap (Surj.ψ k' c (suc k') .∫Hom.fst)
        (ap fst (sym (Tsub-id (suc k'))))
    ∙ Surj.ev-comp k' c
```

In degree zero there is nothing to normalize: the preimage sends
the generating vertex to the element, everything above to zero, and
the only chain condition follows because the level-one part of the
linearised point is retracted onto by a degeneracy.

```agda
  φ-of₀ : (c : ⌞ C .ob 0 ⌟) → ⌞ MC.Moore (Γ C) .ob 0 ⌟
  φ-of₀ c = chain , lift tt
    where
    G0 : Functor (Δ ^op) (Ab lzero)
    G0 = ℤ⟨ Δ[ 0 ] ⟩

    s₀d₁-id
      : Ab lzero .Precategory._∘_ (G0 .F₁ (σ fzero))
          (G0 .F₁ (δ (fsuc fzero)))
      ≡ Ab lzero .Precategory.id
    s₀d₁-id = free-ext (Δ[ 0 ] .F₀ 1) (G0 .F₀ 1) λ u →
        ap (G0 .F₁ (σ fzero) .∫Hom.fst)
          (gen-natural (Δ[ 0 ] .F₀ 1) (Δ[ 0 ] .F₀ 0)
            (Δ[ 0 ] .F₁ (δ (fsuc fzero))) u)
      ∙ gen-natural (Δ[ 0 ] .F₀ 0) (Δ[ 0 ] .F₀ 1)
          (Δ[ 0 ] .F₁ (σ fzero)) (u ∘Δ δ (fsuc fzero))
      ∙ ap (gen {Δ[ 0 ] .F₀ 1})
          (Δ-map-path λ x → Fin1-path _ _)

    lvl1-trivial
      : (x : ⌞ G0 .F₀ 1 ⌟)
      → ((i : Fin 1) → G0 .F₁ (δ (fsuc i)) .∫Hom.fst x
          ≡ Abelian-group-on.1g (G0 .F₀ 0 .snd))
      → x ≡ Abelian-group-on.1g (G0 .F₀ 1 .snd)
    lvl1-trivial x p =
        sym (ap (λ h → h .∫Hom.fst x) s₀d₁-id)
      ∙ ap (G0 .F₁ (σ fzero) .∫Hom.fst) (p fzero)
      ∙ is-group-hom.pres-id (G0 .F₁ (σ fzero) .∫Hom.snd)

    chain : Chain-map (NΔ 0) C
    chain .map zero = Ab lzero .Precategory._∘_
      (R-adjunct adj {a = Δ[ 0 ] .F₀ 0} {b = C .ob 0} (λ _ → c))
      incl0
      where
      incl0 : Ab lzero .Precategory.Hom (NΔ 0 .ob 0) (G0 .F₀ 0)
      incl0 .∫Hom.fst = fst
      incl0 .∫Hom.snd .is-group-hom.pres-⋆ x y = refl
    chain .map (suc j) = zero-hom'
    chain .comm zero (x , p) =
        ap (λ v → R-adjunct adj {a = Δ[ 0 ] .F₀ 0} {b = C .ob 0}
              (λ _ → c) .∫Hom.fst
              (G0 .F₁ (δ fzero) .∫Hom.fst v))
          (lvl1-trivial x p)
      ∙ ap (R-adjunct adj {a = Δ[ 0 ] .F₀ 0} {b = C .ob 0}
              (λ _ → c) .∫Hom.fst)
          (is-group-hom.pres-id (G0 .F₁ (δ fzero) .∫Hom.snd))
      ∙ is-group-hom.pres-id
          (R-adjunct adj {a = Δ[ 0 ] .F₀ 0} {b = C .ob 0}
            (λ _ → c) .∫Hom.snd)
      ∙ sym (is-group-hom.pres-id (C .∂ᶜ 0 .∫Hom.snd))
    chain .comm (suc j) (x , p) =
      sym (is-group-hom.pres-id (C .∂ᶜ (suc j) .∫Hom.snd))

  counit-surj₀
    : (c : ⌞ C .ob 0 ⌟)
    → dk-counit-level C 0 .∫Hom.fst (φ-of₀ c) ≡ c
  counit-surj₀ c = ev-gen (Δ[ 0 ] .F₀ 0) (C .ob 0) (λ _ → c)
    (Δ .Precategory.id)
```

## The counit is an isomorphism, levelwise

```agda
  counit-inverse : (k : Nat) → ⌞ C .ob k ⌟ → ⌞ MC.Moore (Γ C) .ob k ⌟
  counit-inverse zero c = φ-of₀ c
  counit-inverse (suc k') c = φ-of k' c

  counit-rinv
    : (k : Nat) (c : ⌞ C .ob k ⌟)
    → dk-counit-level C k .∫Hom.fst (counit-inverse k c) ≡ c
  counit-rinv zero c = counit-surj₀ c
  counit-rinv (suc k') c = counit-surj k' c

  counit-linv
    : (k : Nat) (φn : ⌞ MC.Moore (Γ C) .ob k ⌟)
    → counit-inverse k (dk-counit-level C k .∫Hom.fst φn) ≡ φn
  counit-linv k φn =
      sym (MΓ.idr k {x = iv})
    ∙ ap (MΓ._*_ k iv) (sym (MΓ.inversel k {x = φn}))
    ∙ MΓ.associative k {x = iv} {y = MΓ._⁻¹ k φn} {z = φn}
    ∙ ap (λ z → MΓ._*_ k z φn) diff-kill
    ∙ MΓ.idl k {x = φn}
    where
    iv : ⌞ MC.Moore (Γ C) .ob k ⌟
    iv = counit-inverse k (dk-counit-level C k .∫Hom.fst φn)

    diff : ⌞ MC.Moore (Γ C) .ob k ⌟
    diff = MΓ._*_ k iv (MΓ._⁻¹ k φn)

    ε-diff : dk-counit-level C k .∫Hom.fst diff ≡ Cc.1g k
    ε-diff =
        is-group-hom.pres-⋆ (dk-counit-level C k .∫Hom.snd) iv
          (MΓ._⁻¹ k φn)
      ∙ ap₂ (Cc._*_ k)
          (counit-rinv k (dk-counit-level C k .∫Hom.fst φn))
          (is-group-hom.pres-inv (dk-counit-level C k .∫Hom.snd)
            {x = φn})
      ∙ Cc.inverser k

    diff-kill : diff ≡ MΓ.1g k
    diff-kill = counit-inj k diff ε-diff
```
