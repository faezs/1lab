<!--
```agda
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Functor.Adjoint
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin
open import Data.Sum

import Algebra.ChainComplex.Moore
import Data.Nat as Nat

open Chain-complex
open Functor
open _=>_
open _⊣_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Fundamental where
```

# The normalization operator and the fundamental class

The [[Moore complex|moore-complex]] of a simplicial abelian group
consists of the simplices whose faces — all but the zeroth — vanish.
Not every simplex is of this form, but every simplex can be
*corrected* to one: subtracting the degenerate correction
$s_{c-1} d_c\, x$ kills the $c$-th face, and walking the faces from
the top down (the same descending pass as the [[Moore filler
|kan-condition]], with the group unit in place of the horn) yields
the **normalization operator**. Applied to the identity simplex it
produces the **fundamental class** $e_k \in N\bZ[\Delta^k]_k$, the
normalized avatar of the generating simplex, which is the engine of
the Dold–Kan counit.

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore

  ¬sucx≤x : ∀ {x} → ¬ (suc x Nat.≤ x)
  ¬sucx≤x {zero}  le = Nat.¬suc≤0 le
  ¬sucx≤x {suc x} le = ¬sucx≤x (Nat.≤-peel le)

  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)

  fin-path : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
  fin-path {n} = fin-ap {n = λ _ → n}

  pred-fin
    : ∀ {n} (F : Fin (suc n)) → 0 Nat.< F .lower
    → Σ[ P ∈ Fin n ] (F .lower ≡ suc (P .lower))
  pred-fin {n} F pos = go (F .lower) (F .Fin.bounded) pos
    where
    go : (l : Nat) → l Nat.< suc n → 0 Nat.< l → Σ[ P ∈ Fin n ] (l ≡ suc (P .lower))
    go zero    _  p = absurd (Nat.¬suc≤0 p)
    go (suc l) bd _ = fin l ⦃ Nat.≤-peel bd ⦄ , refl
```
-->

## The descending correction pass

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  normalize-desc
    : {m₀ : Nat} (fuel c : Nat)
    → c Nat.+ fuel ≡ suc (suc (suc m₀)) → 0 Nat.< c
    → (x : ⌞ G.₀ (suc (suc m₀)) ⌟)
    → Σ[ y ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
        (∀ i → c Nat.≤ i .lower → d i y ≡ Gr.1g (suc m₀))
  normalize-desc zero c eq pos x = x , λ i ge →
    absurd (¬sucx≤x (Nat.≤-trans (i .Fin.bounded)
      (subst (Nat._≤ i .lower) (sym (Nat.+-zeror c) ∙ eq) ge)))
  normalize-desc (suc fuel) zero eq pos x = absurd (Nat.¬suc≤0 pos)
  normalize-desc {m₀} (suc fuel) (suc c₀) eq pos x =
    step (normalize-desc fuel (suc (suc c₀))
      (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x)
    where
    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄

    step
      : Σ[ y ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
          (∀ i → suc (suc c₀) Nat.≤ i .lower → d i y ≡ Gr.1g (suc m₀))
      → Σ[ y ∈ ⌞ G.₀ (suc (suc m₀)) ⌟ ]
          (∀ i → suc c₀ Nat.≤ i .lower → d i y ≡ Gr.1g (suc m₀))
    step (y , fix) = z , fix'
      where
      z : ⌞ G.₀ (suc (suc m₀)) ⌟
      z = Gr._*_ (suc (suc m₀)) y (Gr._⁻¹ (suc (suc m₀)) (s Jf (d Ff y)))

      face-split
        : ∀ i → d i z ≡ Gr._*_ (suc m₀) (d i y) (Gr._⁻¹ (suc m₀) (d i (s Jf (d Ff y))))
      face-split i =
          d-⋆ i y (Gr._⁻¹ (suc (suc m₀)) (s Jf (d Ff y)))
        ∙ ap (Gr._*_ (suc m₀) (d i y)) (d-inv i (s Jf (d Ff y)))

      fix' : ∀ i → suc c₀ Nat.≤ i .lower → d i z ≡ Gr.1g (suc m₀)
      fix' i ge with Nat.≤-split (i .lower) (suc c₀)
      ... | inl lt = absurd (¬sucx≤x (Nat.≤-trans lt ge))
      ... | inr (inr i≡F) =
          ap (λ w → d w z) (fin-path {x = i} {y = Ff} i≡F)
        ∙ face-split Ff
        ∙ ap (λ w → Gr._*_ (suc m₀) (d Ff y) (Gr._⁻¹ (suc m₀) w))
            (d-s-id Ff Jf (inr refl) (d Ff y))
        ∙ Gr.inverser (suc m₀)
      ... | inr (inl gt) =
          face-split i
        ∙ ap₂ (λ u w → Gr._*_ (suc m₀) u (Gr._⁻¹ (suc m₀) w))
            (fix i gt)
            ( d-s-comm-above i Jf i₁ Jd pi refl gt (d Ff y)
            ∙ ap (s Jd) ( d-d-comm Ff i₁ i I₂x refl pi
                            (Nat.≤-peel (subst (suc (suc c₀) Nat.≤_) pi gt)) y
                        ∙ ap (d I₂x) (fix i gt)
                        ∙ is-group-hom.pres-id (G.₁ (δ I₂x) .snd))
            ∙ s-1 Jd )
        ∙ Gr.inverser (suc m₀)
        where
        i₁ : Fin (suc (suc m₀))
        i₁ = pred-fin i (Nat.≤-trans (Nat.s≤s Nat.0≤x) gt) .fst
        pi : i .lower ≡ suc (i₁ .lower)
        pi = pred-fin i (Nat.≤-trans (Nat.s≤s Nat.0≤x) gt) .snd
        bJd : suc c₀ Nat.≤ suc m₀
        bJd = Nat.≤-peel (Nat.≤-trans gt (Nat.≤-peel (i .Fin.bounded)))
        Jd : Fin (suc m₀)
        Jd = fin c₀ ⦃ bJd ⦄
        I₂x : Fin (suc (suc m₀))
        I₂x = fin (suc c₀) ⦃ Nat.s≤s bJd ⦄
```

## The fundamental class

Specialising to the linearised standard simplices and starting from
the generating simplex $[\mathrm{id}_k]$ gives the fundamental class.

<!--
```agda
private
  adj : Free-abelian-functor {lzero} ⊣ Ab↪Sets
  adj = Free-abelian⊣Forget

  gen : {T : Set lzero} → ⌞ T ⌟ → ⌞ Free-abelian-functor .F₀ T ⌟
  gen {T} = adj .unit .η T
```
-->

```agda
fundamental : ∀ k → ⌞ NΔ k .ob k ⌟
fundamental zero = gen {Δ[ 0 ] .F₀ 0} (Δ .Precategory.id) , lift tt
fundamental (suc zero) = z , nrm
  where
  open Simplicial-operators ℤ⟨ Δ[ 1 ] ⟩
  x₀ : ⌞ ℤ⟨ Δ[ 1 ] ⟩ .F₀ 1 ⌟
  x₀ = gen {Δ[ 1 ] .F₀ 1} (Δ .Precategory.id)
  z : ⌞ ℤ⟨ Δ[ 1 ] ⟩ .F₀ 1 ⌟
  z = Gr._*_ 1 x₀ (Gr._⁻¹ 1 (s fzero (d (fsuc fzero) x₀)))
  lower0 : (i : Fin 1) → i .lower ≡ 0
  lower0 i with i .lower | i .Fin.bounded
  ... | zero  | _  = refl
  ... | suc l | bd = absurd (Nat.¬suc≤0 (Nat.≤-peel bd))
  nrm : ∀ (i : Fin 1) → d (fsuc i) z ≡ Gr.1g 0
  nrm i =
      d-⋆ (fsuc i) x₀ (Gr._⁻¹ 1 (s fzero (d (fsuc fzero) x₀)))
    ∙ ap (Gr._*_ 0 (d (fsuc i) x₀)) (d-inv (fsuc i) (s fzero (d (fsuc fzero) x₀)))
    ∙ ap (λ w → Gr._*_ 0 (d (fsuc i) x₀) (Gr._⁻¹ 0 w))
        ( d-s-id (fsuc i) fzero
            (inr (ap suc (lower0 i)))
            (d (fsuc fzero) x₀)
        ∙ ap (λ w → d w x₀) (fin-path {x = fsuc fzero} {y = fsuc i} (ap suc (sym (lower0 i)))))
    ∙ Gr.inverser 0 {x = d (fsuc i) x₀}
fundamental (suc (suc m₀)) =
    body .fst
  , λ i → body .snd (fsuc i) (Nat.s≤s Nat.0≤x)
  where
  body = normalize-desc ℤ⟨ Δ[ suc (suc m₀) ] ⟩ (suc (suc m₀)) 1 refl
    (Nat.s≤s Nat.0≤x) (gen {Δ[ suc (suc m₀) ] .F₀ (suc (suc m₀))} (Δ .Precategory.id))
```

With the fundamental class in hand, the levelwise Dold–Kan counit is
evaluation $\varepsilon(\varphi) = \varphi_k(e_k)$; that this
assembles into a chain map — and that unit and counit are inverse
isomorphisms — rests on the combinatorial expansion of the
normalization operator (the normalization theorem), which remains
future work.

## The levelwise counit

Evaluation at the fundamental class gives the counit's components:
a normalized $k$-simplex of $\Gamma(C)$ — a chain map
$N\bZ[\Delta^k] \to C$ killed by the positive faces — evaluates at
$e_k$ to an element of $C_k$, homomorphically.

```agda
dk-counit-level
  : (C : Chain-complex lzero) (k : Nat)
  → Ab lzero .Precategory.Hom
      (Algebra.ChainComplex.Moore.Moore (Γ C) .ob k) (C .ob k)
dk-counit-level C k .fst (φ , _) = φ .Chain-map.map k .fst (fundamental k)
dk-counit-level C k .snd .is-group-hom.pres-⋆ (φ , _) (ψ , _) = refl
```

Assembling these into a chain map requires commuting evaluation past
the boundary: the face identity $d_0 e_{k+1} \equiv
\delta_0 \cdot e_k$ *modulo the images of the positive coface
pushforwards* (which normalized $\varphi$ kills). That combinatorial
expansion of the normalization operator — and with it the
invertibility of both unit and counit — is the normalization
theorem, and remains future work.

## Naturality of the normalization pass

Maps of simplicial abelian groups commute with every face,
degeneracy, and group operation, so they commute with each
correction step and hence with the whole pass. This is the first of
the three lemmas reducing the counit's chain condition to the
combinatorial core.

```agda
module _ {G G' : Functor (Δ ^op) (Ab lzero)} (α : G => G') where
  private
    module S  = Simplicial-operators G
    module S' = Simplicial-operators G'

    αf : ∀ m → ⌞ G .F₀ m ⌟ → ⌞ G' .F₀ m ⌟
    αf m = α .η m .fst

    α-d : ∀ {m} (i : Fin (suc (suc m))) (x : ⌞ G .F₀ (suc m) ⌟)
        → αf m (S.d i x) ≡ S'.d i (αf (suc m) x)
    α-d {m} i x = happly (ap ∫Hom.fst (α .is-natural (suc m) m (δ i))) x

    α-s : ∀ {m} (j : Fin (suc m)) (x : ⌞ G .F₀ m ⌟)
        → αf (suc m) (S.s j x) ≡ S'.s j (αf m x)
    α-s {m} j x = happly (ap ∫Hom.fst (α .is-natural m (suc m) (σ j))) x

  normalize-desc-natural
    : {m₀ : Nat} (fuel c : Nat)
      (eq : c Nat.+ fuel ≡ suc (suc (suc m₀))) (pos : 0 Nat.< c)
      (x : ⌞ G .F₀ (suc (suc m₀)) ⌟)
    → αf (suc (suc m₀)) (normalize-desc G fuel c eq pos x .fst)
    ≡ normalize-desc G' fuel c eq pos (αf (suc (suc m₀)) x) .fst
  normalize-desc-natural zero c eq pos x = refl
  normalize-desc-natural (suc fuel) zero eq pos x = absurd (Nat.¬suc≤0 pos)
  normalize-desc-natural {m₀} (suc fuel) (suc c₀) eq pos x =
      is-group-hom.pres-⋆ (α .η (suc (suc m₀)) .snd) y _
    ∙ ap₂ (Gr'._*_ (suc (suc m₀)))
        rec
        ( is-group-hom.pres-inv (α .η (suc (suc m₀)) .snd)
        ∙ ap (Gr'._⁻¹ (suc (suc m₀)))
            ( α-s Jf (S.d Ff y)
            ∙ ap (S'.s Jf) (α-d Ff y ∙ ap (S'.d Ff) rec)))
    where
    module Gr' (m : Nat) = Abelian-group-on (G' .F₀ m .snd)
    bF : suc (suc c₀) Nat.≤ suc (suc (suc m₀))
    bF = subst (suc (suc c₀) Nat.≤_)
           (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq)
           (Nat.s≤s (le-plus (suc c₀) fuel))
    Ff : Fin (suc (suc (suc m₀)))
    Ff = fin (suc c₀) ⦃ bF ⦄
    Jf : Fin (suc (suc m₀))
    Jf = fin c₀ ⦃ Nat.≤-peel bF ⦄
    y : ⌞ G .F₀ (suc (suc m₀)) ⌟
    y = normalize-desc G fuel (suc (suc c₀))
          (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x .fst
    rec : αf (suc (suc m₀)) y
        ≡ normalize-desc G' fuel (suc (suc c₀))
            (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x)
            (αf (suc (suc m₀)) x) .fst
    rec = normalize-desc-natural fuel (suc (suc c₀))
            (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) (Nat.s≤s Nat.0≤x) x
```
