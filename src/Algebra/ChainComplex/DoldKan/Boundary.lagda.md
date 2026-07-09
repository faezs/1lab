<!--
```agda
open import Cat.Instances.SimplicialSets.Kan
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Displayed.Total
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex.DoldKan.Normalization
open import Algebra.ChainComplex.DoldKan.Fundamental
open import Algebra.ChainComplex.DoldKan
open import Algebra.ChainComplex

open import Data.Fin
open import Data.Sum

import Data.Nat as Nat

open Functor
open _=>_
open _⊣_
```
-->

```agda
module Algebra.ChainComplex.DoldKan.Boundary where
```

# The boundary formula for fundamental classes

This module assembles the telescoping lemmas and the vanishing
theorem $N \cap D = 0$ into the boundary formula for the fundamental
classes,

$$
d_0\, e_{k+1} \;=\; \sum_{i=0}^{k+1} (-1)^i\, \delta_i \cdot e_k,
$$

the combinatorial engine of the Dold–Kan counit. The strategy: both
sides are normalized, their difference is a sum of degeneracies by
the telescoping expansion, so it vanishes.

## Abelian bookkeeping

<!--
```agda
private
  module abl {ℓ} {T : Type ℓ} (AG : Abelian-group-on T) where
    private module A = Abelian-group-on AG

    shuffle4 : ∀ a b u v → A._*_ (A._*_ a b) (A._*_ u v) ≡ A._*_ (A._*_ a u) (A._*_ b v)
    shuffle4 a b u v =
        sym A.associative
      ∙ ap (A._*_ a) (A.associative ∙ ap (λ z → A._*_ z v) A.commutes ∙ sym A.associative)
      ∙ A.associative

    inv-distr : ∀ a b → A._⁻¹ (A._*_ a b) ≡ A._*_ (A._⁻¹ a) (A._⁻¹ b)
    inv-distr a b =
        sym A.idl
      ∙ ap (λ z → A._*_ z (A._⁻¹ (A._*_ a b))) lem
      ∙ sym A.associative
      ∙ ap (A._*_ (A._*_ (A._⁻¹ a) (A._⁻¹ b))) A.inverser
      ∙ A.idr
      where
      lem : A.1g ≡ A._*_ (A._*_ (A._⁻¹ a) (A._⁻¹ b)) (A._*_ a b)
      lem = sym A.inversel
          ∙ ap (λ z → A._*_ z b)
              ( sym A.idr
              ∙ ap (A._*_ (A._⁻¹ b)) (sym A.inversel)
              ∙ A.associative
              ∙ ap (λ z → A._*_ z a) A.commutes)
          ∙ sym A.associative

    inv-1g : A._⁻¹ A.1g ≡ A.1g
    inv-1g = sym A.idl ∙ A.inverser

    cancel-eq : ∀ a b → A._*_ a (A._⁻¹ b) ≡ A.1g → a ≡ b
    cancel-eq a b p =
        sym A.idr
      ∙ ap (A._*_ a) (sym A.inversel)
      ∙ A.associative
      ∙ ap (λ z → A._*_ z b) p
      ∙ A.idl

    inv-inv : ∀ a → A._⁻¹ (A._⁻¹ a) ≡ a
    inv-inv a = cancel-eq _ _ A.inversel

    inv-flip : ∀ a b → A._⁻¹ (A._*_ a (A._⁻¹ b)) ≡ A._*_ b (A._⁻¹ a)
    inv-flip a b =
        inv-distr a (A._⁻¹ b)
      ∙ ap (A._*_ (A._⁻¹ a)) (inv-inv b)
      ∙ A.commutes

    pass-diff : ∀ a b w
      → A._*_ (A._*_ a (A._⁻¹ w)) (A._⁻¹ (A._*_ b (A._⁻¹ w)))
      ≡ A._*_ a (A._⁻¹ b)
    pass-diff a b w =
        ap (A._*_ (A._*_ a (A._⁻¹ w))) (inv-flip b w)
      ∙ sym A.associative
      ∙ ap (A._*_ a)
          (A.associative ∙ ap (λ z → A._*_ z (A._⁻¹ b)) A.inversel ∙ A.idl)

    rearr : ∀ a b p t
      → A._*_ (A._*_ a (A._⁻¹ b)) (A._⁻¹ (A._*_ p (A._⁻¹ t)))
      ≡ A._*_ (A._*_ a (A._⁻¹ p)) (A._⁻¹ (A._*_ b (A._⁻¹ t)))
    rearr a b p t =
        ap (A._*_ (A._*_ a (A._⁻¹ b))) (inv-flip p t)
      ∙ shuffle4 a (A._⁻¹ b) t (A._⁻¹ p)
      ∙ ap (A._*_ (A._*_ a t)) A.commutes
      ∙ sym (shuffle4 a (A._⁻¹ p) t (A._⁻¹ b))
      ∙ ap (A._*_ (A._*_ a (A._⁻¹ p))) (sym (inv-flip b t))

  ¬sucx≤x : ∀ {x} → ¬ (suc x Nat.≤ x)
  ¬sucx≤x {zero}  le = Nat.¬suc≤0 le
  ¬sucx≤x {suc x} le = ¬sucx≤x (Nat.≤-peel le)

  le0 : ∀ {x} → x Nat.≤ 0 → x ≡ 0
  le0 {zero}  _  = refl
  le0 {suc x} le = absurd (Nat.¬suc≤0 le)

  le-plus : ∀ x y → x Nat.≤ x Nat.+ y
  le-plus zero    y = Nat.0≤x
  le-plus (suc x) y = Nat.s≤s (le-plus x y)
```
-->

## Closure properties of degenerate representations

Bounded-degenerate representations are closed under the group unit,
padding to a larger bound, sums, inverses, single degeneracies, and
pushforward along maps of simplicial abelian groups.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  module _ {m : Nat} where
    private
      module Gsm = Abelian-group-on (G .F₀ (suc m) .snd)
      module Gm  = Abelian-group-on (G .F₀ m .snd)
      module A+  = abl (G .F₀ (suc m) .snd)
      module Am  = abl (G .F₀ m .snd)

    deg-unit : (j : Nat) → j Nat.< suc m → Deg G {m} j Gsm.1g
    deg-unit zero _ = Gm.1g , sym (is-group-hom.pres-id (G .F₁ (σ fzero) .snd))
    deg-unit (suc j) b =
        b , Gm.1g , Gsm.1g , deg-unit j (Nat.<-weaken b)
      , ( sym Gsm.idr
        ∙ ap (Gsm._*_ Gsm.1g)
            (sym (is-group-hom.pres-id (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-pad
      : (j : Nat) (b : suc j Nat.< suc m) {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} (suc j) x
    deg-pad j b {x} dx =
        b , Gm.1g , x , dx
      , ( sym Gsm.idr
        ∙ ap (Gsm._*_ x)
            (sym (is-group-hom.pres-id (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-pad-≤
      : (j j' : Nat) → j Nat.≤ j' → j' Nat.< suc m
      → {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j' x
    deg-pad-≤ j zero le b {x} dx =
      subst (λ z → Deg G {m} z x) (le0 le) dx
    deg-pad-≤ j (suc j') le b {x} dx with Nat.≤-split j (suc j')
    ... | inl j<sj' = deg-pad j' b (deg-pad-≤ j j' (Nat.≤-peel j<sj') (Nat.<-weaken b) dx)
    ... | inr (inl sj'<j) = absurd (¬sucx≤x (Nat.≤-trans sj'<j le))
    ... | inr (inr j≡sj') = subst (λ z → Deg G {m} z x) j≡sj' dx

    deg-sum
      : (j : Nat) {x y : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j y → Deg G {m} j (Gsm._*_ x y)
    deg-sum zero {x} {y} (a , p) (b , q) =
        Gm._*_ a b
      , ( ap₂ Gsm._*_ p q
        ∙ sym (is-group-hom.pres-⋆ (G .F₁ (σ fzero) .snd) a b))
    deg-sum (suc j) {x} {y} (b , a , x' , dx' , p) (b' , c , y' , dy' , q) =
        b , Gm._*_ a c , Gsm._*_ x' y'
      , deg-sum j dx' dy'
      , ( ap₂ Gsm._*_ p (q ∙ ap (Gsm._*_ y')
            (ap (λ z → s z c) (fin-path' {x = fin (suc j) ⦃ b' ⦄} {y = fin (suc j) ⦃ b ⦄} refl)))
        ∙ A+.shuffle4 x' _ y' _
        ∙ ap (Gsm._*_ (Gsm._*_ x' y'))
            (sym (is-group-hom.pres-⋆ (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd) a c)))
      where
      fin-path' : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
      fin-path' {n} = fin-ap {n = λ _ → n}

    deg-inv
      : (j : Nat) {x : ⌞ G .F₀ (suc m) ⌟}
      → Deg G {m} j x → Deg G {m} j (Gsm._⁻¹ x)
    deg-inv zero {x} (a , p) =
        Gm._⁻¹ a
      , ( ap Gsm._⁻¹ p
        ∙ sym (is-group-hom.pres-inv (G .F₁ (σ fzero) .snd)))
    deg-inv (suc j) {x} (b , a , x' , dx' , p) =
        b , Gm._⁻¹ a , Gsm._⁻¹ x'
      , deg-inv j dx'
      , ( ap Gsm._⁻¹ p
        ∙ A+.inv-distr x' _
        ∙ ap (Gsm._*_ (Gsm._⁻¹ x'))
            (sym (is-group-hom.pres-inv (G .F₁ (σ (fin (suc j) ⦃ b ⦄)) .snd))))

    deg-single
      : (i : Nat) (bi : i Nat.< suc m) (y : ⌞ G .F₀ m ⌟)
      → Deg G {m} i (s (fin i ⦃ bi ⦄) y)
    deg-single zero bi y = y , refl
    deg-single (suc i) bi y =
        bi , y , Gsm.1g , deg-unit i (Nat.<-weaken bi)
      , sym Gsm.idl
```

Pushforward: maps of simplicial abelian groups preserve
bounded-degenerate representations.

```agda
module _ {G G' : Functor (Δ ^op) (Ab lzero)} (α : G => G') where
  private
    module S  = Simplicial-operators G
    module S' = Simplicial-operators G'

  deg-push
    : {m : Nat} (j : Nat) {x : ⌞ G .F₀ (suc m) ⌟}
    → Deg G {m} j x → Deg G' {m} j (α .η (suc m) .fst x)
  deg-push {m} zero {x} (a , p) =
      α .η m .fst a
    , ( ap (α .η (suc m) .fst) p
      ∙ happly (ap ∫Hom.fst (α .is-natural m (suc m) (σ fzero))) a)
  deg-push {m} (suc j) {x} (b , a , x' , dx' , p) =
      b , α .η m .fst a , α .η (suc m) .fst x'
    , deg-push j dx'
    , ( ap (α .η (suc m) .fst) p
      ∙ is-group-hom.pres-⋆ (α .η (suc m) .snd) x' _
      ∙ ap (Abelian-group-on._*_ (G' .F₀ (suc m) .snd) (α .η (suc m) .fst x'))
          (happly (ap ∫Hom.fst (α .is-natural m (suc m) (σ (fin (suc j) ⦃ b ⦄)))) a))
```

## The defect of the pass is degenerate

Successive partial passes on the same simplex differ by a sum of
degeneracies: each correction step subtracts a single degeneracy.

```agda
module _ (G : Functor (Δ ^op) (Ab lzero)) where
  open Simplicial-operators G

  pass-defect
    : {m₀ : Nat} (fuel c₀ : Nat)
      (eq : suc c₀ Nat.+ fuel ≡ suc (suc (suc m₀)))
      (x : ⌞ G .F₀ (suc (suc m₀)) ⌟)
    → Deg G {suc m₀} (suc m₀)
        (Abelian-group-on._*_ (G .F₀ (suc (suc m₀)) .snd)
          (normalize-desc G fuel (suc c₀) eq (Nat.s≤s Nat.0≤x) x .fst)
          (Abelian-group-on._⁻¹ (G .F₀ (suc (suc m₀)) .snd) x))
  pass-defect {m₀} zero c₀ eq x =
    subst (Deg G {suc m₀} (suc m₀)) (sym Gsm.inverser)
      (deg-unit G (suc m₀) Nat.≤-refl)
    where module Gsm = Abelian-group-on (G .F₀ (suc (suc m₀)) .snd)
  pass-defect {m₀} (suc fuel) c₀ eq x =
    subst (Deg G {suc m₀} (suc m₀)) path combined
    where
    module Gsm = Abelian-group-on (G .F₀ (suc (suc m₀)) .snd)
    module A+ = abl (G .F₀ (suc (suc m₀)) .snd)

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

    corr : ⌞ G .F₀ (suc (suc m₀)) ⌟
    corr = s Jf (d Ff y)

    rec : Deg G {suc m₀} (suc m₀) (Gsm._*_ y (Gsm._⁻¹ x))
    rec = pass-defect fuel (suc c₀) (sym (Nat.+-sucr (suc c₀) fuel) ∙ eq) x

    corr-deg : Deg G {suc m₀} (suc m₀) (Gsm._⁻¹ corr)
    corr-deg = deg-inv G (suc m₀)
      (deg-pad-≤ G c₀ (suc m₀) (Nat.≤-peel (Nat.≤-peel bF)) Nat.≤-refl
        (deg-single G c₀ (Nat.≤-peel bF) (d Ff y)))

    combined : Deg G {suc m₀} (suc m₀)
      (Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ x)) (Gsm._⁻¹ corr))
    combined = deg-sum G (suc m₀) rec corr-deg

    path : Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ x)) (Gsm._⁻¹ corr)
         ≡ Gsm._*_ (Gsm._*_ y (Gsm._⁻¹ corr)) (Gsm._⁻¹ x)
    path = sym Gsm.associative
         ∙ ap (Gsm._*_ y) Gsm.commutes
         ∙ Gsm.associative
```

## The alternating sum of pushforwards

<!--
```agda
private
  adj : Free-abelian-functor {lzero} ⊣ Ab↪Sets
  adj = Free-abelian⊣Forget

  gen : {T : Set lzero} → ⌞ T ⌟ → ⌞ Free-abelian-functor .F₀ T ⌟
  gen {T} = adj .unit .η T

  gen-nat
    : {T T' : Set lzero} (f : ⌞ T ⌟ → ⌞ T' ⌟) (x : ⌞ T ⌟)
    → Free-abelian-functor .F₁ {T} {T'} f .fst (gen {T} x) ≡ gen {T'} (f x)
  gen-nat {T} {T'} f x = sym (happly (adj .unit .is-natural T T' f) x)

  pred-fin
    : ∀ {n} (F : Fin (suc n)) → 0 Nat.< F .lower
    → Σ[ P ∈ Fin n ] (F .lower ≡ suc (P .lower))
  pred-fin {n} F pos = go (F .lower) (F .Fin.bounded) pos
    where
    go : (l : Nat) → l Nat.< suc n → 0 Nat.< l → Σ[ P ∈ Fin n ] (l ≡ suc (P .lower))
    go zero    _  p = absurd (Nat.¬suc≤0 p)
    go (suc l) bd _ = fin l ⦃ Nat.≤-peel bd ⦄ , refl

  fin-path : ∀ {n} {x y : Fin n} → x .lower ≡ y .lower → x ≡ y
  fin-path {n} = fin-ap {n = λ _ → n}
```
-->

The right-hand side of the boundary formula, defined by recursion —
the alternation is carried by the inverse in each step.

```agda
module _ (k : Nat) where
  private
    module Ck = Abelian-group-on (ℤ⟨ Δ[ suc k ] ⟩ .F₀ k .snd)

  push-nt : (j : Fin (suc (suc k))) → ℤ⟨ Δ[ k ] ⟩ => ℤ⟨ Δ[ suc k ] ⟩
  push-nt j = Free-abelian-functor ▸ Δmap-nt (δ j)

  Σalt : (fuel j : Nat) → j Nat.+ fuel ≡ suc (suc k)
       → ⌞ ℤ⟨ Δ[ suc k ] ⟩ .F₀ k ⌟
  Σalt zero j eq = Ck.1g
  Σalt (suc fuel) j eq = Ck._*_
    (push-nt (fin j ⦃ bj ⦄) .η k .fst (fundamental k .fst))
    (Ck._⁻¹ (Σalt fuel (suc j) (sym (Nat.+-sucr j fuel) ∙ eq)))
    where
    bj : j Nat.< suc (suc k)
    bj = subst (suc j Nat.≤_) (sym (Nat.+-sucr j fuel) ∙ eq)
           (Nat.s≤s (le-plus j fuel))
```

Every summand is normalized, so the whole sum is.

```agda
module _ (k₁ : Nat) where
  private
    k : Nat
    k = suc k₁
    G+ : Functor (Δ ^op) (Ab lzero)
    G+ = ℤ⟨ Δ[ suc k ] ⟩
    Gk : Functor (Δ ^op) (Ab lzero)
    Gk = ℤ⟨ Δ[ k ] ⟩
    module S+ = Simplicial-operators G+
    module Sk = Simplicial-operators Gk
    module Ck = Abelian-group-on (G+ .F₀ k .snd)
    module Ck- = Abelian-group-on (G+ .F₀ k₁ .snd)

  fundamental-norm-any
    : (i : Fin (suc k)) → 1 Nat.≤ i .lower
    → Sk.d i (fundamental k .fst)
    ≡ Abelian-group-on.1g (Gk .F₀ k₁ .snd)
  fundamental-norm-any i pos =
      ap (λ z → Sk.d z (fundamental k .fst))
        (fin-path {x = i} {y = fsuc (pred-fin i pos .fst)} (pred-fin i pos .snd))
    ∙ fundamental k .snd (pred-fin i pos .fst)

  Σalt-norm
    : (fuel j : Nat) (eq : j Nat.+ fuel ≡ suc (suc k))
      (i : Fin (suc k)) → 1 Nat.≤ i .lower
    → S+.d i (Σalt k fuel j eq) ≡ Ck-.1g
  Σalt-norm zero j eq i pos =
    is-group-hom.pres-id (G+ .F₁ (δ i) .snd)
  Σalt-norm (suc fuel) j eq i pos =
      S+.d-⋆ i
        (push-nt k (fin j ⦃ bj ⦄) .η k .fst (fundamental k .fst))
        (Ck._⁻¹ (Σalt k fuel (suc j) (sym (Nat.+-sucr j fuel) ∙ eq)))
    ∙ ap₂ Ck-._*_
        ( sym (happly (ap ∫Hom.fst
            (push-nt k (fin j ⦃ bj ⦄) .is-natural k k₁ (δ i)))
            (fundamental k .fst))
        ∙ ap (push-nt k (fin j ⦃ bj ⦄) .η k₁ .fst) (fundamental-norm-any i pos)
        ∙ is-group-hom.pres-id (push-nt k (fin j ⦃ bj ⦄) .η k₁ .snd))
        ( S+.d-inv i (Σalt k fuel (suc j) (sym (Nat.+-sucr j fuel) ∙ eq))
        ∙ ap Ck-._⁻¹ (Σalt-norm fuel (suc j) (sym (Nat.+-sucr j fuel) ∙ eq) i pos)
        ∙ abl.inv-1g (G+ .F₀ k₁ .snd))
    ∙ Ck-.idr
    where
    bj : j Nat.< suc (suc k)
    bj = subst (suc j Nat.≤_) (sym (Nat.+-sucr j fuel) ∙ eq)
           (Nat.s≤s (le-plus j fuel))
```

## The telescoping claim

For horn dimension at least two, the telescoping lemmas expand the
boundary of the fundamental class into the alternating sum, modulo
degeneracies.

```agda
module _ (m₀' : Nat) where
  private
    k : Nat
    k = suc (suc m₀')
    G+ Gk : Functor (Δ ^op) (Ab lzero)
    G+ = ℤ⟨ Δ[ suc k ] ⟩
    Gk = ℤ⟨ Δ[ k ] ⟩
    module S+ = Simplicial-operators G+
    module C+ = Abelian-group-on (G+ .F₀ k .snd)
    module A+ = abl (G+ .F₀ k .snd)
    module Agk = abl (Gk .F₀ k .snd)

    idk+ : ⌞ G+ .F₀ (suc k) ⌟
    idk+ = gen {Δ[ suc k ] .F₀ (suc k)} (Δ .Precategory.id)
    idkk : ⌞ Gk .F₀ k ⌟
    idkk = gen {Δ[ k ] .F₀ k} (Δ .Precategory.id)

    face-gen
      : (i : Fin (suc (suc k)))
      → S+.d i idk+ ≡ push-nt k i .η k .fst idkk
    face-gen i =
        gen-nat {Δ[ suc k ] .F₀ (suc k)} {Δ[ suc k ] .F₀ k}
          (Δ[ suc k ] .F₁ (δ i)) (Δ .Precategory.id)
      ∙ ap (gen {Δ[ suc k ] .F₀ k}) (Δ .Precategory.idl (δ i))
      ∙ sym ( gen-nat {Δ[ k ] .F₀ k} {Δ[ suc k ] .F₀ k}
                (Δmap-nt (δ i) .η k) (Δ .Precategory.id)
            ∙ ap (gen {Δ[ suc k ] .F₀ k}) (Δ .Precategory.idr (δ i)))

    push-split
      : (j : Fin (suc (suc k))) (a b : ⌞ Gk .F₀ k ⌟)
      → push-nt k j .η k .fst (Abelian-group-on._*_ (Gk .F₀ k .snd) a
          (Abelian-group-on._⁻¹ (Gk .F₀ k .snd) b))
      ≡ C+._*_ (push-nt k j .η k .fst a) (C+._⁻¹ (push-nt k j .η k .fst b))
    push-split j a b =
        is-group-hom.pres-⋆ (push-nt k j .η k .snd) a
          (Abelian-group-on._⁻¹ (Gk .F₀ k .snd) b)
      ∙ ap (C+._*_ (push-nt k j .η k .fst a))
          (is-group-hom.pres-inv (push-nt k j .η k .snd) {x = b})

    eK : ⌞ Gk .F₀ k ⌟
    eK = fundamental k .fst

  tele
    : (fuel j : Nat)
      (eqP : suc j Nat.+ fuel ≡ suc (suc (suc (suc m₀'))))
      (eqS : j Nat.+ suc fuel ≡ suc (suc (suc (suc m₀'))))
      (bj : j Nat.< suc (suc (suc (suc m₀'))))
    → Deg G+ {suc m₀'} (suc m₀')
        (C+._*_
          (S+.d (fin j ⦃ bj ⦄)
            (normalize-desc G+ fuel (suc j) eqP (Nat.s≤s Nat.0≤x) idk+ .fst))
          (C+._⁻¹ (Σalt k (suc fuel) j eqS)))
  tele zero j eqP eqS bj =
    subst (Deg G+ {suc m₀'} (suc m₀')) (sym whole)
      (subst (Deg G+ {suc m₀'} (suc m₀'))
        (push-split (fin j ⦃ bj ⦄) idkk eK)
        (deg-push (push-nt k (fin j ⦃ bj ⦄)) (suc m₀')
          (subst (Deg Gk {suc m₀'} (suc m₀'))
            (Agk.inv-flip eK idkk)
            (deg-inv Gk (suc m₀')
              (pass-defect Gk (suc (suc m₀')) 0 refl idkk)))))
    where
    PA : ⌞ G+ .F₀ k ⌟
    PA = push-nt k (fin j ⦃ bj ⦄) .η k .fst eK
    Σ1 : Σalt k 1 j eqS ≡ PA
    Σ1 = ap (C+._*_ PA) A+.inv-1g ∙ C+.idr
    whole
      : C+._*_ (S+.d (fin j ⦃ bj ⦄) idk+)
          (C+._⁻¹ (Σalt k 1 j eqS))
      ≡ C+._*_ (push-nt k (fin j ⦃ bj ⦄) .η k .fst idkk) (C+._⁻¹ PA)
    whole = ap₂ C+._*_ (face-gen (fin j ⦃ bj ⦄)) (ap C+._⁻¹ Σ1)
  tele (suc fuel') j eqP eqS bj =
    subst (Deg G+ {suc m₀'} (suc m₀')) (sym (step₁ ∙ step₂))
      (deg-sum G+ (suc m₀') DegFF (deg-inv G+ (suc m₀') IH))
    where
    bsj : suc j Nat.< suc (suc (suc (suc m₀')))
    bsj = subst (suc (suc j) Nat.≤_)
            (sym (Nat.+-sucr (suc j) fuel') ∙ eqP)
            (Nat.s≤s (le-plus (suc j) fuel'))
    eq₂ : suc (suc j) Nat.+ fuel' ≡ suc (suc (suc (suc m₀')))
    eq₂ = sym (Nat.+-sucr (suc j) fuel') ∙ eqP
    eq' : suc j Nat.+ fuel' ≡ suc (suc (suc m₀'))
    eq' = Nat.suc-inj eq₂
    eqS' : suc j Nat.+ suc fuel' ≡ suc (suc (suc (suc m₀')))
    eqS' = sym (Nat.+-sucr j (suc fuel')) ∙ eqS

    Q : ⌞ G+ .F₀ (suc k) ⌟
    Q = normalize-desc G+ fuel' (suc (suc j)) eq₂ (Nat.s≤s Nat.0≤x) idk+ .fst

    Pk' : ⌞ Gk .F₀ k ⌟
    Pk' = normalize-desc Gk fuel' (suc j) eq' (Nat.s≤s Nat.0≤x) idkk .fst

    TB : ⌞ G+ .F₀ k ⌟
    TB = Σalt k (suc fuel') (suc j) eqS'

    B : ⌞ G+ .F₀ k ⌟
    B = S+.d (fin (suc j) ⦃ bsj ⦄) Q

    PAe : ⌞ G+ .F₀ k ⌟
    PAe = push-nt k (fin j ⦃ bj ⦄) .η k .fst eK

    FF-path : S+.d (fin j ⦃ bj ⦄) Q ≡ push-nt k (fin j ⦃ bj ⦄) .η k .fst Pk'
    FF-path =
        pass-pull G+ fuel' j eq₂ eq' (fin j ⦃ bj ⦄) Nat.≤-refl idk+
      ∙ ap (λ w → normalize-desc G+ fuel' (suc j) eq' (Nat.s≤s Nat.0≤x) w .fst)
          (face-gen (fin j ⦃ bj ⦄))
      ∙ sym (normalize-desc-natural (push-nt k (fin j ⦃ bj ⦄)) fuel' (suc j) eq'
          (Nat.s≤s Nat.0≤x) idkk)

    DegGk : Deg Gk {suc m₀'} (suc m₀')
      (Abelian-group-on._*_ (Gk .F₀ k .snd) Pk'
        (Abelian-group-on._⁻¹ (Gk .F₀ k .snd) eK))
    DegGk = subst (Deg Gk {suc m₀'} (suc m₀'))
      (Agk.pass-diff Pk' eK idkk)
      (deg-sum Gk (suc m₀')
        (pass-defect Gk fuel' j eq' idkk)
        (deg-inv Gk (suc m₀') (pass-defect Gk (suc (suc m₀')) 0 refl idkk)))

    DegFF : Deg G+ {suc m₀'} (suc m₀')
      (C+._*_ (S+.d (fin j ⦃ bj ⦄) Q) (C+._⁻¹ PAe))
    DegFF = subst
      (λ z → Deg G+ {suc m₀'} (suc m₀') (C+._*_ z (C+._⁻¹ PAe)))
      (sym FF-path)
      (subst (Deg G+ {suc m₀'} (suc m₀'))
        (push-split (fin j ⦃ bj ⦄) Pk' eK)
        (deg-push (push-nt k (fin j ⦃ bj ⦄)) (suc m₀') DegGk))

    IH : Deg G+ {suc m₀'} (suc m₀') (C+._*_ B (C+._⁻¹ TB))
    IH = tele fuel' (suc j) eq₂ eqS' bsj

    step₁
      : C+._*_
          (S+.d (fin j ⦃ bj ⦄)
            (normalize-desc G+ (suc fuel') (suc j) eqP (Nat.s≤s Nat.0≤x) idk+ .fst))
          (C+._⁻¹ (Σalt k (suc (suc fuel')) j eqS))
      ≡ C+._*_ (C+._*_ (S+.d (fin j ⦃ bj ⦄) Q) (C+._⁻¹ B))
          (C+._⁻¹ (C+._*_ PAe (C+._⁻¹ TB)))
    step₁ = ap (λ z → C+._*_ z (C+._⁻¹ (Σalt k (suc (suc fuel')) j eqS)))
      (boundary-step G+ fuel' j eqP (fin j ⦃ bj ⦄) (fin (suc j) ⦃ bsj ⦄)
        refl refl idk+)

    step₂
      : C+._*_ (C+._*_ (S+.d (fin j ⦃ bj ⦄) Q) (C+._⁻¹ B))
          (C+._⁻¹ (C+._*_ PAe (C+._⁻¹ TB)))
      ≡ C+._*_ (C+._*_ (S+.d (fin j ⦃ bj ⦄) Q) (C+._⁻¹ PAe))
          (C+._⁻¹ (C+._*_ B (C+._⁻¹ TB)))
    step₂ = A+.rearr (S+.d (fin j ⦃ bj ⦄) Q) B PAe TB
```

## The boundary formula

```agda
  boundary-formula
    : S+.d (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄) (fundamental (suc k) .fst)
    ≡ Σalt k (suc (suc k)) 0 refl
  boundary-formula = A+.cancel-eq _ _
    (normalized-degenerate-vanish G+ diff diff-norm (suc m₀') tele₀)
    where
    d₀e : ⌞ G+ .F₀ k ⌟
    d₀e = S+.d (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄) (fundamental (suc k) .fst)
    ΣF : ⌞ G+ .F₀ k ⌟
    ΣF = Σalt k (suc (suc k)) 0 refl
    diff : ⌞ G+ .F₀ k ⌟
    diff = C+._*_ d₀e (C+._⁻¹ ΣF)

    tele₀ : Deg G+ {suc m₀'} (suc m₀') diff
    tele₀ = tele (suc (suc (suc m₀'))) 0 refl refl (Nat.s≤s Nat.0≤x)

    d₀e-norm
      : (i : Fin (suc k)) → 1 Nat.≤ i .lower
      → S+.d i d₀e ≡ Abelian-group-on.1g (G+ .F₀ (suc m₀') .snd)
    d₀e-norm i pos =
        S+.d-d-comm (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄) i
          (fin (suc (i .lower)) ⦃ Nat.s≤s (i .Fin.bounded) ⦄)
          (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄)
          refl refl Nat.0≤x (fundamental (suc k) .fst)
      ∙ ap (S+.d (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄))
          (fundamental-norm-any (suc (suc m₀'))
            (fin (suc (i .lower)) ⦃ Nat.s≤s (i .Fin.bounded) ⦄)
            (Nat.s≤s Nat.0≤x))
      ∙ is-group-hom.pres-id (G+ .F₁ (δ (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄)) .snd)

    diff-norm
      : (i : Fin (suc k)) → 1 Nat.≤ i .lower
      → S+.d i diff ≡ Abelian-group-on.1g (G+ .F₀ (suc m₀') .snd)
    diff-norm i pos =
        S+.d-⋆ i d₀e (C+._⁻¹ ΣF)
      ∙ ap₂ (Abelian-group-on._*_ (G+ .F₀ (suc m₀') .snd))
          (d₀e-norm i pos)
          ( S+.d-inv i ΣF
          ∙ ap (Abelian-group-on._⁻¹ (G+ .F₀ (suc m₀') .snd))
              (Σalt-norm (suc m₀') (suc (suc k)) 0 refl i pos)
          ∙ abl.inv-1g (G+ .F₀ (suc m₀') .snd))
      ∙ Abelian-group-on.idl (G+ .F₀ (suc m₀') .snd)
```

## The low-dimensional cases

The machinery above needs at least two levels of faces below the top;
the two low cases are direct computations. In dimension one the
formula is immediate; in dimension two the corrections of adjacent
pushforwards coincide — $\delta_1 \delta_1 = \delta_2 \delta_1$ — and
cancel exactly.

```agda
boundary-formula₀
  : Simplicial-operators.d ℤ⟨ Δ[ 1 ] ⟩ (fin 0 ⦃ Nat.s≤s Nat.0≤x ⦄)
      (fundamental 1 .fst)
  ≡ Σalt 0 2 0 refl
boundary-formula₀ =
    S.d-⋆ (fin 0) x₀
      (Abelian-group-on._⁻¹ (ℤ⟨ Δ[ 1 ] ⟩ .F₀ 1 .snd)
        (S.s fzero (S.d (fsuc fzero) x₀)))
  ∙ ap₂ C._*_
      (dgen (fin 0))
      ( S.d-inv (fin 0) (S.s fzero (S.d (fsuc fzero) x₀))
      ∙ ap C._⁻¹
          ( S.d-s-id (fin 0) fzero (inl refl) (S.d (fsuc fzero) x₀)
          ∙ dgen (fsuc fzero)))
  ∙ sym Σc
  where
  module S = Simplicial-operators ℤ⟨ Δ[ 1 ] ⟩
  module C = Abelian-group-on (ℤ⟨ Δ[ 1 ] ⟩ .F₀ 0 .snd)
  x₀ : ⌞ ℤ⟨ Δ[ 1 ] ⟩ .F₀ 1 ⌟
  x₀ = gen {Δ[ 1 ] .F₀ 1} (Δ .Precategory.id)

  dgen : (i : Fin 2) → S.d i x₀ ≡ gen {Δ[ 1 ] .F₀ 0} (δ i)
  dgen i =
      gen-nat {Δ[ 1 ] .F₀ 1} {Δ[ 1 ] .F₀ 0} (Δ[ 1 ] .F₁ (δ i)) (Δ .Precategory.id)
    ∙ ap (gen {Δ[ 1 ] .F₀ 0}) (Δ .Precategory.idl (δ i))

  pgen : (i : Fin 2)
       → push-nt 0 i .η 0 .fst (fundamental 0 .fst) ≡ gen {Δ[ 1 ] .F₀ 0} (δ i)
  pgen i =
      gen-nat {Δ[ 0 ] .F₀ 0} {Δ[ 1 ] .F₀ 0} (Δmap-nt (δ i) .η 0) (Δ .Precategory.id)
    ∙ ap (gen {Δ[ 1 ] .F₀ 0}) (Δ .Precategory.idr (δ i))

  tail : Σalt 0 1 1 refl ≡ gen {Δ[ 1 ] .F₀ 0} (δ (fin 1))
  tail =
      ap (C._*_ (push-nt 0 (fin 1 ⦃ Nat.s≤s (Nat.s≤s Nat.0≤x) ⦄) .η 0 .fst
           (fundamental 0 .fst)))
        (abl.inv-1g (ℤ⟨ Δ[ 1 ] ⟩ .F₀ 0 .snd))
    ∙ C.idr
    ∙ pgen (fin 1)

  Σc : Σalt 0 2 0 refl
     ≡ C._*_ (gen {Δ[ 1 ] .F₀ 0} (δ (fin 0)))
         (C._⁻¹ (gen {Δ[ 1 ] .F₀ 0} (δ (fin 1))))
  Σc = ap₂ C._*_ (pgen (fin 0)) (ap C._⁻¹ tail)
```
