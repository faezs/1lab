<!--
```agda
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Simplex
open import Cat.Diagram.Exponential
open import Cat.Functor.Compose
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Algebra.ChainComplex

open import Data.Fin using (Fin ; fzero ; fsuc)

import Algebra.ChainComplex.Moore
import Cat.Reasoning

open Chain-complex
open Chain-map
open make-abelian-group
open Functor
open _=>_
```
-->

```agda
module Algebra.ChainComplex.DoldKan where
```

<!--
```agda
private
  module MC = Algebra.ChainComplex.Moore
  module ChC = Cat.Reasoning (Ch lzero)
  module AbC = Cat.Reasoning (Ab lzero)
```
-->

# The inverse Dold–Kan construction {defines="dold-kan eilenberg-maclane-object"}

The [[Moore complex|moore-complex]] sends a simplicial abelian group
to its chain complex of normalized chains. The Dold–Kan
correspondence says this is an *equivalence*, and this module
constructs the essential ingredient of its inverse: the functor
$\Gamma$ sending a chain complex $C$ to the simplicial abelian group

$$
\Gamma(C)_n = \mathrm{Ch}(N\bZ[\Delta^n],\; C)
$$

of chain maps out of the normalized chains of the standard
simplices. This is Kan's construction presented hom-theoretically:
functoriality in $[n]$ is inherited from functoriality of $N \circ
\bZ[-] \circ \Delta[-]$, so no shuffle combinatorics appear at all.
With $\Gamma$ in hand, the **Eilenberg–MacLane objects** $K(A, n)$ —
the paper's deloopings $\mathbf{B}^n A$, diagram (31) — are the
values of $\Gamma$ on complexes concentrated in a single degree, and
ordinary cohomology is $\pi_0$ of mapping spaces into them.

## Linearising simplicial sets

A simplicial set freely generates a simplicial abelian group,
degreewise.

```agda
ℤ⟨_⟩ : Functor (Δ ^op) (Sets lzero) → Functor (Δ ^op) (Ab lzero)
ℤ⟨ X ⟩ = Free-abelian-functor F∘ X
```

## Functoriality of the Moore complex

A map of simplicial abelian groups restricts to normalized chains —
naturality carries the "all faces vanish" condition across — and
commutes with the boundary, giving a chain map of Moore complexes.

```agda
module _ {A B : Functor (Δ ^op) (Ab lzero)} (α : A => B) where
  private
    module A = Functor A
    module B = Functor B
    module MA = Algebra.ChainComplex.Moore A
    module MB = Algebra.ChainComplex.Moore B

    αf : ∀ n → ⌞ A.₀ n ⌟ → ⌞ B.₀ n ⌟
    αf n = α .η n .fst

  private abstract
    norm-pres : ∀ n a → MA.norm n a → MB.norm n (αf n a)
    norm-pres zero a p = lift tt
    norm-pres (suc n) a p = λ i →
        sym (happly (ap ∫Hom.fst (α .is-natural (suc n) n (δ (fsuc i)))) a)
      ∙ ap (αf n) (p i)
      ∙ is-group-hom.pres-id (α .η n .snd)

  moore-map : Chain-map MA.Moore MB.Moore
  moore-map .map n .∫Hom.fst (a , p) = αf n a , norm-pres n a p
  moore-map .map n .∫Hom.snd .is-group-hom.pres-⋆ (a , p) (b , q) =
    Σ-prop-path (MB.norm-is-prop n)
      (is-group-hom.pres-⋆ (α .η n .snd) a b)
  moore-map .comm n (a , p) = Σ-prop-path (MB.norm-is-prop n)
    (happly (ap ∫Hom.fst (α .is-natural (suc n) n (δ fzero))) a)
```

<!--
```agda
private abstract
  moore-map-id
    : {A : Functor (Δ ^op) (Ab lzero)}
    → moore-map (idnt {F = A}) ≡ ChC.id {MC.Moore A}
  moore-map-id {A} = Chain-map-path λ n → ext λ x p →
    Σ-prop-path (MC.norm-is-prop A n) refl

  moore-map-∘
    : {A B C : Functor (Δ ^op) (Ab lzero)}
    → (β : B => C) (α : A => B)
    → moore-map (β ∘nt α)
    ≡ ChC._∘_ {MC.Moore A} {MC.Moore B} {MC.Moore C}
        (moore-map β) (moore-map α)
  moore-map-∘ {A} {B} {C} β α = Chain-map-path λ n → ext λ x p →
    Σ-prop-path (MC.norm-is-prop C n) refl
```
-->

## The chains of the standard simplices

Postcomposition makes the representable $\Delta[-]$ covariant in
its dimension; linearising and taking Moore complexes gives the
chain complexes $N\bZ[\Delta^n]$, functorially.

```agda
Δmap-nt : ∀ {m n} → Δ-map m n → (Δ[ m ] => Δ[ n ])
Δmap-nt g .η k h = g ∘Δ h
Δmap-nt g .is-natural k k' f = funext λ h → Δ .Precategory.assoc g h f

NΔ : Nat → Chain-complex lzero
NΔ n = MC.Moore ℤ⟨ Δ[ n ] ⟩

NΔ-map : ∀ {m n} → Δ-map m n → Chain-map (NΔ m) (NΔ n)
NΔ-map g = moore-map (Free-abelian-functor ▸ Δmap-nt g)
```

<!--
```agda
private abstract
  NΔ-map-id : ∀ {n} → NΔ-map {n} {n} (Δ .Precategory.id {n}) ≡ ChC.id {NΔ n}
  NΔ-map-id {n} =
      ap (moore-map {ℤ⟨ Δ[ n ] ⟩} {ℤ⟨ Δ[ n ] ⟩}) fixup
    ∙ moore-map-id {A = ℤ⟨ Δ[ n ] ⟩}
    where
    fixup
      : (Free-abelian-functor ▸ Δmap-nt (Δ .Precategory.id {n}))
      ≡ idnt {F = ℤ⟨ Δ[ n ] ⟩}
    fixup = Nat-path λ k →
        ap (λ f → Free-abelian-functor .F₁ {Δ[ n ] .F₀ k} {Δ[ n ] .F₀ k} f)
          (funext λ h → Δ .Precategory.idl h)
      ∙ Free-abelian-functor .F-id {Δ[ n ] .F₀ k}

  NΔ-map-∘
    : ∀ {m n k} (g : Δ-map n k) (f : Δ-map m n)
    → NΔ-map (g ∘Δ f)
    ≡ ChC._∘_ {NΔ m} {NΔ n} {NΔ k} (NΔ-map g) (NΔ-map f)
  NΔ-map-∘ {m} {n} {k} g f =
      ap (moore-map {ℤ⟨ Δ[ m ] ⟩} {ℤ⟨ Δ[ k ] ⟩}) fixup
    ∙ moore-map-∘ {ℤ⟨ Δ[ m ] ⟩} {ℤ⟨ Δ[ n ] ⟩} {ℤ⟨ Δ[ k ] ⟩}
        (Free-abelian-functor ▸ Δmap-nt g)
        (Free-abelian-functor ▸ Δmap-nt f)
    where
    fixup
      : (Free-abelian-functor ▸ Δmap-nt (g ∘Δ f))
      ≡ (Free-abelian-functor ▸ Δmap-nt g) ∘nt (Free-abelian-functor ▸ Δmap-nt f)
    fixup = Nat-path λ j →
        ap (λ w → Free-abelian-functor .F₁ {Δ[ m ] .F₀ j} {Δ[ k ] .F₀ j} w)
          (funext λ h → sym (Δ .Precategory.assoc g f h))
      ∙ Free-abelian-functor .F-∘ {Δ[ m ] .F₀ j} {Δ[ n ] .F₀ j} {Δ[ k ] .F₀ j} (Δmap-nt g .η j) (Δmap-nt f .η j)
```
-->

## Hom-groups of chain maps

Chain maps into a fixed complex add pointwise, so the hom-sets of
`Ch`{.Agda} are abelian groups — the enrichment through which
$\Gamma$ lands in simplicial abelian groups rather than mere
simplicial sets.

```agda
Chain-hom-ab : (A B : Chain-complex lzero) → Abelian-group lzero
Chain-hom-ab A B = to-ab mk where
```

<!--
```agda
  module B (n : Nat) = Abelian-group-on (B .ob n .snd)

  module H (n : Nat) =
    Abelian-group-on (Abelian-group-on-hom (A .ob n) (B .ob n))

  mk : make-abelian-group (Chain-map A B)
  mk .ab-is-set = Chain-map-set
  mk .mul f g .map n = H._*_ n (f .map n) (g .map n)
  mk .mul f g .comm n x =
      ap₂ (B._*_ n) (f .comm n x) (g .comm n x)
    ∙ sym (is-group-hom.pres-⋆ (B .∂ᶜ n .∫Hom.snd) _ _)
  mk .inv f .map n = H._⁻¹ n (f .map n)
  mk .inv f .comm n x =
      ap (B._⁻¹ n) (f .comm n x)
    ∙ sym (is-group-hom.pres-inv (B .∂ᶜ n .∫Hom.snd))
  mk .1g .map n = H.1g n
  mk .1g .comm n x = sym (is-group-hom.pres-id (B .∂ᶜ n .∫Hom.snd))
  mk .idl f = Chain-map-path λ n → ext λ x → B.idl n
  mk .assoc f g h = Chain-map-path λ n → ext λ x → B.associative n
  mk .invl f = Chain-map-path λ n → ext λ x → B.inversel n
  mk .comm f g = Chain-map-path λ n → ext λ x → B.commutes n
```
-->

## The functor Γ

```agda
Γ : Chain-complex lzero → Functor (Δ ^op) (Ab lzero)
Γ C .F₀ n = Chain-hom-ab (NΔ n) C
Γ C .F₁ {n} {m} g .∫Hom.fst φ =
  ChC._∘_ {NΔ m} {NΔ n} {C} φ (NΔ-map g)
Γ C .F₁ {n} {m} g .∫Hom.snd .is-group-hom.pres-⋆ φ ψ =
  Chain-map-path λ k → ext λ x p → refl
Γ C .F-id {n} = ext λ φ →
  ap (ChC._∘_ {NΔ n} {NΔ n} {C} φ) NΔ-map-id ∙ ChC.idr φ
Γ C .F-∘ {n} {m} {k} f g = ext λ φ →
    ap (ChC._∘_ {NΔ k} {NΔ n} {C} φ) (NΔ-map-∘ g f)
  ∙ ChC.assoc φ (NΔ-map g) (NΔ-map f)
```

Together with the [[Moore complex|moore-complex]] $N$, both halves
of the Dold–Kan correspondence are now present; the unit and counit
exhibiting them as inverse equivalences remain future work.

## Eilenberg–MacLane objects

The complex concentrated in a single degree has a group in one
position and the trivial group everywhere else, with zero
boundaries.

<!--
```agda
Zero-ab : Abelian-group lzero
Zero-ab = to-ab mk where
  mk : make-abelian-group (Lift lzero ⊤)
  mk .ab-is-set = hlevel 2
  mk .mul _ _ = lift tt
  mk .inv _ = lift tt
  mk .1g = lift tt
  mk .idl _ = refl
  mk .assoc _ _ _ = refl
  mk .invl _ = refl
  mk .comm _ _ = refl

private
  zero-hom : {X Y : Abelian-group lzero} → Ab lzero .Precategory.Hom X Y
  zero-hom {X} {Y} .∫Hom.fst _ = Abelian-group-on.1g (Y .snd)
  zero-hom {X} {Y} .∫Hom.snd .is-group-hom.pres-⋆ _ _ =
    sym (Abelian-group-on.idl (Y .snd))
```
-->

```agda
concentrated : Abelian-group lzero → Nat → Chain-complex lzero
concentrated A zero .ob zero = A
concentrated A zero .ob (suc k) = Zero-ab
concentrated A zero .∂ᶜ n = zero-hom
concentrated A zero .∂ᶜ-∂ᶜ n x = refl
concentrated A (suc n) .ob zero = Zero-ab
concentrated A (suc n) .ob (suc k) = concentrated A n .ob k
concentrated A (suc n) .∂ᶜ zero = zero-hom
concentrated A (suc n) .∂ᶜ (suc k) = concentrated A n .∂ᶜ k
concentrated A (suc n) .∂ᶜ-∂ᶜ zero x = refl
concentrated A (suc n) .∂ᶜ-∂ᶜ (suc k) x = concentrated A n .∂ᶜ-∂ᶜ k x

K : Abelian-group lzero → Nat → Functor (Δ ^op) (Ab lzero)
K A n = Γ (concentrated A n)
```

## Ordinary cohomology

Forgetting the group structure of $K(A,n)$ degreewise gives a
simplicial set, and the $n$-th **cohomology** of a simplicial set
with coefficients in $A$ is the set of connected components of the
mapping space into it — cocycles modulo coboundaries, in the same
combinatorial pattern as the [[nonabelian
$H^1$|simplicial-delooping]] built earlier.

<!--
```agda
private module SC = Cartesian-closed sSet-closed
```
-->

```agda
K-sset : Abelian-group lzero → Nat → ⌞ sSet ⌟
K-sset A n = Ab↪Sets F∘ K A n

H[_,_]⟨_⟩ : ⌞ sSet ⌟ → Nat → Abelian-group lzero → Type
H[ X , n ]⟨ A ⟩ = π₀ˢ SC.[ X , K-sset A n ]
```

That these sets compute singular cohomology of the geometric
realization — and carry the abelian group structure inherited from
$K(A,n)$ — depends on the simplicial homotopy theory (Kan fibrancy
of $K(A,n)$, simplicial homotopies of mapping spaces) catalogued as
future work in the [[reading guide|higher-topos-theory-in-physics]].
