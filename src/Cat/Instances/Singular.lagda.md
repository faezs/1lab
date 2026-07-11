<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Displayed.Total
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Solver
open import Algebra.Group

open import Data.Set.Coequaliser

import Cat.Reasoning

open Precategory
open Terminal
open make-group
```
-->

```agda
module Cat.Instances.Singular where
```

<!--
```agda
private module Grps = Cat.Reasoning (Groups lzero)
```
-->

# The orbi-singular site {defines="orbi-singular-site global-orbit-category"}

The paper's diagram (28): the probes of *orbi-singular* geometry are
the "$G$-cones" $\ast /\!\!/ G$ — a point with the internal symmetry
of a group $G$. A map of such probes $\ast/\!\!/G \to \ast/\!\!/H$
is a group homomorphism, but two homomorphisms that differ by
conjugation in the target present the *same* map of quotient
singularities, since conjugation is an inner symmetry of the cone.
The resulting site is the **global orbit category**: groups, with
conjugacy classes of homomorphisms between them.

```agda
conj
  : (G H : Group lzero)
  → Grps.Hom G H → Grps.Hom G H → Type
conj G H f g = Σ ⌞ H ⌟ λ h →
  ∀ x → g .fst x ≡ h H.⋆ (f .fst x H.⋆ H.inverse h)
  where module H = Group-on (H .snd)
```

<!--
```agda
private
  conj-refl : {G H : Group lzero} (f : Grps.Hom G H) → conj G H f f
  conj-refl {G} {H} f = H.unit , λ x → sym
    ( ap (H.unit H.⋆_) (ap (f .fst x H.⋆_) H.inv-unit ∙ H.idr)
    ∙ H.idl)
    where module H = Group-on (H .snd)

  conj-∘
    : {G H K : Group lzero}
    → (f f' : Grps.Hom H K) (g g' : Grps.Hom G H)
    → conj H K f f' → conj G H g g'
    → conj G K (f Grps.∘ g) (f' Grps.∘ g')
  conj-∘ {G} {H} {K} f f' g g' (k , pk) (h , ph) =
    k K.⋆ f .fst h , λ x →
      f' .fst (g' .fst x)
        ≡⟨ pk (g' .fst x) ⟩
      k K.⋆ (f .fst (g' .fst x) K.⋆ K.inverse k)
        ≡⟨ ap (λ e → k K.⋆ (f .fst e K.⋆ K.inverse k)) (ph x) ⟩
      k K.⋆ (f .fst (h H.⋆ (g .fst x H.⋆ H.inverse h)) K.⋆ K.inverse k)
        ≡⟨ ap (λ e → k K.⋆ (e K.⋆ K.inverse k)) (f-expand x) ⟩
      k K.⋆ ((f .fst h K.⋆ (f .fst (g .fst x) K.⋆ K.inverse (f .fst h))) K.⋆ K.inverse k)
        ≡⟨ group! K ⟩
      (k K.⋆ f .fst h) K.⋆ (f .fst (g .fst x) K.⋆ K.inverse (k K.⋆ f .fst h))
        ∎
    where
      module K = Group-on (K .snd)
      module H = Group-on (H .snd)
      module f = is-group-hom (f .snd)

      f-expand
        : ∀ x → f .fst (h H.⋆ (g .fst x H.⋆ H.inverse h))
        ≡ f .fst h K.⋆ (f .fst (g .fst x) K.⋆ K.inverse (f .fst h))
      f-expand x =
          f.pres-⋆ _ _
        ∙ ap (f .fst h K.⋆_) (f.pres-⋆ _ _ ∙ ap (f .fst (g .fst x) K.⋆_) f.pres-inv)
```
-->

Conjugacy is reflexive — witnessed by the unit — and composition of
homomorphisms descends to conjugacy classes: if $f' = k f k^{-1}$
and $g' = h g h^{-1}$, then $f' g' = (k \cdot f(h))\, (f g)\, (k
\cdot f(h))^{-1}$, so the composite class depends only on the
classes. The category laws hold because they hold on
representatives.

```agda
private
  inc-path
    : {G H : Group lzero} {f g : Grps.Hom G H}
    → f ≡ g → Path (Grps.Hom G H / conj G H) (inc f) (inc g)
  inc-path = ap inc

Snglr : Precategory (lsuc lzero) lzero
Snglr .Ob = Group lzero
Snglr .Hom G H = Grps.Hom G H / conj G H
Snglr .Hom-set G H = squash
Snglr .id = inc Grps.id
Snglr ._∘_ = Quot-op₂ conj-refl conj-refl Grps._∘_ conj-∘
Snglr .idr {G} {H} = Coeq-elim-prop (λ _ → squash _ _)
  λ f → inc-path (Grps.idr f)
Snglr .idl {G} {H} = Coeq-elim-prop (λ _ → squash _ _)
  λ f → inc-path (Grps.idl f)
Snglr .assoc {G} {H} {K} {L} =
  Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → squash _ _)
    (λ f → Coeq-elim-prop (λ _ → Π-is-hlevel 1 λ _ → squash _ _)
      (λ g → Coeq-elim-prop (λ _ → squash _ _)
        (λ h → inc-path (Grps.assoc f g h))))
```

The site has a terminal probe: the trivial cone, the point with no
singularity. Every group maps to the trivial group in exactly one
way, and — the quotient earning its keep — the conjugacy class of
any homomorphism *to* the trivial group is unique on the nose.

```agda
Triv : Group lzero
Triv = to-group mk where
  mk : make-group (Lift lzero ⊤)
  mk .group-is-set = hlevel 2
  mk .unit = lift tt
  mk .mul _ _ = lift tt
  mk .inv _ = lift tt
  mk .assoc _ _ _ = refl
  mk .invl _ = refl
  mk .idl _ = refl

Snglr-terminal : Terminal Snglr
Snglr-terminal .top = Triv
Snglr-terminal .has⊤ G .centre = inc bang where
  bang : Grps.Hom G Triv
  bang .fst _ = lift tt
  bang .snd .is-group-hom.pres-⋆ _ _ = refl
Snglr-terminal .has⊤ G .paths = Coeq-elim-prop (λ _ → squash _ _)
  λ f → quot (lift tt , λ x → refl)
```

**Orbi-singular spaces** are the presheaves on this site — the last
column of the paper's probe table, where orbifold singularities
live. A presheaf assigns to each group $G$ its set of
"$G$-singular points", contravariantly along conjugacy classes; the
[[homotopy quotient|action-groupoid]] built earlier is the
simplicial shadow of the same idea, and the two columns meet in the
paper's orbifolds.

```agda
OrbSpc : Precategory (lsuc (lsuc lzero)) (lsuc lzero)
OrbSpc = PSh (lsuc lzero) Snglr
```

Because `Snglr`{.Agda} has large object- and small hom-sets, the
[[cohesion|cohesive-topos]] machinery — stated for sites with
matching universe levels — does not instantiate directly; but
lifting the homomorphism classes one level is uniform, terminality
lifts along with them, and cohesion follows over the lifted
presentation of the same site.

<!--
```agda
open import Cat.Instances.Lift
import Cat.Instances.Presheaf.Cohesive
```
-->

```agda
Snglr↑ : Precategory (lsuc lzero) (lsuc lzero)
Snglr↑ = Lift-cat lzero (lsuc lzero) Snglr

Snglr↑-terminal : Terminal Snglr↑
Snglr↑-terminal .top = lift Triv
Snglr↑-terminal .has⊤ (lift G) .centre =
  lift (Snglr-terminal .has⊤ G .centre)
Snglr↑-terminal .has⊤ (lift G) .paths (lift h) =
  ap lift (Snglr-terminal .has⊤ G .paths h)

module Orb-cohesion =
  Cat.Instances.Presheaf.Cohesive Snglr↑ Snglr↑-terminal
```
