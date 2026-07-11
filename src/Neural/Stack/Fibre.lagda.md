---
description: |
  The vertical inclusion of a fibre into the total category of a
  split indexed category.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Displayed.Total
open import Cat.Prelude

open import Neural.Stack.Transport

import Neural.Stack.Grothendieck
import Cat.Reasoning
```
-->

```agda
module Neural.Stack.Fibre
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (F : Functor (B ^op) (Strict-cats o' ℓ'))
  where
```

# The fibre inclusions {defines="fibre-inclusion"}

Each fibre $F_U$ of a [[split indexed category|split-grothendieck]]
includes into the total category $\int F$ vertically: an object
$\xi$ goes to $(U, \xi)$, and a fibre morphism rides over the
identity of the base. The paper treats this inclusion silently
whenever it restricts a presheaf on $\int F$ to a fibre — the
quasi-inverse to `Tot`{.Agda ident=Tot} and the fibered Yoneda
embedding of equations 2.7–2.8 both factor through it — so it is
worth the one honest transport square its functoriality costs: the
identity of the base is not the composite of two identities, so the
morphism part of functoriality lives over $\mathrm{id} =
\mathrm{id} \circ \mathrm{id}$, and closes with the
[[toolkit|stack-transport-toolkit]].

<!--
```agda
private
  module B = Cat.Reasoning B
  module F = Functor F

open Neural.Stack.Grothendieck F

open Precategory
open Functor
open ∫Hom
```
-->

```agda
ι : (U : B.Ob) → Functor (Fib U) ∫F
ι U .F₀ ξ = U , ξ
ι U .F₁ {ξ} {ζ} u = ∫hom B.id (subst (Fib U .Hom ξ) (sym (·₀-id ζ)) u)
ι U .F-id = refl
ι U .F-∘ {ξ} {ζ} {η} u w = ∫Hom-path Grothendieck (sym (B.idl B.id)) $
  to-pathp $
       sym (subst-∙ (Fib U .Hom ξ) (sym (·₀-id η)) AP _)
    ∙  sub-parallel (Fib U) (Fib-set U) (sym (·₀-id η) ∙ AP)
         ((sym (·₀-id η) ∙ S₆) ∙ S) (Fib U ._∘_ u w)
    ∙  sym rchain
  where
    S  = sym (·₀-∘ B.id B.id η)
    S₆ = ap (B.id ·₀_) (sym (·₀-id η))
    AP = ap (_·₀ η) (sym (B.idl B.id))

    rchain
      : subst (Fib U .Hom ξ) S
          (Fib U ._∘_
            (B.id ·₁ subst (Fib U .Hom ζ) (sym (·₀-id η)) u)
            (subst (Fib U .Hom ξ) (sym (·₀-id ζ)) w))
      ≡ subst (Fib U .Hom ξ) ((sym (·₀-id η) ∙ S₆) ∙ S) (Fib U ._∘_ u w)
    rchain =
         ap (λ t → subst (Fib U .Hom ξ) S
              (Fib U ._∘_ t (subst (Fib U .Hom ξ) (sym (·₀-id ζ)) w)))
           (F₁-sub (F.₁ B.id) (sym (·₀-id η)) u)
      ∙  ap (subst (Fib U .Hom ξ) S)
           (sub-∘ˡ (Fib U) S₆ (B.id ·₁ u)
             (subst (Fib U .Hom ξ) (sym (·₀-id ζ)) w))
      ∙  ap (λ t → subst (Fib U .Hom ξ) S (subst (Fib U .Hom ξ) S₆ t))
           (comp-key F.F-id u w)
      ∙  ap (subst (Fib U .Hom ξ) S)
           (sym (subst-∙ (Fib U .Hom ξ) (sym (·₀-id η)) S₆ (Fib U ._∘_ u w)))
      ∙  sym (subst-∙ (Fib U .Hom ξ) (sym (·₀-id η) ∙ S₆) S (Fib U ._∘_ u w))
```

The inclusion lands over a single base object: composing with the
projection collapses it to the constant functor, definitionally on
both objects and morphisms — worth recording only in prose, since
`πF F∘ ι U` and the constant functor at $U$ agree on the nose
except for the usual functor-record bookkeeping. What is *not*
here: the restriction of presheaves along `ι`{.Agda} and the
resulting quasi-inverse to `Tot`{.Agda ident=Tot} — the successor
milestone.
