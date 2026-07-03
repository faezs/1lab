<!--
```agda
open import Cat.Instances.Simplex
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Fin

open Precategory
open Functor
open Δ-map
open _=>_
```
-->

```agda
module Cat.Instances.SimplicialPresheaves.Cech
  {C : Precategory lzero lzero}
  where
```

<!--
```agda
open import Cat.Instances.SimplicialPresheaves C
```
-->

# The Čech object of a map of presheaves {defines="cech-object cech-nerve"}

The paper's (38): a map $f : E \to B$ of [[presheaves]] — think of a
cover, or a bundle projection — generates a [[simplicial presheaf]],
its **Čech object**, whose $k$-simplices are the $(k+1)$-fold fibre
products

$$
\check{C}(f)_k = E \times_B E \times_B \cdots \times_B E.
$$

In the language of plots this is concrete: a $(U, [k])$-plot of the
Čech object is a $(k+1)$-tuple of $U$-plots of $E$ which $f$
identifies — i.e. a tuple of plots of the "intersections" of the
cover, which is exactly how the Čech nerve of an open cover arises in
topology.

Before the code, one adjustment. The naive compatibility condition
"every component agrees with the zeroth" is anchored at the vertex
$0$, and reindexing along a simplicial operator moves the anchor:
restricting a tuple along $g : [n] \to [k]$ would have to compare
against index $g(0)$ rather than $0$. We instead store the
(equivalent, and still propositional, since $B(U)$ is a set)
*pairwise* condition, which is stable under reindexing on the nose.

Now the Čech object itself. In the geometric direction a tuple
restricts componentwise, with [[naturality|natural transformation]]
of $f$ guaranteeing that restricted tuples still agree in $B$; in the
simplicial direction it reindexes along the underlying map of a
simplicial operator.

```agda
module _ {E B : ⌞ PSh lzero C ⌟} (f : E => B) where
  Čech : ⌞ sPSh ⌟
  Čech .F₀ (U , k) = el!
    (Σ[ v ∈ (Fin (suc k) → ∣ E .F₀ U ∣) ]
     ((i j : Fin (suc k)) → f .η U (v i) ≡ f .η U (v j)))

  Čech .F₁ (h , g) (v , p) = (λ i → E .F₁ h (v (g .map i))) , λ i j →
       happly (f .is-natural _ _ h) (v (g .map i))
    ∙∙ ap (B .F₁ h) (p (g .map i) (g .map j))
    ∙∙ sym (happly (f .is-natural _ _ h) (v (g .map j)))
```

The functor laws only concern the tuple itself — the agreement
condition is a proposition — and reindexing is strictly functorial,
so both reduce to functoriality of $E$ at each component.

```agda
  Čech .F-id = funext λ (v , p) →
    Σ-prop-path! (funext λ i → happly (E .F-id) (v i))

  Čech .F-∘ (h₂ , g₂) (h₁ , g₁) = funext λ (v , p) →
    Σ-prop-path! (funext λ i →
      happly (E .F-∘ h₂ h₁) (v (g₁ .map (g₂ .map i))))
```

The Čech object comes with its **augmentation** to the base: at
every simplicial level, project the zeroth component of the tuple
and push it into $B$. Naturality in the geometric direction is
naturality of $f$; in the simplicial direction it is the stored
agreement between the (moved) anchor $g(0)$ and $0$.

```agda
  cech-aug : Čech => constᵍ B
  cech-aug .η (U , k) (v , p) = f .η U (v fzero)
  cech-aug .is-natural (U , k) (V , n) (h , g) = funext λ (v , p) →
      happly (f .is-natural _ _ h) (v (g .map fzero))
    ∙ ap (B .F₁ h) (p (g .map fzero) fzero)
```

The genuinely homotopical content of (38) — that for a *cover* the
augmentation is a **local** weak equivalence, so that the Čech
object is a (projectively cofibrant) resolution of $B$ available for
computing nonabelian cohomology — lives in the local model structure
on simplicial presheaves, and remains future work.
