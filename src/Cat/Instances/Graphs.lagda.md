---
description: |
  The category of graphs.
---
<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Reflection

open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Strict

import Cat.Reasoning
```
-->
```agda
module Cat.Instances.Graphs where
```

<!--
```agda
private variable
  o o' ℓ ℓ' : Level
```
-->

# The category of graphs

:::{.definition #graph}
A **graph** (really, an $(o, \ell)$-graph^[and, even more pedantically,
a directed multi-$(o, ℓ)$-graph]) is given by a set $V : \Sets_o$ of
**vertices** and, for each pair of elements $x, y : V$, a set of
**edges** $E(x, y) : \Sets_\ell$ from $x$ to $y$. That's it: a set $V$
and a family of sets over $V \times V$.
:::


```agda
record Graph (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Vertex : Type o
    Edge : Vertex → Vertex → Type ℓ
    Vertex-is-set : is-set Vertex
    Edge-is-set : ∀ {x y} → is-set (Edge x y)
```

<!--
```agda
open Graph
open hlevel-projection

instance
  Underlying-Graph : Underlying (Graph o ℓ)
  Underlying-Graph = record { ⌞_⌟ = Graph.Vertex }

  hlevel-proj-vertex : hlevel-projection (quote Graph.Vertex)
  hlevel-proj-vertex .has-level = quote Graph.Vertex-is-set
  hlevel-proj-vertex .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-vertex .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-vertex .get-argument _ = typeError []

  hlevel-proj-edge : hlevel-projection (quote Graph.Edge)
  hlevel-proj-edge .has-level = quote Graph.Edge-is-set
  hlevel-proj-edge .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-edge .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-edge .get-argument _ = typeError []
```
-->

:::{.definition #graph-homomorphism}
A **graph homomorphism** $G \to H$ consists of a mapping of vertices
$f_v : G \to H$, along with a mapping of edges $f_e : G(x, y) \to H(f_v(x), f_v(y))$.
:::


```agda
record Graph-hom (G : Graph o ℓ) (H : Graph o' ℓ') : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  no-eta-equality
  field
    vertex : ⌞ G ⌟ → ⌞ H ⌟
    edge : ∀ {x y} → G .Edge x y → H .Edge (vertex x) (vertex y)
```

<!--
```agda
private variable
  G H K : Graph o ℓ

open Graph-hom

unquoteDecl H-Level-Graph-hom = declare-record-hlevel 2 H-Level-Graph-hom (quote Graph-hom)

Graph-hom-pathp
  : {G : I → Graph o ℓ} {H : I → Graph o' ℓ'}
  → {f : Graph-hom (G i0) (H i0)} {g : Graph-hom (G i1) (H i1)}
  → (p0 : ∀ (x : ∀ i → G i .Vertex)
          → PathP (λ i → H i .Vertex)
              (f .vertex (x i0)) (g .vertex (x i1)))
  → (p1 : ∀ {x y : ∀ i → G i .Vertex}
          → (e : ∀ i → G i .Edge (x i) (y i))
          → PathP (λ i → H i .Edge (p0 x i) (p0 y i))
              (f .edge (e i0)) (g .edge (e i1)))
  → PathP (λ i → Graph-hom (G i) (H i)) f g
Graph-hom-pathp {G = G} {H = H} {f = f} {g = g} p0 p1 = pathp where
  vertex* : I → Type _
  vertex* i = (G i) .Vertex

  edge* : (i : I) → vertex* i → vertex* i → Type _
  edge* i x y = (G i) .Edge x y

  pathp : PathP (λ i → Graph-hom (G i) (H i)) f g
  pathp i .vertex x = p0 (λ j → coe vertex* i j x) i
  pathp i .edge {x} {y} e =
    p1 {x = λ j → coe vertex* i j x} {y = λ j → coe vertex* i j y}
      (λ j → coe (λ j → edge* j (coe vertex* i j x) (coe vertex* i j y)) i j (e* j)) i
    where

      x* y* : (j : I) → vertex* i
      x* j = coei→i vertex* i x (~ j ∨ i)
      y* j = coei→i vertex* i y (~ j ∨ i)

      e* : (j : I) → edge* i (coe vertex* i i x) (coe vertex* i i y)
      e* j =
        comp (λ j → edge* i (x* j) (y* j)) ((~ i ∧ ~ j) ∨ (i ∧ j)) λ where
          k (k = i0) → e
          k (i = i0) (j = i0) → e
          k (i = i1) (j = i1) → e

Graph-hom-path
  : {f g : Graph-hom G H}
  → (p0 : ∀ x → f .vertex x ≡ g .vertex x)
  → (p1 : ∀ {x y} → (e : Graph.Edge G x y) → PathP (λ i → Graph.Edge H (p0 x i) (p0 y i)) (f .edge e) (g .edge e))
  → f ≡ g
Graph-hom-path {G = G} {H = H} p0 p1 =
  Graph-hom-pathp {G = λ _ → G} {H = λ _ → H}
    (λ x i → p0 (x i) i)
    (λ e i → p1 (e i) i)

instance
  Funlike-Graph-hom : Funlike (Graph-hom G H) ⌞ G ⌟ λ _ → ⌞ H ⌟
  Funlike-Graph-hom .Funlike._#_ = vertex
```
-->

Graphs and graph homomorphisms can be organized into a category $\Graphs$.

```agda
Graphs : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Graphs o ℓ .Precategory.Ob = Graph o ℓ
Graphs o ℓ .Precategory.Hom = Graph-hom
Graphs o ℓ .Precategory.Hom-set _ _ = hlevel 2
Graphs o ℓ .Precategory.id .vertex v = v
Graphs o ℓ .Precategory.id .edge e = e
Graphs o ℓ .Precategory._∘_ f g .vertex v = f .vertex (g .vertex v)
Graphs o ℓ .Precategory._∘_ f g .edge e = f .edge (g .edge e)
Graphs o ℓ .Precategory.idr _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.idl _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.assoc _ _ _ = Graph-hom-path (λ _ → refl) (λ _ → refl)

module Graphs {o} {ℓ} = Cat.Reasoning (Graphs o ℓ)
```

<!--
```agda
open Functor
```
-->

:::{.definition #underlying-graph alias="underlying-graph-functor"}
Note that every [[strict category]] has an underlying graph, where
the vertices are given by objects, and edges by morphisms. Moreover,
functors between strict categories give rise to graph homomorphisms
between underlying graphs. This gives rise to a functor from the
[[category of strict categories]] to the category of graphs.
:::

```agda
Strict-cats↪Graphs : Functor (Strict-cats o ℓ) (Graphs o ℓ)
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex = Precategory.Ob C
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge = Precategory.Hom C
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex-is-set = C-strict
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge-is-set = Precategory.Hom-set C _ _
Strict-cats↪Graphs .F₁ F .vertex = F .F₀
Strict-cats↪Graphs .F₁ F .edge = F .F₁
Strict-cats↪Graphs .F-id = Graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Graphs .F-∘ F G = Graph-hom-path (λ _ → refl) (λ _ → refl)
```

The underlying graph functor is faithful, as functors are graph homomorphisms
with extra properties.

```agda
Strict-cats↪Graphs-faithful : is-faithful (Strict-cats↪Graphs {o} {ℓ})
Strict-cats↪Graphs-faithful p =
  Functor-path
    (λ x i → p i .vertex x)
    (λ e i → p i .edge e)
```

```
-- We need one-hop graph neighborhoods

```
Let a graph be a tuple of nodes and edges,
G = (V, E),
with one-hop neighbourhoods defined as
Nu = {v ∈ V | (v, u) ∈ E}.
```

-- one-hop-graph-neighborhoods : _
-- one-hop-graph-neighborhoods = ?

module Neighborhoods {G : Graph o ℓ} where
  open import Cat.Prelude
  open import 1Lab.Prelude
  open import Data.Sum
  open Graph G

  -- record Neighborhood (G : Graph o ℓ) (v : Graph.Vertex G) : Type (o ⊔ ℓ) where
  --   field
  --     neighbors : Type o
  --     neighbor-edges : neighbors → G .Edge neighbors v
  --     neighbor-is-set : is-set neighbors

  one-hop-out : Vertex G  → Type (o ⊔ ℓ)
  one-hop-out v = Σ[ u ∈ G .Vertex ] G .Edge v u

  one-hop-in : Vertex G → Type (o ⊔ ℓ)
  one-hop-in v = Σ[ u ∈ Graph.Vertex G ] Graph.Edge G u v

  -- one-hop-neighborhood : (G : Graph o ℓ) → (v : Graph.Vertex G) → Neighborhood G v
  -- one-hop-neighborhood G v .Neighborhood.neighbors = one-hop-out G v
  -- one-hop-neighborhood G v .Neighborhood.neighbor-edges (u , e) = e
  -- one-hop-neighborhood G v .Neighborhood.neighbor-is-set =
  --   Σ-inj-set (Graph.Vertex-is-set G) λ _ → Graph.Edge-is-set G

  -- For convenience, we also provide functions to get just the vertex sets
  out-vertices : Vertex G → Type o
  out-vertices v = snd (one-hop-out v)

  in-vertices : Vertex G → Type o
  in-vertices v = fst ∘ one-hop-in G v

  -- Helper function to check if a vertex is a neighbor
  is-neighbor : (G : Graph o ℓ) → (v u : Graph.Vertex G) → Type ℓ
  is-neighbor G v u = Graph.Edge G v u

  -- Function to get all neighbors (both in and out)
  all-neighbors : (G : Graph o ℓ) → Graph.Vertex G → Type (o ⊔ ℓ)
  all-neighbors G v = one-hop-out G v ⊎ one-hop-in G v

-- ```

```
