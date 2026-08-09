---
description: |
  The forked site of a network: the underlying graph of a DNN, and
  the typed-vertex forked graph of Belfiore–Bennequin's fork surgery,
  with the arrow inventory available by construction.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base hiding (_++_)
open import Data.List.Properties
open import Data.Sum.Properties
open import Data.Fin.Properties
open import Data.Fin.Base
open import Data.Sum.Base

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Graph.Fork where
```

# The forked site of a network {defines="fork-site network-graph"}

A general feed-forward architecture has vertices that receive
*several* inputs, and presheaves on the naive path category cannot
express "the value at $c$ is computed from the *joint* values of its
inputs". Belfiore–Bennequin's solution (§1.3 of the paper) is *fork
surgery*: next to each convergent vertex $c$, insert an auxiliary
pair $A^\star_c$ (which the sheaf condition will force to be the
product of the inputs) and $A_c$ (carrying the joint input data),
connected by *tines* from each input, an arrow $A^\star_c \to A_c$
(the paper's *tang* of the fork), and a *handle* $c \to A_c$.

## Networks

A **network** is presented by adjacency data: a finite set of
vertices, for each vertex the list of its inputs, and a depth
function along which information flows strictly upward. From this
presentation we *derive* the paper's graph $\Gamma$, so that the
hypotheses of chapter 1 — Γ is *directed* — become theorems about the
derived graph rather than extra axioms. Two remarks on faithfulness:
the depth function is a topological sort, which is *data* rather than
the bare property of acyclicity (every finite DAG admits one, and
every concrete network comes with its layer depth, so nothing is
lost); and the paper's *classicality* (at most one edge between two
vertices, i.e. no duplicated inputs) is not needed by anything in
this module, so it is stated as a definition to be assumed precisely
where it earns its keep.

```agda
record Network : Type where
  field
    size    : Nat
    inputs  : Fin size → List (Fin size)
    depth   : Fin size → Nat
    depth-< : ∀ c (i : Fin (length (inputs c)))
            → depth (inputs c ! i) Nat.< depth c

open Network public

module _ (N : Network) where
  network-graph : Graph lzero lzero
  network-graph .Graph.Node = Fin (N .size)
  network-graph .Graph.Edge b c =
    Σ[ i ∈ Fin (length (N .inputs c)) ] (N .inputs c ! i ≡ b)
  network-graph .Graph.Node-set = hlevel 2
  network-graph .Graph.Edge-set = hlevel 2

  is-classical : Type
  is-classical = ∀ {b c} → is-prop (network-graph .Graph.Edge b c)
```

Directedness of the derived graph: every edge, hence every nonempty
path, strictly increases depth; in particular Γ has no oriented
cycles. (Compare `path-≤`{.Agda} for the chain.)

```agda
  edge-depth-<
    : ∀ {b c} → network-graph .Graph.Edge b c
    → N .depth b Nat.< N .depth c
  edge-depth-< {b} {c} (i , q) =
    subst (λ m → N .depth m Nat.< N .depth c) q (N .depth-< c i)

  path-depth-≤
    : ∀ {b c} → Path-in network-graph b c
    → N .depth b Nat.≤ N .depth c
  path-depth-≤ nil        = Nat.≤-refl
  path-depth-≤ (cons e p) =
    Nat.≤-trans (Nat.<-weaken (edge-depth-< e)) (path-depth-≤ p)

  network-no-loop
    : ∀ {b c} → network-graph .Graph.Edge c b
    → Path-in network-graph b c → ⊥
  network-no-loop {b} {c} e p = Nat.<-irrefl refl
    (Nat.≤-trans (edge-depth-< e) (Nat.≤-trans (path-depth-≤ p) Nat.≤-refl))
```

## The forked graph

Rather than performing surgery on Γ and then classifying the arrows
of the result — the paper's prose gestures at this classification but
never carries it out — we define the forked graph *directly*, with a
data type of typed vertices and a data family of edges indexed by
them. The arrow inventory then holds **by construction**: the case
analyses that chapter 1 leans on are pattern matches.

A vertex $c$ is a **fork** when it has at least two inputs; only such
vertices grow a star and a tang vertex. (Fork-ness, an inequality of
naturals, is definitionally proof-irrelevant.) We write `tang c` for
the vertex the paper calls $A_c$ — the target of the fork's tang
arrow — and `socket` for that arrow $A^\star_c \to A_c$ itself.

```agda
  is-fork : Fin (N .size) → Type
  is-fork c = 2 Nat.≤ length (N .inputs c)

  data F-vtx : Type where
    orig : Fin (N .size) → F-vtx
    star : (c : Fin (N .size)) → is-fork c → F-vtx
    tang : (c : Fin (N .size)) → is-fork c → F-vtx
```

<!--
```agda
  private
    Code : Type
    Code = Fin (N .size)
         ⊎ ((Σ[ c ∈ Fin (N .size) ] is-fork c)
         ⊎  (Σ[ c ∈ Fin (N .size) ] is-fork c))

    encode : F-vtx → Code
    encode (orig c)   = inl c
    encode (star c f) = inr (inl (c , f))
    encode (tang c f) = inr (inr (c , f))

    decode : Code → F-vtx
    decode (inl c)             = orig c
    decode (inr (inl (c , f))) = star c f
    decode (inr (inr (c , f))) = tang c f

    decode-encode : ∀ v → decode (encode v) ≡ v
    decode-encode (orig c)   = refl
    decode-encode (star c f) = refl
    decode-encode (tang c f) = refl

    ΣF-is-set : is-set (Σ[ c ∈ Fin (N .size) ] is-fork c)
    ΣF-is-set = Σ-is-hlevel 2 (hlevel 2) λ c →
      is-prop→is-set Nat.≤-is-prop

    Code-is-set : is-set Code
    Code-is-set = ⊎-is-hlevel 0 ⦃ hlevel-instance (hlevel 2) ⦄
      ⦃ hlevel-instance (⊎-is-hlevel 0
          ⦃ hlevel-instance ΣF-is-set ⦄ ⦃ hlevel-instance ΣF-is-set ⦄) ⦄

  F-vtx-is-set : is-set F-vtx
  F-vtx-is-set = retract→is-hlevel 2 decode encode decode-encode Code-is-set
```
-->

The **edges**, in *site* orientation (arrows point from a vertex to
the thing its value restricts along — see [`Neural.Base`]): a
*single-input transmission* $c \to b$ when $b$ is the unique input of
$c$; a *tine* $b \to A^\star_c$ for each position at which $b$ occurs
among the inputs of the fork $c$; the *socket* $A^\star_c \to A_c$;
and the *handle* $c \to A_c$. The equational constraints are carried
as *fields* rather than computed indices, so that matching on an
edge never has to unify under a function symbol; and the socket is
allowed to connect a star and a tang with *a priori* different
fork-ness witnesses, so that no proof unification is ever demanded of
the type checker.

[`Neural.Base`]: Neural.Base.html

```agda
  data F-edge : F-vtx → F-vtx → Type where
    single : ∀ {c b} → N .inputs c ≡ b ∷ []
           → F-edge (orig c) (orig b)
    tine   : ∀ {b c} {f : is-fork c} (i : Fin (length (N .inputs c)))
           → N .inputs c ! i ≡ b
           → F-edge (orig b) (star c f)
    socket : ∀ {c} {f f' : is-fork c}
           → F-edge (star c f) (tang c f')
    handle : ∀ {c} {f : is-fork c}
           → F-edge (orig c) (tang c f)
```

The classification of edges by the types of their endpoints — the
paper's implicit "that is all" — is now a theorem, phrased as a
retraction onto a normal form computed by recursion on the vertex
types. The normal form is also what shows that edges form sets.

```agda
  F-edge-shape : F-vtx → F-vtx → Type
  F-edge-shape (orig c)   (orig b)     = N .inputs c ≡ b ∷ []
  F-edge-shape (orig b)   (star c f)   =
    Σ[ i ∈ Fin (length (N .inputs c)) ] (N .inputs c ! i ≡ b)
  F-edge-shape (orig c)   (tang c' f)  = c ≡ c'
  F-edge-shape (star c f) (tang c' f') = c ≡ c'
  F-edge-shape _ _ = ⊥

  edge→shape : ∀ {x y} → F-edge x y → F-edge-shape x y
  edge→shape (single q) = q
  edge→shape (tine i q) = i , q
  edge→shape socket     = refl
  edge→shape handle     = refl

  shape→edge : ∀ {x y} → F-edge-shape x y → F-edge x y
  shape→edge {orig c}   {orig b}     q       = single q
  shape→edge {orig b}   {star c f}   (i , q) = tine i q
  shape→edge {orig c}   {tang c' f'} q       =
    J (λ c'' _ → (f'' : is-fork c'') → F-edge (orig c) (tang c'' f''))
      (λ f'' → handle) q f'
  shape→edge {star c f} {tang c' f'} q       =
    J (λ c'' _ → (f'' : is-fork c'') → F-edge (star c f) (tang c'' f''))
      (λ f'' → socket) q f'

  shape→edge→shape : ∀ {x y} (e : F-edge x y) → shape→edge (edge→shape e) ≡ e
  shape→edge→shape (single q) = refl
  shape→edge→shape (tine i q) = refl
  shape→edge→shape (socket {c} {f} {f'}) = happly
    (J-refl (λ c'' _ → (f'' : is-fork c'') → F-edge (star c f) (tang c'' f''))
      (λ f'' → socket)) f'
  shape→edge→shape (handle {c} {f}) = happly
    (J-refl (λ c'' _ → (f'' : is-fork c'') → F-edge (orig c) (tang c'' f''))
      (λ f'' → handle)) f

  private
    shape-is-set : ∀ x y → is-set (F-edge-shape x y)
    shape-is-set (orig c)   (orig b)     = hlevel 2
    shape-is-set (orig b)   (star c f)   = hlevel 2
    shape-is-set (orig c)   (tang c' f)  = hlevel 2
    shape-is-set (star c f) (tang c' f') = hlevel 2
    shape-is-set (orig c)   (star c' f)  = hlevel 2
    shape-is-set (star c f) (orig b)     = hlevel 2
    shape-is-set (star c f) (star c' f') = hlevel 2
    shape-is-set (tang c f) _            = hlevel 2

  F-edge-is-set : ∀ x y → is-set (F-edge x y)
  F-edge-is-set x y = retract→is-hlevel 2
    shape→edge edge→shape shape→edge→shape (shape-is-set x y)

  fork-graph : Graph lzero lzero
  fork-graph .Graph.Node = F-vtx
  fork-graph .Graph.Edge = F-edge
  fork-graph .Graph.Node-set = F-vtx-is-set
  fork-graph .Graph.Edge-set {x} {y} = F-edge-is-set x y

  fork-site : Precategory lzero lzero
  fork-site = Path-category fork-graph
```

## The arrow inventory

With the edges a data family, the load-bearing classification facts
are pattern matches. Nothing comes out of a tang vertex — tangs are
the local sinks of the site, holding the joint input data that
everything else restricts; and the only edges into a star are its
tines.

```agda
  no-edge-out-of-tang : ∀ {c f v} → F-edge (tang c f) v → ⊥
  no-edge-out-of-tang ()

  path-out-of-tang-is-nil
    : ∀ {c f v} (p : Path-in fork-graph (tang c f) v)
    → Σ[ q ∈ tang c f ≡ v ]
        (PathP (λ i → Path-in fork-graph (tang c f) (q i)) nil p)
  path-out-of-tang-is-nil nil        = refl , refl
  path-out-of-tang-is-nil (cons e p) = absurd (no-edge-out-of-tang e)

  edge-into-star
    : ∀ {v c} {f : is-fork c} (e : F-edge v (star c f))
    → Σ[ i ∈ Fin (length (N .inputs c)) ]
      Σ[ b ∈ Fin (N .size) ]
        ((N .inputs c ! i ≡ b) × (v ≡ orig b))
  edge-into-star (tine {b = b} i q) = i , b , q , refl
```

Finally, the composition lemmas about nonemptiness of paths that the
coverage's stability proof consumes: appending preserves nonemptiness
on either side.

```agda
  nonempty : ∀ {v u} → Path-in fork-graph v u → Ω
  nonempty nil        = ⊥Ω
  nonempty (cons _ _) = ⊤Ω

  ++-nonempty-l
    : ∀ {v u w} (p : Path-in fork-graph v u) {q : Path-in fork-graph u w}
    → ∣ nonempty p ∣ → ∣ nonempty (p ++ q) ∣
  ++-nonempty-l (cons _ _) _ = tt

  ++-nonempty-r
    : ∀ {v u w} (p : Path-in fork-graph v u) {q : Path-in fork-graph u w}
    → ∣ nonempty q ∣ → ∣ nonempty (p ++ q) ∣
  ++-nonempty-r nil        hq = hq
  ++-nonempty-r (cons _ _) hq = tt
```
