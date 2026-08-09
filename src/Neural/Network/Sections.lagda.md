---
description: |
  The unique-section theorem: a choice of activities at the input
  layers of a network extends to a unique global section of the
  dynamical object — what it means for the network to compute a
  function.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_)
open import Data.Fin.Base
open import Data.Dec.Base

open import Neural.Network.Activities
open import Neural.Graph.Fork

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Network.Sections where
```

# The unique-section theorem {defines="unique-section"}

Belfiore–Bennequin observe (§1.3) that, given activities
$\varepsilon^0$ on all the *input* layers, the dynamical object of a
network has a *unique* compatible family of activities — an element
of $\lim X^w$ — extending them: a trained network computes a
function. This module proves it: global sections of the
[[dynamical object|network-activities]] are equivalent to tuples of
input-layer activities. Existence is recursion on the depth of a
vertex (transmit the inputs forward); uniqueness is the same
recursion, using the section's own compatibilities.

```agda
module Network-sections
  {ℓ} (N : Network)
  (X₀ : Fin (N .size) → Set ℓ)
  (d : ∀ c → (∀ i → ∣ X₀ (N .inputs c ! i) ∣) → ∣ X₀ c ∣)
  where

  open Network-dynamics N X₀ d public

  is-input : Fin (N .size) → Type
  is-input c = length (N .inputs c) ≡ 0

  Inputs : Type ℓ
  Inputs = ∀ c → is-input c → ∣ X₀ c ∣

  NSection : Type ℓ
  NSection =
    Σ[ at ∈ ((v : F-vtx N) → Act v) ]
      (∀ v u (e : F-edge N v u) → αₑ e (at u) ≡ at v)

  restrict-inputs : NSection → Inputs
  restrict-inputs (at , _) c _ = at (orig c)
```

## Building the section

The value at a vertex is computed by structural recursion on a fuel
bound for its depth: an input vertex looks up the given activity,
and any other vertex transmits the recursively-computed joint state
of its inputs, which sit at strictly smaller depth. The case split
on inputhood is routed through a helper taking the decision as an
*argument*, so that the reasoning lemmas below can match on it
without any `with`-alignment.

```agda
  private module Build (g : Inputs) where
    go
      : ∀ c → (∀ i → ∣ X₀ (N .inputs c ! i) ∣)
      → Dec (is-input c) → ∣ X₀ c ∣
    go c rec (yes p) = g c p
    go c rec (no ¬p) = d c rec

    dec-of : ∀ c → Dec (is-input c)
    dec-of c = Nat.Discrete-Nat .decide (length (N .inputs c)) 0

    build : (n : Nat) (c : Fin (N .size)) → N .depth c Nat.< n → ∣ X₀ c ∣
    build zero    c bnd = absurd (Nat.¬suc≤0 bnd)
    build (suc n) c bnd = go c
      (λ i → build n (N .inputs c ! i)
        (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel bnd)))
      (dec-of c)

    go-yes
      : ∀ c rec (dec : Dec (is-input c)) (p : is-input c)
      → go c rec dec ≡ g c p
    go-yes c rec (yes p') p = ap (g c) (Nat.Nat-is-set _ _ p' p)
    go-yes c rec (no ¬p)  p = absurd (¬p p)

    go-no
      : ∀ c rec (dec : Dec (is-input c)) (¬p : ¬ is-input c)
      → go c rec dec ≡ d c rec
    go-no c rec (yes p) ¬p = absurd (¬p p)
    go-no c rec (no _)  ¬p = refl

    build-irr
      : ∀ n n' c bnd bnd' → build n c bnd ≡ build n' c bnd'
    build-irr zero    n'       c bnd bnd' = absurd (Nat.¬suc≤0 bnd)
    build-irr (suc n) zero     c bnd bnd' = absurd (Nat.¬suc≤0 bnd')
    build-irr (suc n) (suc n') c bnd bnd' = λ k →
      go c
        (λ i → build-irr n n' (N .inputs c ! i)
          (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel bnd))
          (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel bnd')) k)
        (dec-of c)
```

<!--
```agda
    rec₀ : ∀ c (i : Fin (length (N .inputs c))) → ∣ X₀ (N .inputs c ! i) ∣
    rec₀ c i = build (N .depth c) (N .inputs c ! i)
      (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel Nat.≤-refl))

    at₀ : (c : Fin (N .size)) → ∣ X₀ c ∣
    at₀ c = build (suc (N .depth c)) c Nat.≤-refl

    sec-at : ∀ v → Act v
    sec-at (orig c)   = at₀ c
    sec-at (star c f) i = at₀ (N .inputs c ! i)
    sec-at (tang c f) i = at₀ (N .inputs c ! i)

    build-tip
      : ∀ {b} n c (i : Fin (length (N .inputs c)))
      → (ieq : N .inputs c ! i ≡ b)
      → (bnd : N .depth (N .inputs c ! i) Nat.< n)
      → (bnd' : N .depth b Nat.< n)
      → build n (N .inputs c ! i) bnd
      ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) (build n b bnd')
    build-tip {b} n c i ieq bnd bnd' =
      J (λ b ieq
          → ∀ (bnd' : N .depth b Nat.< n)
          → build n (N .inputs c ! i) bnd
          ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) (build n b bnd'))
        (λ bnd' → build-irr n n (N .inputs c ! i) bnd bnd'
                ∙ sym (transport-refl _))
        ieq bnd'

    tuple-of
      : ∀ {b} (x : ∣ X₀ b ∣) (l : List (Fin (N .size))) (q' : b ∷ [] ≡ l)
      → (rec : (i : Fin (length l)) → ∣ X₀ (l ! i) ∣)
      → (rec-ok : ∀ (i : Fin (length l)) (ieq : l ! i ≡ b)
                → rec i ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) x)
      → subst (λ l' → (i : Fin (length l')) → ∣ X₀ (l' ! i) ∣) q'
          (one-tuple x)
      ≡ rec
    tuple-of {b} x l q' = J
      (λ l q' →
        (rec : (i : Fin (length l)) → ∣ X₀ (l ! i) ∣)
        → (∀ (i : Fin (length l)) (ieq : l ! i ≡ b)
           → rec i ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) x)
        → subst (λ l' → (i : Fin (length l')) → ∣ X₀ (l' ! i) ∣) q'
            (one-tuple x)
        ≡ rec)
      (λ rec rec-ok → transport-refl _ ∙ funext λ i → point i rec rec-ok)
      q'
      where
        point
          : ∀ (i : Fin 1) rec rec-ok
          → one-tuple {b = b} x i ≡ rec i
        point (fin zero) rec rec-ok =
          sym (rec-ok fzero refl ∙ transport-refl _)
        point (fin (suc k) ⦃ bd ⦄) rec rec-ok =
          absurd (Nat.¬suc≤0 (Nat.≤-peel bd))
```
-->

The edge compatibilities. Tines and the socket are immediate (up to
a transport killed by `J`); handles and single-input transmissions
compute by `go-no`, with a pointwise comparison of the joint tuples
(`tuple-of`, matching the single input's one-element tuple against
the recursively built one).

```agda
    fork-not-input : ∀ {c} → is-fork N c → ¬ is-input c
    fork-not-input fk p = Nat.¬suc≤0 (subst (2 Nat.≤_) p fk)

    single-not-input : ∀ {c b} → N .inputs c ≡ b ∷ [] → ¬ is-input c
    single-not-input q p = Nat.zero≠suc (sym p ∙ ap length q)

    sec-resp : ∀ v u (e : F-edge N v u) → αₑ e (sec-at u) ≡ sec-at v
    sec-resp _ _ (tine {b = b} {c = c} {f = f} i q) =
      J (λ b q
          → subst (λ m → ∣ X₀ m ∣) q (at₀ (N .inputs c ! i))
          ≡ at₀ b)
        (transport-refl _)
        q
    sec-resp _ _ (socket {c = c}) = refl
    sec-resp _ _ (handle {c = c} {f = f}) =
        ap (d c) (funext λ i →
          build-irr (suc (N .depth (N .inputs c ! i))) (N .depth c)
            (N .inputs c ! i) Nat.≤-refl
            (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel Nat.≤-refl)))
      ∙ sym (go-no c (rec₀ c) (dec-of c) (fork-not-input f))
    sec-resp _ _ (single {c = c} {b = b} q) =
        ap (d c) (tuple-of (at₀ b) (N .inputs c) (sym q) (rec₀ c) rec-ok)
      ∙ sym (go-no c (rec₀ c) (dec-of c) (single-not-input q))
      where
        rec-ok
          : ∀ i (ieq : N .inputs c ! i ≡ b)
          → rec₀ c i
          ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) (at₀ b)
        rec-ok i ieq =
            build-tip (N .depth c) c i ieq
              (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel Nat.≤-refl))
              (subst (λ m → N .depth m Nat.< N .depth c) ieq
                (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel Nat.≤-refl)))
          ∙ ap (subst (λ m → ∣ X₀ m ∣) (sym ieq))
              (build-irr (N .depth c) (suc (N .depth b)) b
                (subst (λ m → N .depth m Nat.< N .depth c) ieq
                  (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel Nat.≤-refl)))
                Nat.≤-refl)
```

## Existence and restriction

```agda
  section-of : Inputs → NSection
  section-of g = Build.sec-at g , Build.sec-resp g

  restrict-section
    : ∀ g → restrict-inputs (section-of g) ≡ g
  restrict-section g = funext λ c → funext λ p →
    Build.go-yes g c (Build.rec₀ g c) (Build.dec-of g c) p
```

## Uniqueness

Any section agrees with the built one: by the same recursion over
depth, using the section's *own* compatibilities. The vertex
trichotomy — input, single-input, fork — is resolved by matching the
input list *together with* the equation relating it to the vertex,
which is exactly the datum the site's edge constructors carry, so no
`with`-abstraction over neutral scrutinees is ever needed.

```agda
  private module Unique (s : NSection) where
    open Build (restrict-inputs s)

    s-tine
      : ∀ {c} {fk : is-fork N c} (i : Fin (length (N .inputs c)))
      → s .fst (star c fk) i ≡ s .fst (orig (N .inputs c ! i))
    s-tine {c} {fk} i =
      sym (transport-refl _) ∙ s .snd _ _ (tine {c = c} {f = fk} i refl)

    s-socket
      : ∀ {c} {fk : is-fork N c}
      → s .fst (tang c fk) ≡ s .fst (star c fk)
    s-socket {c} {fk} = s .snd _ _ (socket {c = c} {f = fk} {f' = fk})

    agree
      : ∀ n c (bnd : N .depth c Nat.< n)
      → build n c bnd ≡ s .fst (orig c)
    agree zero    c bnd = absurd (Nat.¬suc≤0 bnd)
    agree (suc n) c bnd = go-c (N .inputs c) refl
      where
        recₙ : ∀ i → ∣ X₀ (N .inputs c ! i) ∣
        recₙ i = build n (N .inputs c ! i)
          (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel bnd))

        tip-agree
          : ∀ {b} i (ieq : N .inputs c ! i ≡ b)
          → recₙ i ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq) (s .fst (orig b))
        tip-agree {b} i ieq =
            agree n (N .inputs c ! i)
              (Nat.≤-trans (N .depth-< c i) (Nat.≤-peel bnd))
          ∙ J (λ b' ieq'
                → s .fst (orig (N .inputs c ! i))
                ≡ subst (λ m → ∣ X₀ m ∣) (sym ieq') (s .fst (orig b')))
              (sym (transport-refl _))
              ieq

        go-c
          : ∀ (l : List (Fin (N .size))) (q : N .inputs c ≡ l)
          → go c recₙ (dec-of c) ≡ s .fst (orig c)
        go-c [] q = go-yes c recₙ (dec-of c) (ap length q)
        go-c (b ∷ []) q =
            go-no c recₙ (dec-of c) (single-not-input q)
          ∙ ap (d c) (sym (tuple-of (s .fst (orig b))
              (N .inputs c) (sym q) recₙ tip-agree))
          ∙ s .snd _ _ (single q)
        go-c (b ∷ b' ∷ bs) q =
            go-no c recₙ (dec-of c)
              (λ p → Nat.zero≠suc (sym p ∙ ap length q))
          ∙ ap (d c) (funext λ i →
                tip-agree i refl
              ∙ transport-refl _
              ∙ sym (s-tine {c} {fk} i)
              ∙ sym (happly s-socket i))
          ∙ s .snd _ _ (handle {c = c} {f = fk})
          where
            fk : is-fork N c
            fk = subst (2 Nat.≤_) (sym (ap length q))
              (Nat.s≤s (Nat.s≤s Nat.0≤x))

    agree-at : ∀ v → sec-at v ≡ s .fst v
    agree-at (orig c) = agree (suc (N .depth c)) c Nat.≤-refl
    agree-at (star c fk) = funext λ i →
        agree (suc (N .depth (N .inputs c ! i))) (N .inputs c ! i)
          Nat.≤-refl
      ∙ sym (s-tine {c} {fk} i)
    agree-at (tang c fk) = funext λ i →
        agree (suc (N .depth (N .inputs c ! i))) (N .inputs c ! i)
          Nat.≤-refl
      ∙ sym (s-tine {c} {fk} i)
      ∙ sym (happly (s-socket {c} {fk}) i)

  section-unique
    : ∀ (s : NSection) → section-of (restrict-inputs s) ≡ s
  section-unique s = Σ-prop-path
    (λ at → Π-is-hlevel 1 λ v → Π-is-hlevel 1 λ u → Π-is-hlevel 1 λ e →
      Act-is-set v (αₑ e (at u)) (at v))
    (funext (Unique.agree-at s))
```

**The unique-section theorem**: global sections of the dynamical
object are exactly tuples of input activities — a network computes.

```agda
  section≃inputs : NSection ≃ Inputs
  section≃inputs = Iso→Equiv
    ( restrict-inputs
    , iso section-of restrict-section section-unique)
```
