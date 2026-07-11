---
description: |
  Proposition 1.1(i), repaired and strengthened: over a spacelike
  network, the entire forked site is thin and antisymmetric — a
  poset — and the reduced category of Belfiore–Bennequin is the full
  subposet on non-star vertices.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Prelude

open import Data.List.Base using (List ; [] ; _∷_ ; length ; _!_ ; ∷-head-inj)
open import Data.List.Properties
open import Data.Sum.Base
open import Data.Fin.Base

open import Order.Base

open import Neural.Poset.NoLoops
open import Neural.Poset.Reduced
open import Neural.Graph.Fork

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Poset.Thin where
```

# The forked site of a spacelike network is a poset {defines="fork-thin"}

This module proves the repaired form of Belfiore–Bennequin's
Proposition 1.1(i), strengthened from the reduced category to the
whole site: for a [[spacelike]] network, *every* hom-set of the
forked site is a proposition, and the resulting thin category is
antisymmetric. The [[counterexample|spacelike]] in
`Neural.Poset.Reduced` shows the hypothesis is necessary.

The engine is a code construction in the style of
`path-codep`{.Agda}: given two parallel paths (their sources joined
by an identification, to keep the induction K-free), we produce a
code for an identification between them, by case analysis on their
first edges. The spacelike hypothesis enters in exactly two places:
it makes *every* edge type a proposition (two tines into the same
star from the same vertex must use the same position), and it kills
the mixed configurations where one path takes a tine directly while
the other first descends a single-input chain.

<!--
```agda
module _ (N : Network) (sp : is-spacelike N) where
  private
    Γ  = fork-graph N
    Γ₀ = network-graph N

    suc≰self : ∀ x → Nat.suc x Nat.≤ x → ⊥
    suc≰self zero    p = Nat.¬suc≤0 p
    suc≰self (suc x) p = suc≰self x (Nat.≤-peel p)
```
-->

## Edges are propositions

```agda
  private
    shape-is-prop : ∀ x y → is-prop (F-edge-shape N x y)
    shape-is-prop (orig c) (orig b) = hlevel 2 (N .inputs c) (b ∷ [])
    shape-is-prop (orig b) (star c f) (i , q) (i' , q') =
      λ k → ieq k , qeq k
      where
        ieq : i ≡ i'
        ieq = sp .tips-incomparable c i i'
          (subst (λ m → Path-in Γ₀ (N .inputs c ! i) m) (q ∙ sym q') nil)

        qeq : PathP (λ k → N .inputs c ! ieq k ≡ b) q q'
        qeq = is-prop→pathp (λ k → hlevel 2 (N .inputs c ! ieq k) b) q q'
    shape-is-prop (orig c) (tang c' f)    = hlevel 2 c c'
    shape-is-prop (star c f) (tang c' f') = hlevel 2 c c'
    shape-is-prop (star c f) (orig b)     = hlevel 1
    shape-is-prop (star c f) (star c' f') = hlevel 1
    shape-is-prop (tang c f) _            = hlevel 1

  F-edge-is-prop : ∀ {x y} → is-prop (F-edge N x y)
  F-edge-is-prop {x} {y} = retract→is-hlevel 1
    (shape→edge N) (edge→shape N) (shape→edge→shape N)
    (shape-is-prop x y)
```

## The code construction

<!--
```agda
  private
    tp-ne
      : ∀ {v u u'} (e : u ≡ u') (p : Path-in Γ v u)
      → ∣ nonempty N p ∣ → ∣ nonempty N (subst (Path-in Γ v) e p) ∣
    tp-ne {v} e p hp = J
      (λ u' e → ∣ nonempty N (subst (Path-in Γ v) e p) ∣)
      (subst (λ z → ∣ nonempty N z ∣) (sym (transport-refl p)) hp)
      e

    tp-ne-l
      : ∀ {v v' u} (e : v ≡ v') (p : Path-in Γ v u)
      → ∣ nonempty N p ∣ → ∣ nonempty N (subst (λ m → Path-in Γ m u) e p) ∣
    tp-ne-l {u = u} e p hp = J
      (λ v' e → ∣ nonempty N (subst (λ m → Path-in Γ m u) e p) ∣)
      (subst (λ z → ∣ nonempty N z ∣) (sym (transport-refl p)) hp)
      e

    epathp
      : ∀ {x x' m m'} (kk : x ≡ x') (bs : m ≡ m')
      → (e : F-edge N x m) (e' : F-edge N x' m')
      → PathP (λ i → F-edge N (kk i) (bs i)) e e'
    epathp kk bs = is-prop→pathp (λ i → F-edge-is-prop {kk i} {bs i})
```
-->

The mixed-route contradictions, shared by the symmetric cases below.
`clash-tang` refutes a pair of parallel paths into a tang where one
starts with a tine and the other with a single-input transmission;
`clash-star` is the analogue for a star target.

```agda
  private
    clash-star
      : ∀ {a a' c fc b₁} (aeq : a ≡ a')
      → (i₂ : Fin (length (N .inputs c))) → N .inputs c ! i₂ ≡ a'
      → N .inputs a ≡ b₁ ∷ []
      → Path-in Γ (orig b₁) (star c fc)
      → ⊥
    clash-star {a} {a'} {c} {fc} {b₁} aeq i₂ q₂ q₁ p₁ =
      let
        (j , γ , ne) = reach-star-from-single N q₁ p₁

        tipa : N .inputs c ! i₂ ≡ a
        tipa = q₂ ∙ sym aeq

        jeq : j ≡ i₂
        jeq = sp .tips-incomparable c j i₂
          (subst (λ m → Path-in Γ₀ (N .inputs c ! j) m) (sym tipa) γ)
      in network-loop N γ (ap (λ k → N .inputs c ! k) jeq ∙ tipa) ne

    clash-tang
      : ∀ {a a' c fc b₁} (aeq : a ≡ a')
      → (i₂ : Fin (length (N .inputs c))) → N .inputs c ! i₂ ≡ a'
      → N .inputs a ≡ b₁ ∷ []
      → Path-in Γ (orig b₁) (tang c fc)
      → ⊥
    clash-tang {a} {a'} {c} {fc} {b₁} aeq i₂ q₂ q₁ p₁ with reach-from-single N q₁ p₁
    ... | inl (γ , ne) = suc≰self (N .depth a)
      (Nat.≤-trans (edge-depth-< N (i₂ , q₂ ∙ sym aeq)) (path-depth-≤ N γ))
    ... | inr (j , γ , ne) =
      let
        tipa : N .inputs c ! i₂ ≡ a
        tipa = q₂ ∙ sym aeq

        jeq : j ≡ i₂
        jeq = sp .tips-incomparable c j i₂
          (subst (λ m → Path-in Γ₀ (N .inputs c ! j) m) (sym tipa) γ)
      in network-loop N γ (ap (λ k → N .inputs c ! k) jeq ∙ tipa) ne
```

The code itself. Parallel empty paths are equal; an empty path
parallel to a nonempty one yields a loop; and for two nonempty
paths, the sixteen combinations of first edges are either compatible
(equal middle vertices, edges identified by propositionality, tails
by recursion), refuted by a vertex-type discrimination across the
source identification, or refuted by the clash lemmas and the
depth arguments.

```agda
  thin-code
    : ∀ {x x' y} (kk : x ≡ x')
    → (p : Path-in Γ x y) (q : Path-in Γ x' y)
    → path-codep Γ (λ i → kk i) p q
  thin-code kk nil nil = lift tt
  thin-code kk nil (cons e q) = absurd (no-loop N
    (subst (Path-in Γ _) kk (cons e q))
    (tp-ne kk (cons e q) tt))
  thin-code kk (cons e p) nil = absurd (no-loop N
    (subst (λ m → Path-in Γ m _) kk (cons e p))
    (tp-ne-l kk (cons e p) tt))

  -- single / single
  thin-code kk (cons (single q₁) p₁) (cons (single q₂) q₁') =
    bs , epathp kk bs _ _ , thin-code bs p₁ q₁'
    where
      bs : _ ≡ _
      bs = ap orig (∷-head-inj
        (sym q₁ ∙ ap (N .inputs) (ap (vtx-name N) kk) ∙ q₂))

  -- handle / handle
  thin-code kk (cons handle p₁) (cons handle q₁) =
    bs , epathp kk bs _ _ , thin-code bs p₁ q₁
    where
      bs : _ ≡ _
      bs = path-out-of-tang-is-nil N p₁ .fst
         ∙ sym (path-out-of-tang-is-nil N q₁ .fst)

  -- socket / socket
  thin-code kk (cons socket p₁) (cons socket q₁) =
    bs , epathp kk bs _ _ , thin-code bs p₁ q₁
    where
      bs : _ ≡ _
      bs = path-out-of-tang-is-nil N p₁ .fst
         ∙ sym (path-out-of-tang-is-nil N q₁ .fst)

  -- tine / tine
  thin-code kk (cons (tine i₁ q₁) nil) (cons (tine i₂ q₂) nil) =
    refl , epathp kk refl _ _ , lift tt
  thin-code kk (cons (tine i₁ q₁) nil) (cons (tine i₂ q₂) (cons socket t)) =
    absurd (subst is-tang-vtx' (path-out-of-tang-is-nil N t .fst) tt)
    where is-tang-vtx' = is-tang-vtx N
  thin-code kk (cons (tine i₁ q₁) (cons socket t)) (cons (tine i₂ q₂) nil) =
    absurd (subst (is-tang-vtx N) (path-out-of-tang-is-nil N t .fst) tt)
  thin-code kk (cons (tine {c = c₁} {f = f₁} i₁ q₁) (cons socket t₁))
               (cons (tine {c = c₂} {f = f₂} i₂ q₂) (cons socket t₂)) =
    bs , epathp kk bs _ _ ,
    (bs' , epathp bs bs' _ _ , thin-code bs' t₁ t₂)
    where
      bs' : _ ≡ _
      bs' = path-out-of-tang-is-nil N t₁ .fst
          ∙ sym (path-out-of-tang-is-nil N t₂ .fst)

      fkp : PathP (λ i → is-fork N (ap (vtx-name N) bs' i)) f₁ f₂
      fkp = is-prop→pathp (λ i → Nat.≤-is-prop) f₁ f₂

      bs : star c₁ f₁ ≡ star c₂ f₂
      bs = λ i → star (ap (vtx-name N) bs' i) (fkp i)

  -- single / tine and tine / single: the spacelike clashes
  thin-code kk (cons (single q₁) p₁) (cons (tine i₂ q₂) nil) =
    absurd (clash-star (ap (vtx-name N) kk) i₂ q₂ q₁ p₁)
  thin-code kk (cons (single q₁) p₁) (cons (tine i₂ q₂) (cons socket t)) =
    absurd (clash-tang (ap (vtx-name N) kk) i₂ q₂ q₁
      (subst (Path-in Γ _) (sym (path-out-of-tang-is-nil N t .fst)) p₁))
  thin-code kk (cons (tine i₂ q₂) nil) (cons (single q₁) p₁) =
    absurd (clash-star (ap (vtx-name N) (sym kk)) i₂ q₂ q₁ p₁)
  thin-code kk (cons (tine i₂ q₂) (cons socket t)) (cons (single q₁) p₁) =
    absurd (clash-tang (ap (vtx-name N) (sym kk)) i₂ q₂ q₁
      (subst (Path-in Γ _) (sym (path-out-of-tang-is-nil N t .fst)) p₁))

  -- single / handle and handle / single: forks have no single input
  thin-code kk (cons (single q₁) p₁) (cons (handle {f = f'}) q₁') =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (subst (2 Nat.≤_) (ap length q₁)
      (subst (λ m → 2 Nat.≤ length (N .inputs m))
        (sym (ap (vtx-name N) kk)) f'))))
  thin-code kk (cons (handle {f = f'}) q₁') (cons (single q₁) p₁) =
    absurd (Nat.¬suc≤0 (Nat.≤-peel (subst (2 Nat.≤_) (ap length q₁)
      (subst (λ m → 2 Nat.≤ length (N .inputs m))
        (ap (vtx-name N) kk) f'))))

  -- tine / handle and handle / tine: a fork is never its own tip
  thin-code kk (cons (tine i₁ q₁) (cons socket t₁)) (cons handle t₂) =
    absurd (Nat.<-irrefl refl (edge-depth-< N (i₁ ,
      q₁ ∙ ap (vtx-name N) kk ∙ sym (ap (vtx-name N)
        (path-out-of-tang-is-nil N t₁ .fst
          ∙ sym (path-out-of-tang-is-nil N t₂ .fst))))))
  thin-code kk (cons (tine i₁ q₁) nil) (cons handle t₂) =
    absurd (subst (is-tang-vtx N)
      (path-out-of-tang-is-nil N t₂ .fst) tt)
  thin-code kk (cons handle t₂) (cons (tine i₁ q₁) (cons socket t₁)) =
    absurd (Nat.<-irrefl refl (edge-depth-< N (i₁ ,
      q₁ ∙ ap (vtx-name N) (sym kk) ∙ sym (ap (vtx-name N)
        (path-out-of-tang-is-nil N t₁ .fst
          ∙ sym (path-out-of-tang-is-nil N t₂ .fst))))))
  thin-code kk (cons handle t₂) (cons (tine i₁ q₁) nil) =
    absurd (subst (is-tang-vtx N)
      (path-out-of-tang-is-nil N t₂ .fst) tt)

  -- source-type clashes across kk
  thin-code kk (cons (single q₁) p₁) (cons socket q₁') =
    absurd (subst (is-orig-vtx N) kk tt)
  thin-code kk (cons (tine i₁ q₁) p₁) (cons socket q₁') =
    absurd (subst (is-orig-vtx N) kk tt)
  thin-code kk (cons handle p₁) (cons socket q₁') =
    absurd (subst (is-orig-vtx N) kk tt)
  thin-code kk (cons socket p₁) (cons (single q₁) q₁') =
    absurd (subst (is-star-vtx N) kk tt)
  thin-code kk (cons socket p₁) (cons (tine i₁ q₁) q₁') =
    absurd (subst (is-star-vtx N) kk tt)
  thin-code kk (cons socket p₁) (cons handle q₁') =
    absurd (subst (is-star-vtx N) kk tt)
```

## The poset

```agda
  fork-hom-is-prop : ∀ {x y} → is-prop (Path-in Γ x y)
  fork-hom-is-prop p q = path-encode Γ _ p q (thin-code refl p q)

  fork-antisym : ∀ {x y} → Path-in Γ x y → Path-in Γ y x → x ≡ y
  fork-antisym nil        q = refl
  fork-antisym (cons e p) q = absurd
    (no-loop N (q ++ cons e p) (++-nonempty-r N q tt))

  fork-poset : Poset lzero lzero
  fork-poset .Poset.Ob = F-vtx N
  fork-poset .Poset._≤_ x y = Path-in Γ x y
  fork-poset .Poset.≤-thin = fork-hom-is-prop
  fork-poset .Poset.≤-refl = nil
  fork-poset .Poset.≤-trans p q = p ++ q
  fork-poset .Poset.≤-antisym = fork-antisym
```

And the paper's statement: the reduced category — the full
subcategory on ordinary and tang vertices — is the poset
$\mathbf{X}$ that the rest of chapter 1 works over.

```agda
  private
    is-plain-is-prop : (v : F-vtx N) → is-prop (is-plain v)
    is-plain-is-prop (orig c)   = hlevel 1
    is-plain-is-prop (star c f) = hlevel 1
    is-plain-is-prop (tang c f) = hlevel 1

  reduced-poset : Poset lzero lzero
  reduced-poset .Poset.Ob = Σ[ v ∈ F-vtx N ] is-plain v
  reduced-poset .Poset._≤_ (x , _) (y , _) = Path-in Γ x y
  reduced-poset .Poset.≤-thin = fork-hom-is-prop
  reduced-poset .Poset.≤-refl = nil
  reduced-poset .Poset.≤-trans p q = p ++ q
  reduced-poset .Poset.≤-antisym p q =
    Σ-prop-path is-plain-is-prop (fork-antisym p q)
```
