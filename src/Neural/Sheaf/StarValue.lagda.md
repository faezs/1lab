---
description: |
  The sheaf condition at a star computes: for any sheaf on a forked
  DNN site, restriction along the tines is an equivalence between the
  value at a star and the product of the values at the fork's inputs.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude

open import Data.List.Base using (length ; _!_)
open import Data.Fin.Base

open import Neural.Site.Topology
open import Neural.Graph.Fork

import Cat.Functor.Reasoning.Presheaf as Psh
```
-->

```agda
module Neural.Sheaf.StarValue where
```

# The value of a sheaf at a star {defines="star-value"}

For a sheaf $A$ on the forked site of a network, the sheaf condition
at the [[tine coverage]] does exactly what Belfiore–Bennequin promise
in §1.3: it forces the value at each star $A^\star_c$ to be the
product of the values at the fork's inputs, with the tines acting as
the projections. This module proves that restriction along the
canonical tines

$$
A(A^\star_c) \longrightarrow \textstyle\prod_i A(\mathrm{orig}\,b_i)
$$

is an equivalence. It is the pointwise heart of the reduction of the
sheaf topos to presheaves on the reduced poset.

<!--
```agda
module _ {ℓ} (N : Network)
  (A : Functor ((fork-site N) ^op) (Sets ℓ))
  (shf : is-sheaf (fork-coverage N) A)
  where

  private
    module A = Psh A
    Γ = fork-graph N

  open Patch
```
-->

```agda
  star-restrict
    : ∀ {c} {f : is-fork N c}
    → A ʻ star c f → (∀ i → A ʻ orig (N .inputs c ! i))
  star-restrict x i = A.₁ (cons (tine i refl) nil) x
```

From a tuple of input values we build a patch over the tine sieve, by
recursion on the arrows of the sieve: a one-edge arrow is a tine and
selects a component, and a longer arrow restricts the patch of its
tail — the same free-generation induction as the sheaf condition for
the explicit sheafification.

```agda
  private
    tine-mem
      : ∀ {c} {f : is-fork N c} (i : Fin (length (N .inputs c)))
      → cons (tine {f = f} i refl) nil ∈ ⟦ tine-cover N c f ⟧
    tine-mem i = inc (i , nil , refl)

    module _ {c : Fin (N .size)} {f : is-fork N c}
      (t : ∀ i → A ʻ orig (N .inputs c ! i))
      where

      tine-case : ∀ {w} → F-edge N w (star c f) → A ʻ w
      tine-case (tine j q) = subst (λ m → A ʻ orig m) q (t j)

      part₀
        : ∀ {w} (g : Path-in Γ w (star c f)) → ∣ nonempty N g ∣
        → A ʻ w
      part₀ nil ne = absurd ne
      part₀ (cons e nil) ne = tine-case e
      part₀ (cons e (cons e' g)) ne =
        A.₁ (cons e nil) (part₀ (cons e' g) tt)

      part₀-cons
        : ∀ {m m'} (e : F-edge N m' m) (X : Path-in Γ m (star c f))
        → (neX : ∣ nonempty N X ∣) (ne' : ∣ nonempty N (cons e X) ∣)
        → part₀ (cons e X) ne' ≡ A.₁ (cons e nil) (part₀ X neX)
      part₀-cons e nil         neX ne' = absurd neX
      part₀-cons e (cons e' X) neX ne' = refl

      part₀-compat
        : ∀ {w w'} (g : Path-in Γ w (star c f)) (ne : ∣ nonempty N g ∣)
        → (h : Path-in Γ w' w) (ne' : ∣ nonempty N (h ++ g) ∣)
        → A.₁ h (part₀ g ne) ≡ part₀ (h ++ g) ne'
      part₀-compat g ne nil ne' =
        A.F-id ∙ ap (part₀ g) (nonempty N g .is-tr ne ne')
      part₀-compat g ne (cons e h) ne' =
          A.F-∘ (cons e nil) h
        ∙ ap (A.₁ (cons e nil)) (part₀-compat g ne h (++-nonempty-r N h ne))
        ∙ sym (part₀-cons e (h ++ g) (++-nonempty-r N h ne) ne')

      tuple-patch : Patch A ⟦ tine-cover N c f ⟧
      tuple-patch .part g hg =
        part₀ g (Equiv.to (covers-star-is-nonempty N g) hg)
      tuple-patch .patch g hg h hgh =
        part₀-compat g (Equiv.to (covers-star-is-nonempty N g) hg) h
          (Equiv.to (covers-star-is-nonempty N (h ++ g)) hgh)
```

The equivalence. The section is exactly the gluing property of the
sheaf at the canonical tines (with a transport at `refl` to unfold
the projection); injectivity is separatedness for the tine cover,
since two elements of $A(A^\star_c)$ with equal tine restrictions
agree on every arrow of the sieve by functoriality.

```agda
  star-restrict-is-equiv
    : ∀ {c} {f : is-fork N c}
    → is-equiv (star-restrict {c} {f})
  star-restrict-is-equiv {c} {f} = is-iso→is-equiv isom
    where
      restrict-agrees
        : ∀ {x : A ʻ star c f} {w} (g : Path-in Γ w (star c f))
        → (ne : ∣ nonempty N g ∣)
        → part₀ (star-restrict x) g ne ≡ A.₁ g x
      restrict-agrees {x} (cons (tine j q) nil) ne =
        J (λ b q → subst (λ m → A ʻ orig m) q
              (A.₁ (cons (tine {b = N .inputs c ! j} {f = f} j refl) nil) x)
            ≡ A.₁ (cons (tine {b = b} {f = f} j q) nil) x)
          (transport-refl _)
          q
      restrict-agrees {x} (cons e (cons e' g)) ne =
          ap (A.₁ (cons e nil)) (restrict-agrees {x = x} (cons e' g) tt)
        ∙ sym (A.F-∘ (cons e nil) (cons e' g))

      isom : is-iso (star-restrict {c} {f})
      isom .is-iso.from t = shf .is-sheaf.whole tt (tuple-patch t)
      isom .is-iso.rinv t = funext λ i →
          shf .is-sheaf.glues tt (tuple-patch t)
            (cons (tine i refl) nil) (tine-mem i)
        ∙ transport-refl (t i)
      isom .is-iso.linv x = shf .is-sheaf.separate tt λ g hg →
          shf .is-sheaf.glues tt (tuple-patch (star-restrict x)) g hg
        ∙ restrict-agrees g
            (Equiv.to (covers-star-is-nonempty N g) hg)
```
