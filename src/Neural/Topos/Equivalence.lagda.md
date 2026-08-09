---
description: |
  The corollary of Proposition 1.1: the sheaf topos of a DNN site is
  equivalent to presheaves on the reduced category, by restriction,
  with the extension functor providing the section and the star-value
  equivalence providing fullness and faithfulness.
---
<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open import Data.List.Base using (length ; _!_)
open import Data.Fin.Base

open import Neural.Sheaf.StarValue
open import Neural.Topos.Extension
open import Neural.Poset.Reduced
open import Neural.Site.Topology
open import Neural.Graph.Fork

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning
```
-->

```agda
module Neural.Topos.Equivalence where
```

# The topos of a network is presheaves on its poset {defines="dnn-topos-equivalence"}

The corollary to Proposition 1.1 in Belfiore–Bennequin: the sheaf
topos $\mathrm{Sh}(C, J)$ of a DNN's forked site is equivalent to
the category of presheaves on the reduced category $C_{\mathbf X}$.
We prove it by exhibiting *restriction along the plain vertices* as
fully faithful and split essentially surjective: the section of
restriction is the [[extension|presheaf-extension]] functor, and
both fullness and faithfulness reduce to the [[star-value]]
equivalence — a sheaf has no information at a star beyond the tuple
of its tip values.

Note the direction of the economy: no comparison-lemma or
dense-subsite machinery is required; the finite, free structure of
the site lets everything be computed.

<!--
```agda
module _ {ℓ} (N : Network) where
  private
    Γ = fork-graph N

    SheafCat : Precategory _ _
    SheafCat = Sheaves (fork-coverage N) ℓ

    PShX : Precategory _ _
    PShX = PSh ℓ (Reduced N)

  open Functor
  open _=>_
```
-->

## Restriction

A presheaf on the site restricts to the reduced category by applying
it to plain vertices and to the paths between them (which are the
same thing as reduced morphisms).

```agda
  Res₀ : Functor ((fork-site N) ^op) (Sets ℓ) → ⌞ PShX ⌟
  Res₀ A .F₀ (v , _) = A .F₀ v
  Res₀ A .F₁ p = A .F₁ p
  Res₀ A .F-id = A .F-id
  Res₀ A .F-∘ = A .F-∘

  Res : Functor SheafCat PShX
  Res .F₀ (A , _) = Res₀ A
  Res .F₁ h .η (v , _) = h .η v
  Res .F₁ h .is-natural (u , _) (v , _) p = h .is-natural u v p
  Res .F-id = ext λ _ _ → refl
  Res .F-∘ f g = ext λ _ _ → refl
```

## Essential surjectivity

The extension of a presheaf restricts back to it: the components are
identities, and naturality is the statement that the extension's
fold of edge actions agrees with the original presheaf on any path
between plain vertices — proven by peeling the path one edge (or,
through a star, one tine–socket pair) at a time.

```agda
  module _ (F : ⌞ PShX ⌟) where
    private
      module F = Psh F
      open Extend N F using (ORIG ; TANG ; Ext₀ ; ρₑ ; ρ ; Ext ; Ext-is-sheaf)

      val : ∀ {v} (pl : is-plain {N} v) → Ext₀ v → F ʻ (v , pl)
      val {orig c}   pl x = x
      val {star c f} pl x = absurd pl
      val {tang c f} pl x = x

      unval : ∀ {v} (pl : is-plain {N} v) → F ʻ (v , pl) → Ext₀ v
      unval {orig c}   pl x = x
      unval {star c f} pl x = absurd pl
      unval {tang c f} pl x = x

      val-unval
        : ∀ {v} (pl : is-plain {N} v) (x : F ʻ (v , pl))
        → val pl (unval pl x) ≡ x
      val-unval {orig c}   pl x = refl
      val-unval {star c f} pl x = absurd pl
      val-unval {tang c f} pl x = refl

      unval-val
        : ∀ {v} (pl : is-plain {N} v) (x : Ext₀ v)
        → unval pl (val pl x) ≡ x
      unval-val {orig c}   pl x = refl
      unval-val {star c f} pl x = absurd pl
      unval-val {tang c f} pl x = refl

    ρ-plain
      : ∀ {u v} (pu : is-plain {N} u) (pv : is-plain {N} v)
      → (p : Path-in Γ u v) (x : Ext₀ v)
      → val pu (ρ p x) ≡ F.₁ {v , pv} {u , pu} p (val pv x)
    ρ-plain {orig a}   pu pv nil x = sym F.F-id
    ρ-plain {star c f} pu pv nil x = absurd pu
    ρ-plain {tang c f} pu pv nil x = sym F.F-id
    ρ-plain {orig a} pu pv (cons (single q) p) x =
        ap (ρₑ (single q)) (ρ-plain tt pv p x)
      ∙ sym (F.F-∘ (cons (single q) nil) p)
    ρ-plain {orig a} pu pv (cons handle p) x =
        ap (ρₑ handle) (ρ-plain tt pv p x)
      ∙ sym (F.F-∘ (cons handle nil) p)
    ρ-plain {orig a} pu pv (cons (tine {c = c} {f = fk} i q) nil) x =
      absurd pv
    ρ-plain {orig a} pu pv (cons (tine {c = c} {f = fk} i q) (cons socket p)) x =
      J (λ b q →
          ∀ (pu : is-plain {N} (orig b))
          → val pu (ρ (cons (tine {b = b} {c = c} {f = fk} i q) (cons socket p)) x)
          ≡ F.₁ {_ , pv} {orig b , pu}
              (cons (tine {b = b} {c = c} {f = fk} i q) (cons socket p)) (val pv x))
        (λ pu →
            transport-refl _
          ∙ ap (F.₁ (cons (tine i refl) (cons socket nil)))
              (ρ-plain tt pv p x)
          ∙ sym (F.F-∘ (cons (tine i refl) (cons socket nil)) p))
        q pu
    ρ-plain {star c f} pu pv (cons socket p) x = absurd pu

    Res-Ext≅ : Cat.Reasoning._≅_ PShX (Res₀ Ext) F
    Res-Ext≅ = Cat.Reasoning.make-iso PShX to from
      (ext λ where (v , pl) x → val-unval pl x)
      (ext λ where (v , pl) x → unval-val pl x)
      where
        to : Res₀ Ext => F
        to .η (v , pl) = val pl
        to .is-natural (u , pu) (v , pv) p = funext λ x →
          ρ-plain pv pu p x

        from : F => Res₀ Ext
        from .η (v , pl) = unval pl
        from .is-natural (u , pu) (v , pv) p = funext λ x →
            ap (unval pv ⊙ F.₁ p) (sym (val-unval pu x))
          ∙ ap (unval pv) (sym (ρ-plain pv pu p (unval pu x)))
          ∙ unval-val pv (ρ p (unval pu x))

  Res-is-split-eso : is-split-eso Res
  Res-is-split-eso F = (Extend.Ext N F , Extend.Ext-is-sheaf N F) , Res-Ext≅ F
```

## Full faithfulness

A morphism of sheaves is determined by its components at the plain
vertices: at a star, the [[star-value]] equivalence forces the
component to be the conjugate of the tuple of plain components. This
gives the inverse to the action of `Res`{.Agda} on morphisms;
naturality of the reconstruction is a per-edge check, with the tine
and socket squares closing by the unit and counit of the star-value
equivalence.

```agda
  module _ {AS BS : ⌞ SheafCat ⌟} where
    private
      A = AS .fst
      B = BS .fst
      module A = Psh (AS .fst)
      module B = Psh (BS .fst)

      rB : ∀ {c} {f : is-fork N c}
         → (B ʻ star c f) ≃ (∀ i → B ʻ orig (N .inputs c ! i))
      rB {c} {f} = star-restrict N B (BS .snd) {c} {f} ,
        star-restrict-is-equiv N B (BS .snd) {c} {f}

    private module _ (φ : Res₀ A => Res₀ B) where
      ψ₀ : ∀ v → A ʻ v → B ʻ v
      ψ₀ (orig c)   = φ .η (orig c , tt)
      ψ₀ (tang c f) = φ .η (tang c f , tt)
      ψ₀ (star c f) x = Equiv.from rB λ i →
        φ .η (orig (N .inputs c ! i) , tt)
          (A.₁ (cons (tine i refl) nil) x)

      ψ-edge
        : ∀ {u v} (e : F-edge N u v) (x : A ʻ v)
        → ψ₀ u (A.₁ (cons e nil) x) ≡ B.₁ (cons e nil) (ψ₀ v x)
      ψ-edge (single q) x = happly (φ .is-natural _ _ (cons (single q) nil)) x
      ψ-edge handle     x = happly (φ .is-natural _ _ (cons handle nil)) x
      ψ-edge (tine {b = b} {c = c} {f = fk} i q) x =
        J (λ b q
            → ψ₀ (orig b) (A.₁ (cons (tine {b = b} {c = c} {f = fk} i q) nil) x)
            ≡ B.₁ (cons (tine {b = b} {c = c} {f = fk} i q) nil) (ψ₀ (star c fk) x))
          (sym (happly (Equiv.ε rB _) i))
          q
      ψ-edge (socket {c = c} {f = fs} {f' = fs'}) x =
        Equiv.injective rB $ funext λ i →
            happly (Equiv.ε rB _) i
          ∙ ap (φ .η _) (sym (A.F-∘ (cons (tine i refl) nil) (cons socket nil)))
          ∙ happly (φ .is-natural _ _
              (cons (tine i refl) (cons (socket {f = fs} {f' = fs'}) nil))) x
          ∙ B.F-∘ (cons (tine i refl) nil) (cons socket nil)

      ψ-nat
        : ∀ {u v} (p : Path-in Γ u v) (x : A ʻ v)
        → ψ₀ u (A.₁ p x) ≡ B.₁ p (ψ₀ v x)
      ψ-nat {u} nil x = ap (ψ₀ u) A.F-id ∙ sym B.F-id
      ψ-nat (cons e p) x =
          ap (ψ₀ _) (A.F-∘ (cons e nil) p)
        ∙ ψ-edge e (A.₁ p x)
        ∙ ap (B.₁ (cons e nil)) (ψ-nat p x)
        ∙ sym (B.F-∘ (cons e nil) p)

      ψ : A => B
      ψ ._=>_.η = ψ₀
      ψ ._=>_.is-natural u v p = funext (ψ-nat p)

    Res-is-ff : is-equiv (Res .F₁ {AS} {BS})
    Res-is-ff = is-iso→is-equiv isom where
      isom : is-iso (Res .F₁ {AS} {BS})
      isom .is-iso.from = ψ
      isom .is-iso.rinv φ = ext λ where
        (orig c   , pl) x → refl
        (tang c f , pl) x → refl
        (star c f , pl) x → absurd pl
      isom .is-iso.linv h = ext λ where
        (orig c)   x → refl
        (tang c f) x → refl
        (star c f) x →
            ap (Equiv.from rB) (funext λ i →
              happly (h .is-natural _ _ (cons (tine i refl) nil)) x)
          ∙ Equiv.η rB (h .η (star c f) x)
```

Assembling, we obtain the corollary of Proposition 1.1: **the topos
of a deep neural network is the presheaf topos on its poset of
layers and joints**.

```agda
  Res-is-equivalence : is-equivalence Res
  Res-is-equivalence = ff+split-eso→is-equivalence
    (λ {AS} {BS} → Res-is-ff {AS} {BS})
    Res-is-split-eso
```
