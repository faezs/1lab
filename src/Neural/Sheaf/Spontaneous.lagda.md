---
description: |
  Spontaneous activity: a sheaf on a DNN site whose value at a tang
  strictly exceeds the joint state of the fork's inputs — the sheaf
  condition constrains stars only, so the topos contains dynamics
  that are not feed-forward.
---
<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Site.Base
open import Cat.Prelude

open import Data.List.Base using (length ; _!_)
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Fin.Base

open import Neural.Topos.Extension
open import Neural.Poset.Reduced
open import Neural.Site.Topology
open import Neural.Graph.Fork

import Data.Nat.Base as Nat
```
-->

```agda
module Neural.Sheaf.Spontaneous where
```

# Spontaneous activity {defines="spontaneous-activity"}

Belfiore–Bennequin close §1.5 with a remark that chapter 3 turns
into a theme: the sheaves on a DNN site are *not* all feed-forward.
The sheaf condition forces the value at each star to be the product
of the tip values — but it says nothing about the *tangs*, whose
value may strictly exceed the joint state of the fork's inputs. The
gap is "spontaneous activity": internal states not determined by the
inputs.

Here we exhibit the phenomenon concretely, on the diamond network's
fork. Take the *constant* presheaf at `Bool`{.Agda} on the reduced
poset; its [[extension|presheaf-extension]] is a sheaf whose value at
the tang is `Bool`{.Agda}, while the joint input state is
`Bool × Bool`{.Agda} — too big to come from any feed-forward
dynamical object, whose tang value is by construction the product of
the tips.

```agda
private
  ConstBool : Functor ((Reduced diamond) ^op) (Sets lzero)
  ConstBool .Functor.F₀ _ = el! Bool
  ConstBool .Functor.F₁ _ x = x
  ConstBool .Functor.F-id = refl
  ConstBool .Functor.F-∘ _ _ = refl

  c-fork' : is-fork diamond (fin 2)
  c-fork' = Nat.s≤s (Nat.s≤s Nat.0≤x)

open Extend diamond ConstBool using (Ext ; Ext-is-sheaf ; Ext₀)
```

The extension is a sheaf — that is Proposition 1.1(iii), already
proven — and its value at the tang of the fork is `Bool`{.Agda},
whereas the product of the two tip values has four elements. No
equivalence can relate them:

```agda
spontaneous-sheaf : is-sheaf (fork-coverage diamond) Ext
spontaneous-sheaf = Ext-is-sheaf
```

The counting argument. Write $k_{tt}$, $k_{tf}$, $k_{ft}$ for three
of the four joint states; an injection of the joint states into
`Bool`{.Agda} sends them to three booleans, two of which must agree —
and each coincidence contradicts injectivity at one of the two
coordinates.

```agda
private
  Joint : Type
  Joint = (i : Fin (length (diamond .inputs (fin 2)))) → Bool

  k-tt k-tf k-ft : Joint
  k-tt _ = true
  k-tf (fin zero)    = true
  k-tf (fin (suc _)) = false
  k-ft (fin zero)    = false
  k-ft (fin (suc _)) = true

  third : (x y z : Bool) → ¬ x ≡ y → ¬ z ≡ x → z ≡ y
  third true  true  z     ¬xy ¬zx = absurd (¬xy refl)
  third false false z     ¬xy ¬zx = absurd (¬xy refl)
  third true  false true  ¬xy ¬zx = absurd (¬zx refl)
  third true  false false ¬xy ¬zx = refl
  third false true  false ¬xy ¬zx = absurd (¬zx refl)
  third false true  true  ¬xy ¬zx = refl

  no-injection : (f : Joint → Bool) → injective f → ⊥
  no-injection f inj with f k-tt ≡? f k-tf
  ... | yes p = true≠false (happly (inj p) (fsuc fzero))
  ... | no ¬p with f k-ft ≡? f k-tt
  ...   | yes q = true≠false (sym (happly (inj q) fzero))
  ...   | no ¬q = true≠false
    (sym (happly (inj (third (f k-tt) (f k-tf) (f k-ft) ¬p ¬q)) fzero))
```

And the headline: the tang value of the spontaneous sheaf — the
internal state the network maintains at the fork — admits no
equivalence with the joint state of the inputs. Sheaves on a DNN
site are strictly more general than feed-forward functionings, whose
tang values are by construction the products of their tips.

```agda
spontaneous
  : ¬ (Ext₀ (tang (fin 2) c-fork') ≃ Joint)
spontaneous e = no-injection (Equiv.from e)
  (Equiv.injective (Equiv.inverse e))
```
