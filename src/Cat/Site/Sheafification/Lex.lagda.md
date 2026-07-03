<!--
```agda
open import Cat.Functor.Hom.Yoneda
open import Cat.Site.Sheafification
open import Cat.Diagram.Terminal
open import Cat.Functor.Hom
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open Functor
open _=>_
```
-->

```agda
module Cat.Site.Sheafification.Lex
  {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  where
```

# Towards left exactness of sheafification {defines="lex-sheafification"}

For the category of sheaves on a site to be a [[topos]] in the
official sense — a *lex-reflective* subcategory of presheaves — the
sheafification reflector must preserve finite limits. This module
proves the first half of left exactness for the 1Lab's
higher-inductive sheafification, over an *arbitrary* coverage: the
sheafification of any terminal presheaf is terminal among sheaves.
The key is that both halves of the sheaf condition appear as
constructors of the higher inductive type: gluing lets us *build*
points, and separation (`sep`{.Agda}) lets us *compare* them cover
by cover, which is exactly what a contractibility proof by
induction needs.

A terminal presheaf is pointwise contractible, by the Yoneda lemma.

```agda
module _ (T : Functor (C ^op) (Sets ℓ)) (term : is-terminal (PSh ℓ C) T) where
  open Sheafification J T

  private
    T-contr : ∀ U → is-contr (T ʻ U)
    T-contr U = Equiv→is-hlevel 0 (yo T , yo-is-equiv T) (term (Hom-into C U))
```

The sheafification of a pointwise contractible presheaf is pointwise
contractible: the centre is the inclusion of the centre, and the
induction principle reduces the path-space to two cases. On
inclusions, contractibility of $T$ answers directly; on a point that
is only *locally* known, separation reduces the comparison to the
patches of a cover, where naturality of the inclusion and
contractibility of $T$ finish.

```agda
  private
    inc-path
      : ∀ {V} {x y : T ʻ V} → x ≡ y
      → Path (Sheafify₀ V) (inc x) (inc y)
    inc-path = ap inc

  private abstract
    contr-paths : ∀ {U} (x : Sheafify₀ U) → inc (T-contr U .centre) ≡ x
    contr-paths = Sheafify-elim-prop
      (λ {V} x → inc (T-contr V .centre) ≡ x)
      (λ x → squash _ _)
      (λ {V} x → inc-path (T-contr V .paths x))
      (λ {V} c x loc → sep c λ {W} f hf →
          sym (inc-natural (T-contr V .centre))
        ∙ inc-path (is-contr→is-prop (T-contr W) _ _)
        ∙ loc f hf)

  Sheafify-⊤-is-contr : ∀ U → is-contr (Sheafify₀ U)
  Sheafify-⊤-is-contr U .centre = inc (T-contr U .centre)
  Sheafify-⊤-is-contr U .paths = contr-paths
```

Packaging: since sheaves form a full subcategory of presheaves, a
pointwise contractible sheaf receives a unique map from anything.

```agda
  Sheafification-pres-⊤
    : is-terminal (Sheaves J ℓ) (Sheafify , Sheafify-is-sheaf)
  Sheafification-pres-⊤ F .centre .η V _ =
    Sheafify-⊤-is-contr V .centre
  Sheafification-pres-⊤ F .centre .is-natural V W f = funext λ a →
    is-contr→is-prop (Sheafify-⊤-is-contr W) _ _
  Sheafification-pres-⊤ F .paths g = Nat-path λ V → funext λ a →
    is-contr→is-prop (Sheafify-⊤-is-contr V) _ _
```

## What remains

The second half of left exactness — preservation of pullbacks — is
the genuinely hard part, and we record precisely where the
difficulty lives. Pullbacks of sheaves are computed as presheaf
pullbacks, so preservation amounts to: the canonical map from the
sheafification of a pullback to the pullback of sheafifications is
an isomorphism, pointwise. Surjectivity-up-to-covers is within reach
of the induction principle above (every point of a sheafification
is locally an inclusion). The obstruction is *injectivity*: one must
characterise when two inclusions `inc x ≡ inc y`{.Agda} agree, and
for a one-step higher-inductive sheafification this is a path-space
problem — the classical plus-construction is applied *twice*
precisely to make such equalities locally detectable in the
original presheaf. A proof will need either an encode–decode
characterisation of the HIT's path spaces or a formalisation of the
two-step construction; we leave it, precisely delimited, as the
remaining gap between `Sh[_,_]`{.Agda} and `Topos`{.Agda}.
