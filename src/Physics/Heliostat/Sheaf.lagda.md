<!--
```agda
{-# OPTIONS --lossy-unification #-}
import Cat.Instances.FormalSmoothSets
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Hom
open import Cat.Functor.Base
open import Cat.Prelude

open import Algebra.Ring.Commutative

open import Data.Fin using (Fin)

open import Physics.Heliostat.Optics

import Cat.Instances.Presheaf.Germs
import Algebra.Ring.Polynomial
import Cat.Instances.Presheaf.Concrete
import Cat.Instances.FormalSmoothSets.DeRham

open Precategory
open Functor
open _=>_
```
-->

```agda
module Physics.Heliostat.Sheaf where
```

# The aiming section is built from germs {defines="aiming-section ray-sheaf germ-of-the-aiming-field"}

A heliostat's control software carries, at each point of the mirror, the
direction it must throw the sun: a `ray_sheaf` whose sections are
aiming fields and whose stalks — in the C comment that named this
module, *"the section is built from germs"* — are the local pieces from
which a global aiming field is glued. This module makes that phrase
literal. Following Giotopoulos and Sati's *Field Theory via Higher
Geometry I* [@GiotopoulosSati:FieldTheory] and Schreiber's *Higher
Topos Theory in Physics* [@Schreiber:HTTPhysics], we read the aiming
field as a **plot of a [[formal smooth set|formal-smooth-sets]]** over
the reflector's own probe site — the infinitesimally
[[thickened Cartesian spaces|thickened-cartesian-space]]
$\rm{ThCartSp}$ — and its stalks as the
[[germs of that plot|germ-of-a-plot]] in Schreiber's diagrams (5) and
(6): germs are a set-quotient of plots, and maps of aiming fields
descend to germs.

The mirror is a two-dimensional probe. The `Physics.Heliostat.Optics`{.Agda}
computation of the reflected ray already lives over exactly this probe:
its observable ring is the polynomial ring $R[u,v]$ in the two mirror
coordinates, and *that is definitionally the function ring of the probe*
$\bA^2$ in `Cat.Instances.FormalSmoothSets`{.Agda}. So the synthetic
aiming computation, verbatim, **is** a plot of the line $\bA^1$ by the
mirror probe $\bA^2$; the sheaf-theoretic apparatus of germs is laid on
top of it without changing a symbol.

**The honest scope, stated up front.** Over this *formal* (polynomial)
site the thickening inclusions are injective, so restriction along a
neighbourhood loses no information and the germ relation collapses to
equality: **germs over the formal site coincide with plots.** The 1Lab
ships only the [[discrete neighbourhood structure|neighbourhood-structure]]
(`Cat.Instances.Presheaf.Germs`{.Agda}), and
`germs-discrete-is-equiv`{.Agda} makes the identification precise. The
genuinely *shrinking* infinitesimal neighbourhoods of the smooth site —
which would make germ-locality strictly weaker than globality — do
**not** exist here; per the reading guide `Physics`{.Agda}, "the
smooth-site instance of (7) … with shrinking-neighbourhood germs"
remains the analytic gap, waiting on a real-numbers object. We prove the
trivial/discrete theorem — *the section is its own germ* — and claim
nothing beyond it.

```agda
module sheaf {ℓ} (R : CRing ℓ) where
```

<!--
```agda
  open Algebra.Ring.Polynomial R
```
-->

We open the three ingredients: the site and its line, the synthetic
optics over the observable ring, and the germ machinery specialised to
this site.

```agda
  open Cat.Instances.FormalSmoothSets R
  open Physics.Heliostat.Optics.optics R
  open Physics.Heliostat.Optics.euclid (R[ Lift ℓ (Fin 2) ])
  open Cat.Instances.Presheaf.Concrete ThCartSp pt-terminal
  open Cat.Instances.FormalSmoothSets.DeRham R using (Ω¹-dR ; Ω¹-dR-not-concrete)
  module G = Cat.Instances.Presheaf.Germs ThCartSp
```

## The mirror probe, and the definitional coincidence

The reflector's probe is the un-thickened plane $\bA^2 = $ `𝔸 2 0`. Its
function ring is, *by definition* of `O∙`{.Agda} in
`Cat.Instances.FormalSmoothSets`{.Agda}, the polynomial ring on two
generators — which is the very ring `Physics.Heliostat.Optics`{.Agda}
calls the observable ring $\rm{Obs}$. We record the coincidence as a
`refl`{.Agda}: the mirror probe's functions and the optics observables
are the same type on the nose.

```agda
  mirror : ThAff
  mirror = 𝔸 2 0

  Obs-is-mirror-functions : ⌞ O mirror ⌟ ≡ ⌞ R[ Lift ℓ (Fin 2) ] ⌟
  Obs-is-mirror-functions = refl
```

Because $\bA^1$ is representable, a plot of the line by the mirror probe
— an element of $\bA^1(\bA^2)$ — is by full faithfulness of the Yoneda
embedding just a probe map `ThHom mirror (𝔸 1 0)`, and by
`plots-𝔸¹`{.Agda} that is the same as one ring element of `O mirror`.
This is the bridge: **a mirror-coordinate polynomial is a plot of the
line.**

```agda
  plot-of-line : ⌞ O mirror ⌟ → ∣ 𝔸¹ .F₀ mirror ∣
  plot-of-line c = Equiv.from (plots-𝔸¹ mirror) c
```

## The aiming section as a plot

The synthetic aiming field is `reflect incoming (normal Q)`{.Agda} from
`Physics.Heliostat.Optics`{.Agda}: the axial solar ray reflected in the
paraboloid's derived normal, a `Vec3`{.Agda} whose three components are
elements of the observable ring. Each component is therefore a
polynomial in the two mirror coordinates — hence, through
`plot-of-line`{.Agda}, a plot of the line. We take the $z$-component
(`.snd .snd`), the aiming direction along the optical axis, as our
running section.

```agda
  aim-z : ⌞ R ⌟ → ⌞ O mirror ⌟
  aim-z Q = reflect incoming (normal Q) .snd .snd

  aiming-plot : ⌞ R ⌟ → ∣ 𝔸¹ .F₀ mirror ∣
  aiming-plot Q = plot-of-line (aim-z Q)
```

Round-tripping the aiming polynomial through its plot is definitional —
the `to`{.Agda} of `plots-𝔸¹`{.Agda} reads off the image of the single
generator, and the right-inverse law is `refl`{.Agda}. So the plot
`aiming-plot Q` genuinely carries the optics computation `aim-z Q`, with
nothing lost or added.

```agda
  aiming-plot-recovers : ∀ Q → Equiv.to (plots-𝔸¹ mirror) (aiming-plot Q) ≡ aim-z Q
  aiming-plot-recovers Q = refl
```

## The section is its own germ

Now the germ. Over the mirror probe we take the
[[discrete neighbourhood structure|neighbourhood-structure]]
`discrete-nbhd`{.Agda} — the only one the formal site supports — and
form the germ `G.Germs`{.Agda} of the line $\bA^1$ at `mirror`. The
germ of the aiming plot is its class under agreement on a neighbourhood;
with discrete neighbourhoods there is only the probe itself, so the
class is the plot.

```agda
  aiming-germ : ⌞ R ⌟ → G.Germs (G.discrete-nbhd mirror) 𝔸¹
  aiming-germ Q = inc (aiming-plot Q)
```

The identification `germs-discrete`{.Agda} sends a discrete germ back to
the plot it came from, and `germs-discrete-is-equiv`{.Agda} witnesses
that this is an equivalence: **over the formal site, germs are plots.**
Recovering the aiming plot from its germ is definitional.

```agda
  germ-is-plot : ⌞ R ⌟ → ∣ 𝔸¹ .F₀ mirror ∣
  germ-is-plot Q = G.germs-discrete 𝔸¹ (aiming-germ Q)

  germ-recovers-plot : ∀ Q → germ-is-plot Q ≡ aiming-plot Q
  germ-recovers-plot Q = refl

  germs-are-plots : is-equiv (G.germs-discrete {mirror} 𝔸¹)
  germs-are-plots = G.germs-discrete-is-equiv 𝔸¹
```

This is Schreiber's diagram (5) made concrete for the aiming field: the
germ is a set-quotient of plots, and here — trivial coverage, injective
thickenings — the quotient does nothing, so *the section is its own
germ*. That is precisely `ray_sheaf`'s "the section is built from
germs", with the caveat that over the formal site the building is by the
identity map.

## Aiming descends to germs (Schreiber's (6))

A map of aiming fields restricts to germs: this is `germs-map`{.Agda},
the paper's (6). To instantiate it we need a concrete morphism of smooth
sets `𝔸¹ => 𝔸¹`. We instantiate `germs-map`{.Agda} on the identity
morphism `idnt`{.Agda} of the line — the reference reparametrisation, on
which the germ functor's action is pinned down by `germs-map-id`{.Agda}.

```agda
  aim-germs-map
    : G.Germs (G.discrete-nbhd mirror) 𝔸¹
    → G.Germs (G.discrete-nbhd mirror) 𝔸¹
  aim-germs-map = G.germs-map (G.discrete-nbhd mirror) {X = 𝔸¹} {Y = 𝔸¹} idnt
```

The germ of the aiming field, pushed through this map of aiming fields,
is again a germ over the same probe — the restriction of a morphism of
smooth sets to germs, exactly diagram (6). For the identity morphism the
restriction is the identity on germs (`germs-map-id`{.Agda}), so the
aiming germ is carried to itself.

```agda
  aim-descends : ∀ Q → aim-germs-map (aiming-germ Q) ≡ aiming-germ Q
  aim-descends Q = G.germs-map-id (G.discrete-nbhd mirror) {X = 𝔸¹} (aiming-germ Q)
```

A *nontrivial* endomorphism of the line is also within reach: any probe
map `h : ThHom (𝔸 1 0) (𝔸 1 0)` gives one by the Yoneda embedding, since
`yo`{.Agda} produces a natural transformation of representables and
$\rm{Hom}_{-,U} \equiv \yo\,U$ holds definitionally. Its germ action is
the same `germs-map`{.Agda}, transporting the aiming germ along the
reparametrisation; we record the constructor without pinning its germ
value to the identity.

```agda
  line-endo : ThHom (𝔸 1 0) (𝔸 1 0) → (𝔸¹ => 𝔸¹)
  line-endo h = yo {C = ThCartSp} 𝔸¹ {U = 𝔸 1 0} h

  aim-germs-map' : ThHom (𝔸 1 0) (𝔸 1 0)
    → G.Germs (G.discrete-nbhd mirror) 𝔸¹
    → G.Germs (G.discrete-nbhd mirror) 𝔸¹
  aim-germs-map' h = G.germs-map (G.discrete-nbhd mirror) {X = 𝔸¹} {Y = 𝔸¹} (line-endo h)
```

## Connection to focusing

The aiming field the germs are built from is the *focusing* field of
`Physics.Heliostat.Optics`{.Agda}: under the focal relation $4qf = 1$,
`focusing`{.Agda} proves `reflect incoming (normal Q)`{.Agda} is a
$4q$-multiple of the ray toward the focus, and `focusing-parallel`{.Agda}
that it is parallel to it. So the germ of `aiming-plot Q` — the local
data of the aiming section — points, under the focal hypothesis, at the
focus: the stalks of `ray_sheaf` are germs of a field that aims every
mirror point at one target. We do not re-prove focusing here; it is a
theorem of the optics module, and the aiming section is its
$z$-component viewed as a plot.

```agda
  aim-z-is-focusing-z
    : ∀ Q F → Focal Q F
    → aim-z Q ≡ (four (con Q) ·s (focus F -v σ Q)) .snd .snd
  aim-z-is-focusing-z Q F focal = ap (λ v → v .snd .snd) (focusing Q F focal)
```

## The tangent derivative, honestly

The `Physics.Heliostat.Optics`{.Agda} partials `∂u`{.Agda}/`∂v`{.Agda}
are computed by the dual-number recipe: thicken one mirror coordinate by
an $\epsilon$ with $\epsilon^2 = 0$, evaluate, and read off the
$\epsilon$-coefficient. That is a *by-hand* construction over the
observable ring; it does not, by itself, exhibit the partial as the
derivative-slot of a genuine synthetic tangent vector. Here we close
that gap, using the [[Kock–Lawvere|formal-smooth-set]] theorem
`Kock-Lawvere`{.Agda} already proved for this topos.

`Kock-Lawvere`{.Agda} lives inside the anonymous
`module _ (n k : Nat)`, so specialising it to the mirror probe is a
positional application `Kock-Lawvere 2 0`; because `mirror`{.Agda} is
definitionally `𝔸 2 0`, no coercion is needed. Its statement is that
a map of the infinitesimal disk into the line over the mirror probe is
*exactly* a pair of plots — a **value** and a **derivative** — and
nothing more:

```agda
  KL-mirror
    : ∣ T 𝔸¹ .F₀ mirror ∣
    ≃ (∣ 𝔸¹ .F₀ mirror ∣ × ∣ 𝔸¹ .F₀ mirror ∣)
  KL-mirror = Kock-Lawvere 2 0
```

The two factors are each `∣ 𝔸¹ .F₀ mirror ∣ = ThHom mirror (𝔸 1 0)`, and
`plots-𝔸¹ mirror`{.Agda} identifies those with ring elements of
`O mirror`{.Agda} — the very observables `σz Q`{.Agda} and its by-hand
partial `∂u (σz Q)`{.Agda} live in. So we feed the *value* polynomial
`σz Q`{.Agda} and its *hand-computed* partial `∂u (σz Q)`{.Agda}, each
turned into a plot by `Equiv.from (plots-𝔸¹ mirror)`{.Agda}, into the
inverse of Kock–Lawvere: the result is a genuine element of `T 𝔸¹`{.Agda}
over the mirror — a synthetic tangent vector whose value is the section
and whose derivative-slot is the by-hand partial.

```agda
  ∂uσz-tangent : ⌞ R ⌟ → ∣ T 𝔸¹ .F₀ mirror ∣
  ∂uσz-tangent Q = Equiv.from KL-mirror
    ( Equiv.from (plots-𝔸¹ mirror) (σz Q)
    , Equiv.from (plots-𝔸¹ mirror) (∂u (σz Q)) )
```

Kock–Lawvere then certifies that reading the derivative-slot back off
this tangent recovers the partial we started with — transporting along
the counit `Equiv.ε`{.Agda} of the composite equivalence, the trailing
`plots-𝔸¹`{.Agda} round-trip fusing definitionally.

```agda
  ∂u-is-KL-derivative
    : ∀ Q
    → Equiv.to (plots-𝔸¹ mirror)
        (Equiv.to KL-mirror (∂uσz-tangent Q) .snd)
      ≡ ∂u (σz Q)
  ∂u-is-KL-derivative Q =
    ap (λ pr → Equiv.to (plots-𝔸¹ mirror) (pr .snd))
       (Equiv.ε KL-mirror _)
```

This upgrades the dual-number computation from a *recipe* to a *theorem*:
the partial `∂u (σz Q)`{.Agda} is not merely an $\epsilon$-coefficient
but the genuine tangent-derivative that `Kock-Lawvere`{.Agda} guarantees
is all the data of a disk-map, over the mirror probe. We prove this for
the $z$-component `σz`{.Agda} only; a chain rule, a Leibniz law at the
level of `T 𝔸¹`{.Agda}, and higher jets are not developed here.

## The aiming field, concretely — and where concreteness fails

Schreiber's (11)/(12) sit the **concrete** objects — the diffeological
spaces, determined by their honest *points* — strictly inside the smooth
sets. `is-concrete`{.Agda} (`Cat.Instances.Presheaf.Concrete`{.Agda}) is
the property that a plot is pinned down by its evaluation on the points
of the probe. It is tempting to declare the aiming line concrete; over
the *formal, thickened* site `ThCartSp`{.Agda} this is **false**, and
honesty requires we say so rather than assert it. The obstruction is the
infinitesimal probe `𝔻`{.Agda}: it has a single point yet carries
strictly more plots than points can see — a plot of the line by
`𝔻`{.Agda} is a *value and a derivative*, by the very `Kock-Lawvere`{.Agda}
theorem used just above, whereas its single point sees only the value.
This is exactly how the de Rham classifier of $1$-forms fails to be
concrete; the 1Lab ships that negative result as
`Ω¹-dR-not-concrete`{.Agda}, and we re-export it as the honest contrast:
the classifier of the aiming field's *differentials* is not
point-determined.

```agda
  aiming-nonconcrete-contrast
    : ¬ (CRing-on.1r (R .snd) ≡ CRing-on.0r (R .snd))
    → ¬ is-concrete Ω¹-dR
  aiming-nonconcrete-contrast = Ω¹-dR-not-concrete
```

What *is* honestly true of the aiming values is weaker and cheaper: they
are **representable, hence determined by the single polynomial that names
them**. `aiming-plot Q`{.Agda} is an element of the representable
`𝔸¹ = よ₀ ThCartSp (𝔸 1 0)`{.Agda}, and `plots-𝔸¹ mirror`{.Agda} shows a
plot of the line is *exactly* one ring element of `O mirror`{.Agda} — the
aiming polynomial itself, recovered definitionally.

```agda
  aiming-is-representable
    : ∀ Q → Equiv.to (plots-𝔸¹ mirror) (aiming-plot Q) ≡ aim-z Q
  aiming-is-representable = aiming-plot-recovers
```

We prove the **negative**, Schreiber-(12) statement — over the thickened
site the de Rham classifier `Ω¹-dR`{.Agda} is *not* concrete — and we
deliberately do **not** claim the aiming line `𝔸¹`{.Agda} is concrete: it
is not, over this formal site, for the same `𝔻`{.Agda}-plot reason, and
no representable-is-concrete lemma is shipped to lean on. What we assert
positively is only that the aiming values are representable and
point-determined by their naming polynomial — the genuine, weaker fact
the API supports.

## What is and is not proven

We have realised `ray_sheaf`'s germs as **germs of the heliostat's
aiming section over the reflector's actual probe site**
$\rm{ThCartSp}$, computed synthetically: the aiming polynomial is a plot
of the line by the mirror probe `𝔸 2 0` (whose function ring *is* the
optics observable ring, `Obs-is-mirror-functions`{.Agda}), its germ is
formed over the discrete neighbourhood structure, and the identification
germ = plot is `germs-discrete-is-equiv`{.Agda}. The restriction of a
morphism of aiming fields to germs — Schreiber's (6) — is
`germs-map`{.Agda}, instantiated on a concrete endomorphism of the line.

What we prove is the **trivial-coverage theorem**: over the formal site,
where thickening inclusions are injective and the coverage is
[[trivial|trivial-coverage]], germs along discrete neighbourhoods *are*
plots, so the aiming section **is** its own germ. What we do **not**
prove — and, honestly, cannot here — is the smooth-site version: germs
along genuinely *shrinking* open neighbourhoods over a good-open-cover
coverage, where germ-locality would be strictly weaker than globality
and the stalk would forget everything but an infinitesimal
neighbourhood. That is the analytic content of Schreiber's (7) that the
reading guide `Physics`{.Agda} lists as missing, and it waits on the
same real-numbers object — multiplication of Dedekind cuts and a
constructive theory of $C^\infty$ maps — that bounds every other module
in this development. Over the polynomial site the germ *is* the plot;
the shrinking germ is future work.
