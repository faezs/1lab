# Topos and Stacks of Deep Neural Networks — formalization roadmap

**Paper:** Belfiore & Bennequin, *Topos and Stacks of Deep Neural Networks*,
arXiv:2106.14587v3, 151 printed pages.
**Branch:** `topos-of-dnns`, built on top of the full physics stack
(cohesion, sites/sheafification/`Sheaves-topos`, Moore/Dold–Kan, simplicial
sets, `Forcing`). Local only — never push (same policy as the physics work).
**Namespace:** all new modules under `src/Neural/**`, literate `.lagda.md`,
zero postulates, following the `write-physics` conventions.

This document is the output of a full read of the paper (every numbered
statement and equation audited) against a full inventory of this fork,
with every claimed reuse adversarially verified against the actual source.
Line references to 1lab identifiers below were checked in this tree.

---

## 0. Verdict

**Yes — the fork has enough power to formalize the true semantic content of
this paper, and in several places the cubical formalization is *stronger*
than the paper.** The honest boundary:

- **~70% of the paper is formalizable mathematics** and maps with unusually
  high reuse onto existing modules: the DNN site and its topos (Ch. 1) onto
  `Cat.Site.*`/`Order.*`, stacks-as-fibrations (Ch. 2) onto `Cat.Displayed.*`,
  semantic information (Ch. 3) onto order theory + explicit cochain algebra,
  the braid tower (Ch. 4) onto `Algebra.Group.*` + HIT quotients, the
  2-category of networks (Ch. 5) onto `Cat.Bi.Instances.Displayed`, and
  Appendices A/C/D/E onto frames, group actions, and the upstream monoidal
  strength/monad stack (Appendix E's eqs. (60)–(61) are *literally*
  `left-φ`/`right-φ` in `Cat.Monoidal.Strength.Monad`).
- **The formalization must repair the paper, not transcribe it.** Verified
  defects to fix: the Grothendieck topology's stability axiom is never
  checked; Prop 1.1(i) is prose case analysis; Theorem 1.2 has no definition
  of "trees joined at minimal points"; Theorem 2.2's printed statement is
  garbled (relative vs absolute conditions conflated); Theorem 2.1's
  feed-forward half cites an *unpublished* companion text; Prop 3.4 has a
  broken step (repair: `T|P = ¬P` for every `T ≤ ¬P`); Prop C.2 is false as
  stated (only the localic shadow holds); the bisimplicial face count is off
  by one; (3.60) vs (3.86)–(3.87) have inconsistent signs; B₃ quotients are
  by `⟨⟨a²⟩⟩`/`⟨⟨a⁴⟩⟩`, not of `B₃/C`.
- **Classical scaffolding is replaced, deliberately, with no semantic loss:**
  Quillen model structures → lifting classes (`Cat.Morphism.Lifts`) +
  explicit fibrancy characterizations + the zigzag-HIT `Localisation`;
  homotopy colimits/double mapping cylinders → pushout/coequaliser HITs;
  derivators → pointwise Kan-extension records; Boolean arguments →
  explicit complementedness hypotheses; smooth manifolds/backprop calculus →
  the branch's synthetic differential geometry (where tangent objects become
  *theorems* — the paper only asserts them).
- **Genuine walls (delimited, not faked):** Mather/Whitney stability theory
  (Thm 4.1's negative half — replaced by its monodromy surrogate), period
  integrals of elliptic curves, Lambek–Scott completeness, π₁ of the
  discriminant complement (modeled definitionally, synthetic computation
  flagged as future work), the 3-categorical coherence of Ch. 5 (which the
  paper also never states), Appendix B (Zariski spectra — skipped whole).

---

## 1. Ground rules (normative for every `Neural.*` module)

1. **Universe policy.** Network sites and fibers at `lzero`. `Grpd_C`, `A_C`
   live at `lsuc lzero` and are never asked to be small. `PSh-omega`,
   `PSh-closed`, `Presheaf.Exponentials` are hard-pinned to
   `Precategory ℓ ℓ` — keep everything one-universe. `Open-coverage` lands
   at `Coverage _ (lsuc o)`: every Alexandrov/frame leg (Ch. 1 Prop 1.2,
   App. A, App. C) must use the level-general `Sheaves` record from
   `Cat.Site.Base`, **not** the `Sh[_,_]` one-universe aliases.
2. **Split/strict is normative.** Stacks are split strict-groupoid-valued
   presheaves (`Grpd` = full subcategory of `Strict-cats` on
   `is-pregroupoid`; `Grpd_C = Cat[C^op, Grpd]`). The HoTT "families of
   1-types" reading is a separate optional module, proven only for toy
   networks, labelled a *reading*, never an equivalence (no strictification
   theorem exists and none is cheap).
3. **No model-structure record, ever.** Fibrancy = explicit lifting/matching
   conditions; `Ho` = `Localisation` at the weak-equivalence wide
   subcategory; "ideal semantic flow" = unit-iso/reflective-subcategory data.
4. **Zero postulates; hypotheses as records — with inhabitants.** Every
   hypothesis record (`Gate`, `SemanticTransfer`, `InformationSpaces`,
   coherence (3.24), complementedness, …) ships a nontrivial instance in the
   same module. A machine-checked theory of type signatures is failure.
5. **The golden thread.** A 3-layer chain network with finite fibers must
   instantiate *every* new construction (site → topology → sheafification →
   Ω → stack → transfer → flow → semantic cochain) before the general
   version is attempted. It is the permanent regression test.
6. **Timeboxes.** Every difficulty-4 item gets a 2-week timebox with a
   pre-declared fallback written into the module header first (e.g.
   Alexandrov duality for finite posets only; Thm 2.2 for `F' = 1` only).
7. **Verification protocol** as in the skill: mikan with `-M6g`, exit-code
   checked, machine-wide lock, in-file `--lossy-unification` only, one
   heavy module at a time, commit per green milestone
   (`defn:`/`chore:` + Co-Authored-By).
8. **Memory discipline for term size.** Split equivalences into
   functors/unit/counit/triangle files; consumers import the equivalence
   record, never unfold it; no `Bi.Solver` on decorated 2-cells (hand-write
   the ~6 coherence squares); build thin-fiber (poset) variants first —
   the paper itself licenses "groupoids may be replaced by posets".

---

## 2. The spine (the ~20% that carries ~80% of the semantic value)

Phases are ordered; items within a phase can proceed in parallel. Names are
the planned modules. (d*n*) = difficulty 1–5.

### Phase 0 — conventions and shared infrastructure

| Module | Content | d |
|---|---|---|
| `Neural.Base` | Conventions: universe policy, arrow directions (site arrow deeper→shallower vs dynamics input→output), identifier table of known landmines (§5) | 1 |
| `Neural.Order.Adjunction` | Monotone (Galois) adjunctions between posets — missing upstream, used everywhere from Lemma 2.4 to §3.3 | 1 |
| `Neural.Order.FrameHeyting` | Frame ⇒ Heyting via `⋃ˢ` subset-joins (discharges the upstream TODO at `Order/Frame.lagda.md:132`; **first inhabitants of `is-heyting-algebra` in the library**, incl. `Props`, `ℙ A`); small `Order.Heyting.Reasoning` lemma layer (¬, ⊤⇨T=T, exponential law) | 2 |
| `Neural.Kan.Ran` | **Shared Ran-side dualization** (3–5 days): `precompose ⊣ Ran`, pointwise-Ran comma formula, via `Kan.Duality`'s `Co-lan→Ran`. The library is left-biased (verified: only `Lan⊣precompose`, `cocomplete→lan` exist); five entries in Ch. 2/5 silently need the other half. For the spine itself, fork-site `F_*` is a finite product built directly — do that first, general Ran later | 3 |

### Phase 1 — Chapter 1: the DNN site and its topos

| Module | Content | d |
|---|---|---|
| `Neural.Chain` | Golden thread: chain site over `Fin-poset`, presheaves `X^w`, `𝕎`, crossed `𝕏` (eq. 1.1), `pr₂` natural, fiber over `w : 1 → 𝕎` | 2 |
| `Neural.Chain.Omega` | Ω of a chain topos computed: `Sieves .F₀ k ≃ Fin (suc (suc k))` (thresholds `(∅,…,⋆,…)`) | 2 |
| `Neural.Graph.Fork` | **Design-critical.** Do *not* do surgery-then-classify: define the forked site as an inductive family of **typed vertices** (ordinary/tip/tine/tang `A⋆`/handle `A`) with Hom by recursion on types, so the arrow inventory holds definitionally; prove the surgery `Γ ↦ 𝚪` produces an instance afterwards. Validate on one-fork, two-fork, LSTM cell *before* Prop 1.1 | 3 |
| `Neural.Site.Topology` | The tine coverage as a real `Coverage` (the branch's **first nontrivial coverage**) via `from-families`; **one parametric stability lemma** ("all-incoming-arrows coverage at a designated vertex class is stable in the free category on a DAG whose designated vertices admit no other incoming paths"), instantiated later for RNN/LSTM/GRU; counter-lemma: an empty cover at handles forces sheaves terminal there (the p. 18 remark) | 3 |
| `Neural.Sheaf.Explicit` | One-step sheafification `X ↦ X⋆` (product at `A⋆`), `is-sheaf` directly, universal property; agreement with the HIT `Sheafify` via `unit-kernel` — first concrete workout of the branch sheafification stack on a nontrivial coverage | 3 |
| `Neural.Network.Activities`, `Neural.Network.Weights` | `X^w` on the forked site; unique-section theorem (`is-contr` of the section fiber given inputs — this *is* what a network computes); the weight sheaf `𝕎` over downstream subgraphs `Γ_x`; crossed product `𝕏` | 3 |
| `Neural.Poset.Reduced`, `Neural.Topos.Equivalence` | **Prop 1.1**: `C_𝐗` is a poset (hardest honest proof of Ch. 1 — by induction on the typed inventory, not prose case-bash); restriction; unique sheaf extension; **Corollary: `Sh(C,J) ≃ PSh(C_𝐗)`** built directly as restriction ⊣ explicit-extension (no comparison-lemma machinery needed) | 4 |
| `Neural.Poset.Alexandrov` | **Prop 1.2 as general Alexandrov duality**: `PSh(P) ≃ Sh(Lower-sets P, Open-coverage)` for an *arbitrary* poset — a reusable library theorem. Note: weaken the existing `Order.Frame.Free.Lower-sets-frame`'s hypothesis rather than adding a name-colliding new one | 4 |
| `Neural.Poset.TreeStructure` | **Thm 1.2 reformulated precisely**: min/max classification (outputs⊎tips / inputs⊎tangs), unique covering chains away from tips, trees share only minimal points ("rooted tree" defined honestly) | 3 |
| `Neural.Semantics.InputOutput` | `H⁰ = lim` over the finite poset; feed-forward ⇒ the input–output relation is a function's graph; spontaneous-activity sheaf (`Neural.Sheaf.Spontaneous`) witnessing strictness | 2 |

Backpropagation (§1.4), reformulated synthetically, is **off the spine** but
planned: `Neural.Backprop.Paths` (path sets by well-founded induction),
`Neural.Backprop.Cooperative` (path-tree recursion; derive binary ⊕ +
assoc/comm as corollaries), `Neural.Backprop.ChainRule` (Lemma 1.1 via
SDG/dual numbers — tangent objects become theorems), and **one merged**
`Neural.Backprop.Flow` (discrete ℕ-indexed gradient flow; Theorem 1.1's real
content = componentwise updates commute with forgetting projections;
continuous flow as a delimited module hypothesis; minibatch naturality
verbatim). The completeness critic's dependency cycle between the old two
flow entries is resolved by this merge.

### Phase 2 — logic infrastructure (the schedule-critical block)

**Re-budget: 4–6 weeks.** This is the single load-bearing prerequisite for
every logic statement in Ch. 2–3, and the feasibility review found the
original week-scale estimate fictional.

| Module | Content | d |
|---|---|---|
| `Neural.Topos.Predicates` | **Representation decision:** work with Ω-valued predicates `Hom(X, Ω)` (sieve-valued maps), *not* the subobject poset — `Physics.SmoothWorld.Forcing` already has machine-checked Heyting ⇒ᵢ and both quantifier adjunctions `∃[_] ⊣ pullback ⊣ ∀[_]` on sieves; transfer pointwise. Prove `Sub(X) ≅ Hom(X,Ω)` once; translate only where subobjects are forced. Beck–Chevalley only for the product-projection and base-morphism cases the paper uses | 4 |
| `Neural.Logic.Hyperdoctrine` | First-order Heyting hyperdoctrine record (extends `Regular-hyperdoctrine` with fibrewise Heyting + ∀ with BC); extend `Doctrine.Logic`'s grammar with `∀/`⇒/`∨/`⊥; soundness into `Neural.Topos.Predicates`. (Lambek–Scott completeness: **skipped, delimited**) | 4 |

### Phase 3 — Chapter 2: stacks and the logic of fibers

| Module | Content | d |
|---|---|---|
| `Neural.Stack.Grothendieck` | **Pseudofunctor→fibration for split functors** `F : C^op → Strict-cats` (missing upstream — only the inverse `Fibres` exists): displayed category per eq. 2.2, `∫`/`πᶠ`, cleaving, `Right-fibration` when fibers are pregroupoids. Fix the `λ_α/λ'_α/τ'_α` naming here once | 3 |
| `Neural.Stack.Presheaves` | **Core infrastructure:** `PSh(∫F) ≃` compatible families (eqs. 2.4–2.6); split into functors/unit/counit/triangle files (OOM discipline); fibered Yoneda (2.7–2.8) | 4 |
| `Neural.Stack.Fibration` | Adjoint triple `F_! ⊣ F_α^* ⊣ F_*`: `F_!` by upstream Lan; `F_*` **directly as finite products over the fork site** (honest, computes; general Ran from Phase 0's `Neural.Kan.Ran` later); eq. 2.19 by construction | 3 |
| `Neural.Stack.Omega` | Glued classifier `Ω_F` on sieve families; **Prop 2.1 by transport** of `PSh-omega` across the families equivalence (the paper's implicit computation made explicit) | 3 |
| `Neural.Stack.Open` | "Open" *defined* by the adjoint characterization at trivial topology (MLM cited machinery re-proven natively at the sieve level); transport dictionary (2.13–2.16); Lemma 2.3 (fibration ⇒ open — conditions (i)–(ii) vacuous at trivial topology); Prop 2.2 | 4 |
| `Neural.Stack.Adjunction` | Lemma 2.4: `Ω_α ⊣ τ'_α`, section property (2.24–2.29) — elementary, fully precise in the paper | 2 |
| `Neural.Stack.Boolean` | Lemma 2.1 under an **explicit complementedness hypothesis** (irreducibly classical otherwise; groupoid presheaves are *not* constructively Boolean — honest side lemma with decidability) | 3 |
| `Neural.Stack.ContractedProduct` | **THE research risk (see §4).** Lemma 2.2: `G ×_{G'} X'` as set-quotient HIT, Heyting-bijective `f^*`; then the *unproven* groupoid extension | 5 |
| `Neural.Stack.Semantics` | **Theorem 2.1** assembled; Definition 2.1 (standard/strong hypothesis records); `Neural.Stack.BaseChange` for `λ_π ⊣ τ'_π` (2.31–2.32) as integration test | 4 |
| `Neural.Model.Toy` | Lemmas 2.5–2.7 (Shadok segment, confluence, divergence) — mere lifts, complemented monos delimited; **excellent first targets for §2.4** | 2 |
| `Neural.Model.Isofibration`, `Neural.Model.Injective`, `Neural.Model.Fibrant` | Classes only (isofibration, injective-on-objects); Prop 2.3 via `clo ⊣ ev` transposition; **corrected relative Theorem 2.2** (matching maps, induction deleting an initial star, unique paths ⇒ matching objects are products — with an explicit bridge lemma from Thm 1.2, per the completeness audit); Corollary-as-definition of **fibrant network stack**, incl. the paper's unproved bridge: fibrant ⇔ every `F_α` satisfies Thm 2.1's hypothesis. **Do `M ∈ {Set, Grpd, Cat}`** — the Cat instance is required by Thm 2.3 (completeness-critic major finding) | 4 |
| `Neural.Model.IdealFlow` | **New entry (completeness gap):** `is-ideal-flow F := π^*π_* ≅ Id` (Def 2.1 strong tier); fibrant ⇒ ideal-flow by composing Corollary-(b) with Thm 2.1/Eq 2.30; converse *not* claimed. This is the anchor Ch. 5's Ho-layer consumes | 2 |
| `Neural.Model.TypeTheory`, `Neural.Model.GeometricFibration` | MLTT dictionary (ambient in cubical — contexts/types/terms/Σ/Π as semantic glossary, no initiality); identity types = path spaces comparison lemma; Lemma 2.8; Thm 2.3's real content: Σ_f via `fibration-∘`, **Π_f along Grothendieck fibrations built fresh** (the hard part), preservation of matching conditions (asserted, never written in the paper) | 4 |

### Phase 4 — Chapter 3: semantic information (against an interface)

Keystone: **one `SemanticTransfer` record** (Heyting-algebra fibers, monotone
adjunction `π^★ ⊣ π_★`, three-strength hierarchy, and the paper's *hidden*
hypotheses as explicit fields: `π^★` preserves ¬ and ⇒). Everything in
§3.3–3.5 is developed against it, independent of the DNN site. Instances
shipped in the same module: G-sets along a concrete surjective group hom,
and a fork projection on the toy network.

| Cluster | Modules | Content | d |
|---|---|---|---|
| Manifolds | `Neural.Network.Conditioning`, `Neural.Semantics.CatsManifold` | `C₊`, conditioned `X₊`; cat's manifold = `lim X₊` (eq. 3.1 is *verbatim* `Limit = Ran !F`, `Cat.Diagram.Limit.Base:178`) | 2–3 |
| Transfer layer | `Neural.Semantics.Transfer`, `.Localized`, `.Theories`, `.Modules`, `.PropositionFibration` | Lemmas 3.1–3.3 (2–6-line proofs given the interface), Props 3.1–3.3, Thm 3.1; `Ã`/`Ã′` as **thin displayed categories** with (co)cartesian lifts = `π^★`/`π_★` (the [Rap10] model-category framing dropped losslessly); `Ã′_strict` via `Wide-subcat`; conditioning `T|Q = Q ⇨ T` | 1–3 |
| Bar complex | `Neural.Information.Bar`, `.Acyclicity`, `.Ambiguity`, `.Mutual`, `.Concavity`, `.KL` | Cochains with explicit coboundary (3.28), δδ=0; **Props 3.4–3.6 with explicit contracting homotopies** (Prop 3.4's broken step repaired); ambiguity/precision; mutual information `I_λ = δ^t φ` (sign bug documented, (3.60) normative); concavity over any Heyting poset; semantic KL + distance (prove the asserted positivity⟺concavity equivalence). Ordered values: use ℚ | 2–3 |
| CBH | `Neural.Information.CarnapBarHillel` | Finite Boolean instance, integer content, inclusion–exclusion concavity; **finite-topology non-concavity counterexample** (typo fixed); independency = additivity | 3 |
| Cohomology | `Neural.Categorical.Cohomology` | Small-category cohomology `H^*(D,Φ)` via the explicit cosimplicial complex — generic in `(D, Φ)`, replaces SGA4 resolutions; do *not* route through the lzero-pinned sSet stack | 3 |
| Histories | `Neural.Homotopy.TheorySpace`, `.Histories`, `.BiSimplicial`, `.LocalSystem`, `.Dynamical` | Simplicial `Θ^•_λ` (degeneracies reconstructed — paper omits them); quotient + homotopy quotient as coequaliser/pushout HITs (Bousfield–Kan unnecessary); bisimplicial `Θ^•_*` with **corrected face count**; `gI`, `gX`, and `gS` as a *conditional* existence theorem under coherence (3.24) | 2–4 |
| Info spaces | `Neural.Information.Spaces`(+`.Boolean`) | `InformationSpaces` interface (difference operation axiomatized — never constructed in the paper) + **one consistency instance** (decidable subsets); Lemma 3.6, Props 3.7–3.8 (hidden cofibration hypothesis surfaced); `I₂` as an *actual pullback* in the type-valued instance (the cubical jewel); independence = initial intersection; Ansätze 1–4 **skipped** (deferred to an unavailable preprint) | 2–3 |
| Example | `Neural.Example.LTwoThree` | `G = S₃ × D₄` acting on `Fin 64`; orbits/stabilizers by decidable enumeration; self-duality; "Galois-like but not Galois" non-existence | 3 |

### Phase 5 — Chapter 4: memory cells and the braid tower

Decoupled from the spine — **best candidate for parallel work**.

| Module | Content | d |
|---|---|---|
| `Neural.Site.RNN`, `.LSTM`, `.GRU` | Concrete finite sites via the Phase-1 parametric stability lemma; `Coverings.stable` obligations acknowledged | 2 |
| `Neural.Dynamics.Hadamard`, `.Memory` | States as `Fin m → ℝ` (`Data.Real.Ring`); multiplicity invariant as a well-typedness theorem (*improves* on the paper); `Gate` record for σ/tanh (no `exp` in constructive ℝ — hypotheses-as-fields, incl. the paper's own open diffeomorphism hypothesis); linear-regime ring identities | 2–3 |
| `Neural.Graph.CycleRank` | Cycle rank by `refl`: 3 (LSTM), 5 (GRU); non-planarity skipped (no embedding theory, nothing uses it) | 2 |
| `Neural.Memory.NormalForm`, `Neural.Unfolding.Cell` | Viète elimination over any CRing with ½,⅓; normal-form identities; parameter counts by `refl` | 2 |
| `Neural.Cubic.Discriminant` | `-(4u³+27v²) = ∏(zᵢ-zⱼ)²` over any CRing (the semantic content of the cusp); `3^m` bound; constructive root *existence* delimited | 3 |
| `Neural.Homotopy.FundamentalGroupoid` | **Extend** `Cat.Instances.Discrete.Pre.Π₁` (exists upstream! do not rebuild): `is-pregroupoid Π₁`, `Aut(x) ≅ π₁` | 2 |
| `Neural.Braid.B3` | B₃ = pushout `ℤ ←(·2)– ℤ –(·3)→ ℤ` (`Groups-finitely-cocomplete`, verified `Free/Product.lagda.md:180`); braid relation, center `c = x²` central in two lines; σ-presentation equivalence **only if** a small normal-closure/presented-group helper is added (verifier: the mutually-inverse-homs plan needs a codomain group to exist) | 3 |
| `Neural.Braid.Groupoids`, `.Quotients`, `.SL2`, `.Monodromy` | Trivialized `𝓑₃`-groupoid models (Π(Λ*_ℂ) ≃ model delimited as research); `B3(ℝ)` via `Restrict`; Culioli groupoid `B3^r` with 4-object skeleton (rational subtype); generic **groupoid quotient by conjugation-stable subgroups** (upstreamable); tower `B₃ ↠ S₃` (afternoon), `SL₂(ℤ)` instance, `B₃/⟨c⟩ ≅ PSL₂(ℤ)` timeboxed to "hom + kernel-contains" fallback; S₃ monodromy on roots; elliptic periods **skipped** | 2–4 |
| `Neural.Unfolding.Stability` | **Thm 4.1 reformulated:** positive half = algebraic conjugacy to `z³+uz+v` under the Gate hypothesis + per-neuron 1-vs-3 dichotomy; negative half = monodromy obstruction to continuous root sections (Mather theory named as the skipped citation) | 4 |
| `Neural.Catastrophe.Thom`, `Neural.Stack.Braided` | Thom's list as named polynomials (Dₙ delimited unless built via `Semidirect`); braided stacks via `Chaotic` constant-fibre bifibration + `Right-fibration` — an honest *prestack* (no descent condition exists in the repo; said plainly) | 2–3 |

### Phase 6 — Chapter 5: the 2-category of networks and derivators

| Module | Content | d |
|---|---|---|
| `Neural.Network.Attention`, `.LSTM`, `.Relation` | Attention/LSTM/relation operators over an abstract ordered ring with abstracted softmax; the one provable lemma: **Sₙ-invariance** (needs a new `∑-permute` for `Algebra.Group.NAry` — a day) | 1–2 |
| `Neural.Semantics.Pair` | **The chapter's prize:** objects `(E, Right-fibration, A : PSh(∫E))`, 1-cells = fibred `Vertical-functor` + `φ : A ⇒ A' ∘ (∫ᶠF)^op` — the strictness of (5.8) makes this *easier* cubically; thin-fiber variant first | 3 |
| `Neural.Semantics.TwoCategory` | 2-cells `(λ : F =>↓ G, a)` with (5.11); **2-category axioms the paper only asserts** — `Disp[]` (verified: `Cat/Bi/Instances/Displayed.lagda.md:135`) supplies the stack component; genuinely a 2-category, not (2,1) | 4 |
| `Neural.Semantics.BaseChange` | Giraud triple: `u^*` = `Change-of-base` (exists); discrete case = `Lan⊣precompose` + Phase-0 Ran; groupoid case as ordinary adjunctions between vertical-functor categories; full 2-adjunction delimited | 4 |
| `Neural.Derivator.Base`, `.Presheaf` | Derivator record = "adjoints to restriction, pointwise" (fix the paper's variance sloppiness; state (d) on both sides); worked instance `I ↦ PSh(I)` — u_! by import, **u_* is new mechanical work** (left-bias correction); `H^*(C;F) := (p_C)_* F` | 3 |
| `Neural.Homotopy.SemanticFlow` | `Ho(M_C) := Localisation` at W (verbatim the paper's "formally inverting zigzags"); ideal flows = reflective-subcategory statement via `Neural.Model.IdealFlow` | 3 |
| *Deferred* | 3-category `Neural.Semantics.Global` (no 2-/3-cells defined in the paper), `Neural.Site.Morphisms` (AGV/Shulman — entire morphism-of-sites layer absent; build only the easy direction if base change demands it), derived-category derivator axioms, `Neural.Derivator.Abelian` beyond the definition (needs `H_n` for chain complexes — itself a useful week) | 5 |

### Phase 7 — Appendices A/C/D/E (the crisp gems)

| Module | Content | d |
|---|---|---|
| `Neural.Fuzzy.*` (A) | `Set_Ω` over a frame; **Bell's equivalence `Set_Ω ≃ Sh(Ω,K)`** — the cubical proof is *better* (implicit choices become centres of contraction via `is-sheaf₁`); spatial/Alexandrov lattice core; stop after Prop A.1 unless the Ch. 1 localic story wants the showcase | 3–4 |
| `Neural.Groupoid.*` (C) | Prop C.1 (essentially upstream: `π₁F-is-equivalence`/`Concrete≃Abstract`); `PSh(⊎) ≃ ∏PSh` (absent upstream, straightforward); orbit algebra `Sub(X) ≅ ℙ(X/G)` Boolean-as-complemented; **Prop C.2 corrected**: `Sh(ℙK, Open-coverage) ≃ (K → Set)` — only the localic shadow, with the crisp non-equivalence remark | 2–3 |
| `Neural.Information.ChainSite`, `.Precision` (D) | `Ω^E` = Heyting algebra of nested finite subsets (built directly, sidestepping the missing `Sub(X)` Heyting structure); Lemma D.1 = the ƛ/ev verification; **Prop D.1 concavity over ℚ** (δ_k = 2^{-k}); tree extension recorded as the paper's own conjecture / stretch goal | 2–3 |
| `Neural.Semantics.Closed`, `Neural.Linear.*` (E) | `Monoidal-closed` record (surprising upstream gap); theories as Ω-valued right-closed classes (**renamed** `Neural.Linear.Theories` to avoid the Ch. 3 collision; Heyting posets are thin instances); linear exponential `!` à la Melliès (all ingredient records exist upstream: `Comonad-on`, `Comonoid-on`, `Lax-monoidal`), Seely isos, co-Kleisli CCC (home of `Cartesian-closed`: `Cat.Diagram.Exponential:158`, **not** the phantom `Cat.CartesianClosed.Base`); tensorial negation/dialogue categories; Lemma E.1 strengths into upstream `Monad-strength`; eqs. (60)–(61) = `left-φ`/`right-φ`, commutative⇒monoidal = `monoidal≃commutative` (`Cat.Monoidal.Monad`); Prop E.3 (cleanest target, the source of examples); **Hasegawa E.2 = the one research-risk item here** (multi-day diagram chase, cited without proof); `𝒜^η ≃ (𝒜^η)^op` ("classical negation without a false object"); ¬¬-as-nucleus replaces the Lawvere–Tierney remark (no LT machinery exists) | 2–4 |

---

## 3. Risk register (from adversarial review)

1. **[blocker] Lemma 2.2's groupoid extension** (Theorem 2.1's feed-forward
   half) exists only in an unpublished companion text. De-risk in tiers:
   (1) group case fully (specified in the paper); (2) reduce groupoids
   *presented as indexed sums of connected components* to the group case via
   Prop C.1 (Phase 7 module — pull it forward); (3) fallback: state Thm
   2.1(b) conditionally on the Def 2.1 record + certify non-vacuity on a toy.
   **Budget a month; schedule early** — failure re-scopes Ch. 2–3.
2. **[blocker] The logic infrastructure is a quarter, not a week.** Mitigated
   by the `Hom(X,Ω)` representation (Phase 2) riding on `Forcing`'s
   already-machine-checked quantifier adjunctions.
3. **[blocker] Aggregate proof mass.** ~60 modules; cubical d4 items run
   3–6× estimates. Mitigations: the spine, timeboxes with pre-declared
   fallbacks, golden-thread regression, thin-fiber-first policy.
4. **[major] Strict vs univalent groupoid schism** — resolved by fiat
   (ground rule 2): split/strict is normative, HoTT reading optional.
5. **[major] Ran-side Kan extensions missing** — one shared Phase-0 work
   item; fork-site `F_*` as finite products for the spine.
6. **[major] Fork inventory is a single point of failure** — resolved by
   the typed-vertices design (Phase 1) and the parametric stability lemma.
7. **[major] Interface vacuity** — ground rule 4 (inhabitants mandatory)
   and the golden thread.
8. **[major] OOM/term size** — ground rule 8; treat OOM as a design smell.

## 4. Known landmines (verified; fold into `Neural.Base` prose)

- `Open-coverage : Coverage _ (lsuc o)` → use level-general `Sheaves`, never
  `Sh[_,_]`, on Alexandrov/frame legs.
- `Lower-sets-frame` already exists (`Order.Frame.Free:70`) — weaken its
  `Meet-semilattice` hypothesis; do not mint a colliding name.
- `prop→is-subterminal-PSh` (not `prop→subterminal-PSh`),
  `Cat.Instances.Presheaf.Limits:68`; `clo⊣ev` is the **left** adjoint only.
- `Cartesian-closed` lives in `Cat.Diagram.Exponential:158`;
  `Cat.CartesianClosed.Base` does not exist.
- `Π₁` (fundamental pregroupoid) already exists: `Cat.Instances.Discrete.Pre`.
  Set truncation is `Data.Set.Truncation` (not `1Lab.HIT.Truncation`).
- `is-heyting-algebra` requires joins + bottom (a full lattice) — more than
  the paper's closed monoidal poset; every intended instance has them.
- `⋃ˢ` (`Order.Diagram.Lub.Subset`) is `opaque` — route Frame⇒Heyting
  through `⋃ˢ-inj`/`⋃ˢ-universal` or `opaque unfolding`.
- The sSet/nerve/Dold–Kan stack is pinned to `lzero` with `is-set` objects —
  Ch. 3's categorical cohomology must use chains-of-arrows, not sSet.
- `Cartesian-fibration` is a *cleaving* (chosen lifts); `Fibres` needs one
  fixed universe pair for all fibers.
- `precompose` lives in `Cat.Functor.Compose`. `Representables-generate-presheaf`
  (Coyoneda:186). Vertical composition `_∘nt↓_`, whiskering `_◆↓_`.
- No: model structures, stacks/descent, LT topologies, morphisms of sites,
  classifying topoi for theories, Boolean-algebra record, braid groups,
  `exp` on ℝ, homology `H_n` of chain complexes, orbit–stabilizer machinery,
  `∑-permute`. (All verified by grep; several are planned contributions.)

## 5. Explicit skips (essay / proof-by-citation — delimited in prose, never faked)

Ch. 1: KL/Bethe remark; "no known exception" claim. Ch. 2: Lurie A.2.8
scaffolding; Lambek–Scott completeness; §2.5 (title ends in "?"). Ch. 3:
pp. 48–50 program (vanishing cycles, Ext¹-entropy); interpretation passages;
Ansätze 1–4. Ch. 4: Whitney/Mather germ theory; elliptic period integrals;
§4.5 pre-semantics essay (Culioli arrows recorded as named examples).
Ch. 5: 3-categorical coherence; "composition of derivators"; B₅ claim;
Θ_P/M_P program. Appendices: B entirely (Hochster/Lewis by citation; its one
DNN-relevant fact — finite poset recovered from its open lattice — survives
in `Neural.Fuzzy.Spatial`); D's tree extension (the paper's own conjecture;
our best stretch goal); E's bar-complex information program.

## 6. Sequencing summary

```
Phase 0 (conventions, FrameHeyting, Ran dual)        ~1–2 weeks
Phase 1 (Ch.1 spine incl. golden thread)             ~4–6 weeks
Phase 2 (logic infrastructure)                       ~4–6 weeks
  + EARLY: Lemma 2.2 group case + groupoid reduction (de-risk, ~4 weeks,
    can overlap Phase 1)
Phase 3 (Ch.2 stacks → Thm 2.1, fibrant stacks)      ~6–8 weeks
Phase 4 (Ch.3 information layer, interface-first)    ~6–8 weeks
Phase 5 (Ch.4 braid tower — parallelizable)          ~3–4 weeks
Phase 6 (Ch.5 2-category + derivator instance)       ~4–6 weeks
Phase 7 (Appendix gems — interleave as palate cleansers)
```

Realistically a 6–12 month program for the full spine with one typechecker;
the golden thread + Phase 1 + Phase 2 + Theorem 2.1 constitute a coherent,
publishable first milestone. Every phase ends with `src/Neural.lagda.md`
(the reading guide, `Physics.lagda.md`-style) updated with typechecked
`_ = theorem` link blocks and an honest missing-list.
