---
name: write-physics
description: Write machine-checked physics in this 1lab fork — compiled dynamical systems that run by refl, synthetic derivatives and conservation laws via nilpotent infinitesimals, differential forms and gauge invariance, fermionic algebra, and gauged symmetries — using the formalized topos-physics stack on the `physics` branch. Use whenever asked to formalize, simulate, or prove something physical here.
---

# Writing physics in the 1Lab

This repo (branch `physics`) contains a zero-postulate, computing
formalization of the topos-theoretic physics stack. Physics written
here is not modelled — it *is* the computation: orbits close by
`refl`, conservation laws are ring identities, and every claim
typechecks. Your job when writing new physics: pick the right recipe
below, imitate the exemplar module exactly, verify with the
protocol, and commit per green milestone.

Read the exemplars before writing anything:
- `src/Physics/Oscillator.lagda.md` — the master exemplar: one system
  through every layer (compiled dynamics, synthetic force,
  infinitesimal Hamiltonian mechanics, fermions, gauging).
- `src/Physics/Newton.lagda.md` — second-order mechanics (jets, F = ma).
- `src/Physics/Maxwell.lagda.md` — gauge fields (forms, field strength,
  gauge invariance).
- `src/Physics.lagda.md` — the reading guide: what exists, what's
  missing (its final section is the authoritative gap list — never
  claim something it lists as missing).
- `src/Physics/Paper.lagda.md` — the claims discipline: every
  assertion is a typechecked `_ = theorem` link block.

## Verification protocol (non-negotiable)

- Typecheck: `/nix/store/8gim2p64g2hgw3ngwvav283kg68cc95d-Mikan-2.9.0/bin/mikan +RTS -M6g -RTS <file>`
- ALWAYS check the exit code (`; echo "exit=$?"`). Exit 251 = heap
  exhaustion = FAILURE; grepping for "error" misses it.
- ONE mikan process machine-wide. If other agents may be running:
  `until mkdir /tmp/mikan-lock 2>/dev/null; do sleep 5; done` before,
  `rmdir /tmp/mikan-lock` after (success or failure). Never hold the
  lock while editing.
- NEVER pass `--lossy-unification` on the command line (it
  invalidates the whole library's interface cache → OOM rebuild).
  In-file `{-# OPTIONS --lossy-unification #-}` pragma is fine for
  heavy modules.
- Zero postulates. If a statement resists proof, weaken or delimit
  it honestly in prose; never assert.
- Commit per green milestone:
  `git commit -m "defn: <lowercase description>" -m "Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"`.
  Never push unless the user asks; the safe remote branch is
  `physics` on `git@github.com:faezs/1lab.git` — NEVER push to the
  branch name `schreiber-htt-physics` (frozen head of a closed
  upstream PR) and never to `the1lab/1lab`.

## Recipe 1 — a compiled dynamical system (runs by refl)

Pattern: `Physics/Oscillator.lagda.md` §"Dynamics, compiled and conserved".
1. Base types as a data type with decidable structure; operations as
   an indexed `data Op : types.Ty B → B → Type` — keep at most one
   constructor per index so `Op` is a proposition (mirror
   `Osc-op-is-prop`).
2. Package as `λ-Signature lzero`; then MID-FILE
   `open import Cat.CartesianClosed.Free <Sig>` and `...Free.Lambda <Sig>`.
3. The dynamics is an `Expr` λ-term (constructors `` `hom ``,
   `` `⟨_,_⟩ ``, `` `π₁ ``, `` `π₂ ``, `` `var ``, `stop`).
4. Interpret in Sets: `module M = Cat.CartesianClosed.Free.Model <Sig>
   (Sets-cartesian {ℓ = lzero}) Sets-closed`, an
   `elim.base-method M.chaotic-cartesian M.chaotic-closed (λ _ → el! Int)`
   clause per operation, `module Run = M.model … `, and
   `step s = Run.compile .F₁ ⟦ prog ⟧ᵉ (lift tt , s)`.
5. Deliverables: concrete refl-checks (`_ : step (3 , 4) ≡ (4 , -3) ; _ = refl`),
   then UNIVERSAL theorems (periodicity, conservation) proven with
   `Data.Int` lemmas (`negℤ-negℤ`, `*ℤ-negl`, `+ℤ-commutative`; there
   is no `*ℤ-negr` — commute first). Frame invariance results as
   (discrete) Noether statements.

## Recipe 2 — synthetic derivatives and forces

Pattern: `force-from-potential` in Oscillator. Over any `(R : CRing ℓ)`:
observables live in `R[ Lift ℓ (Fin 1) ]` (open `Algebra.Ring.Polynomial R`),
generator `x̂ = var (lift fzero)`. The derivative is evaluation at the
thickened point: `taylor = extend (Dual.ι-dual R[x] CR.∘ con-hom)
(λ _ → x̂ , con 1r)` (import `Algebra.Ring.DualNumbers as Dual`);
`δ p = taylor .∫Hom.fst p .snd`. Dual multiplication is
`(a,b)(c,d) = (ac, ad + bc)` — the Leibniz rule lives in the
ε-component, so `δ (x̂ *ₚ x̂) ≡ x̂ +ₚ x̂` is a two-liner
(`ap₂ _+ₚ_ Rx.*-idr (*ₚ-idl x̂)`). For invariant statements use
Kähler forms: `Ω¹ R[x] con-hom`, `d-leibniz`, `·ω-distr`. Two
variables (partial derivatives): `R[ Lift ℓ (Fin 2) ]` with per-variable
thickening maps (`hamiltonian-mechanics` shows `∂x`/`∂p`); exact
conservation `{H,H} = 0` is ring algebra with `ε² = 0`.

## Recipe 3 — second-order mechanics (jets, F = ma)

Pattern: `Physics/Newton.lagda.md` + `Algebra.Ring.Weil`. W₂ = R[δ]/δ³
has carrier `⌞R⌟ × ⌞R⌟ × ⌞R⌟`, product `(a,b,c)(a',b',c') =
(aa', ab'+ba', ac'+bb'+ca')`, jet derivative `D (a,b,c) = (b, c+c, 0)`
(divided-power-free: the derivative of a 2-jet is a 1-jet — the
FULL-triple Leibniz rule is FALSE; only `D-leibniz₀/₁` hold).
`taylor₂` evaluates at `x̂ + δ`: value, force, curvature in one pass.
State second-order laws as jet-level equations on components
(`is-jet-flow` with the truncated Hamilton equations); Newton is
`velocity₁ ∙ force₀ : c + c ≡ − x₀`. Over rings without ½, take
halving witnesses as hypotheses — never divide.

## Recipe 4 — gauge fields and forms

Pattern: `Physics/Maxwell.lagda.md` + `Algebra.Ring.Kahler.Exterior`.
2-forms `Ω²` with `_d∧d_`, wedge `wedge : ⌞A⌟ → Ω¹ → Ω²`, exterior
derivative `d¹` (built as a paramorphism), `d¹-d : d¹ (dₖ a) ≡ 0²`,
and the gauge lemma `gauge : d¹ (ω +ω dₖ χ) ≡ d¹ ω`. A gauge theory
here = a potential (1-form over `R[ Lift ℓ (Fin n) ]`), its field
strength `F = d¹ A`, a computed value (`F-value`), and the gauge
equivalence theorem via `gauge`. Ω^≥3/Bianchi-in-degree-2 do not
exist yet — say so if needed, don't fake it.

## Recipe 5 — fermions and gauged symmetries

Fermions: open `Algebra.Ring.Grassmann R q`. Pauli exclusion is the
constructor `θ-sq`; parity `σ-parity` is `(−1)^F` (fixes `con`,
negates `θ`, involution `σ-σ`). New CAR-style theorems: shuffle
constants with `con-comm`, reassociate with `*g-assoc`, kill squares
with `θ-sq`, cancel cross terms with `θ-anticomm` + `+g-invr` (the
`modes-nilpotent` proof is the template; note `_+g_`/`_*g_` share a
fixity level — parenthesize fully).

Gauging: build the symmetry group with `make-group`/`to-group` (there
is no Bool-xor group upstream — inline it), the action as
`Action (Sets lzero) G X` with iso equality via
`module Sl = Cat.Reasoning (Sets lzero)` and `Sl.≅-path`, then
instantiate `Cat.Instances.SimplicialSets.ActionGroupoid G X act`:
`homotopy-quotient`, `quotient-vertices/edges`. The physics payoff to
state: distinct stabilizer loops at symmetric configurations
(`gauge-loops-differ` pattern) — the groupoid remembers what the
quotient set forgets.

## Deeper infrastructure (when the physics needs it)

Sites & topoi: any pointed probe site gets cohesion
(`Cat.Instances.Presheaf.Cohesive`, needs `Precategory ℓ ℓ`);
`Cat.Instances.FormalSmoothSets` has the Kock–Lawvere THEOREM;
`Cat.Instances.SuperSmoothSets`, `.Singular`, `.NegativeSpheres` are
the other probe columns. `Cat.Site.Sheafification.{Kernel,Topos}`:
the sheafification unit's kernel is saturated local equality, and
`Sheaves-topos : Topos ℓ Sh[ C , J ]` — cite these rather than
reproving. Reals: `Data.Real.{Base,Arithmetic,Order}` (order, additive
group, lattice, archimedean, Bishop approximation; NO multiplication
yet). Cohomology: `Algebra.ChainComplex.{Moore,DoldKan}` gives
`K A n` and `H[ X , n ]⟨ A ⟩`. Internal ∞-topoi:
`Homotopy.Modality` (RSS modalities, lex = sub-∞-topoi).

## Gotcha corpus (each of these cost a debugging round once)

- Agda has NO inline type ascription `(e : T)`; use monomorphic
  operators or `Path T x y`.
- Non-injective type-level functions (`O`, `Moore`, `∣_∣`, `agree`)
  block implicit inference: pin implicits (`{B = B}`, `F₁ {X} {Y}`),
  and make TYPED helpers for ambiguous constructors
  (`inc-path : x ≡ y → Path (Quotient) (inc x) (inc y) ; inc-path = ap inc`).
- HIT constructors inherit module params implicitly; module-level
  functions take them explicitly (`Ω¹-elim-prop A φ …`).
- Eliminators are generated with explicit motives and cases
  (`make-elim-with default-elim-visible`); copattern clauses of one
  definition must be textually contiguous.
- `ext` on Σ-domain homs curries (`ext λ x p → …`); prefer `funext`
  or `Nat-path {C = _ ^op} {D = Sets ℓ}` for NT components.
- `cring!` (ring solver) works ONLY over an abstract `(R : CRing ℓ)`
  module parameter — prove identities abstractly, instantiate at
  concrete rings (ℤ-comm) where they bridge definitionally. Same for
  `group!`. State solver goals as named `private abstract` lemmas
  with full explicit signatures; never inline in `ap₂`.
- Functions pattern-matching ⦃instance⦄ args (`invℚ`) get stuck on
  instance METAS: pin like `*ℚ-invr {2} {2-nonzero}`.
- Closed decidable ℚ/discrete facts: `decide!`. ℚ's `_≤_` has NO
  fixity — parenthesize against `_+ℚ_`.
- `_⟪_⟫_` is ternary mixfix — no sections; use `F .F₁ f`.
- Prop-valued goals make merely-existing witnesses (`J .stable`,
  effectivity, class representatives) freely eliminable — architect
  proofs so the hard elimination happens at a prop. For inductive
  predicates needing this everywhere, define them as prop-valued
  HITs with UNTRUNCATED recursive families + a squash constructor
  (the `Loc-eq`/`is-covering` pattern); truncation-nested variants
  fail termination.
- Fibres of an injective map into a set are props — use this to
  extract from `∥_∥` without choice; inhabited + prop = contractible
  = `is-equiv` directly.
- 1lab `Fin` matches with `fin` patterns (`fin 0`, `fin (suc k)`),
  not `fzero`/`fsuc`.
- `Data.Rational` is `Ratio`; rational ops pattern-match `inc` of
  both args — stuck on variables, reason propositionally.

## Style

Literate `.lagda.md`: real mathematical prose between visible code
blocks; plumbing in `<!-- ```agda … ``` -->` hidden blocks; heading
`{defines="kebab-anchors"}`; wikilinks `[[target|anchor]]` must point
at existing `defines` anchors. Physics modules state their units and
conventions in prose, cite what they use with `` `name`{.Agda} ``,
and end by saying honestly what is *not* proven. New headline
theorems get a `_ = theorem` link block added to `src/Physics.lagda.md`
(and its missing-list updated) in a separate `chore:` commit.
