# Physics, in the 1Lab

> *Nothing in this development is asserted on authority. It typechecks,
> so the theorems exist.*

This is a fork of the [1Lab](https://1lab.dev) carrying the branch
`physics`: a constructive, zero-postulate, **computing** formalization
of the mathematical stack of Urs Schreiber's *Higher Topos Theory in
Physics* (arXiv:2311.11026) — probe sites and their gros topoi,
cohesion, nilpotent infinitesimals, fermionic algebra, gauge
groupoids, Dedekind reals, and the internal theory of higher toposes
— in cubical Agda, in the 1Lab's house style, on the 1Lab's
infrastructure.

The claim, bounded precisely: here the physics *is* the computation.
A harmonic oscillator specified once as a λ-term is compiled into the
topos of sets and **traces its orbit by `refl`**; its conservation
laws, force law, exclusion principle, and gauge redundancy are
theorems. The axioms of synthetic differential geometry are not
postulated but **proven** for an explicitly constructed site — the
Kock–Lawvere property is a theorem here, and mechanics proceeds with
nilpotents in place of limits.

## Where to start reading

- **The paper**: [`src/Physics/Paper.lagda.md`](src/Physics/Paper.lagda.md)
  — *Physics by refl*. Every claim is a typechecked hyperlink into the
  formalization; the paper is itself a module that fails to build if a
  theorem breaks.
- **The reading guide**: [`src/Physics.lagda.md`](src/Physics.lagda.md)
  — maps the paper's numbered diagrams, one by one, to their
  formalizations, and maintains the honest list of what is still
  missing.
- **The physics**: [`src/Physics/Oscillator.lagda.md`](src/Physics/Oscillator.lagda.md)
  — one system through every column of the probe table: compiled
  dynamics (orbit by `refl`, energy conservation and exact period-four
  time symmetry for *all* states), the force derived synthetically
  from the potential, exact conservation along the infinitesimal
  Hamiltonian flow (with the Euler integrator's energy drift computed
  as precisely the `dt²` term nilpotency kills), Pauli exclusion as
  ring algebra, and the gauged parity symmetry whose homotopy quotient
  provably remembers the stabilizer a quotient set would destroy.

Highlights elsewhere in the stack: the free-CCC compilation pipeline
(`Cat.CartesianClosed.Free.*`), cohesion over any pointed probe site
(`Cat.Instances.Presheaf.Cohesive`), the thickened site with the
Kock–Lawvere theorem (`Cat.Instances.FormalSmoothSets`), the
non-concrete de Rham classifier, the super site with its terminal
super point (`Cat.Instances.SuperSmoothSets`), Grassmann algebras with
the CAR/Pauli theorems, homotopy quotients and nonabelian `H¹`, Čech
objects, Moore complexes, the site of negative-dimensional spheres,
Dedekind reals with order, lattice and additive-group structure
(`Data.Real.*`), and modalities à la Rijke–Shulman–Spitters with lex
modalities as internal sub-∞-toposes (`Homotopy.Modality`).

## Checking it

Every module typechecks with the 1Lab's Mikan (Agda) toolchain — see
the upstream build instructions below. The development discipline: one
typechecker process at a time, every commit gated on a clean exit
code, zero postulates throughout (`grep -r postulate src/Physics
src/Data/Real` returns nothing).

## Provenance

All infrastructure, style, and the mathematical substrate belong to
the [1Lab and its contributors](https://1lab.dev) — this fork adds a
physics stack on top and is developed independently of upstream. The
new modules were written by Claude (Anthropic) as a human-directed
agent system, with the typechecker as sole arbiter; see the paper's
colophon.

---

# Building

Building the 1Lab is a rather complicated task, which has led to a lot
of homebrew infrastructure being developed for it. We build against a
specific build of Mikan (see the arguments to `fetchgit` in
`support/nix/haskell-packages.nix`), and there are also quite a few
external dependencies (e.g. pdftocairo, katex). The recommended way of
building the 1Lab is using Nix.

As a quick point of reference, `nix-build` will type-check and compile
the entire thing, and copy the necessary assets to the right locations.
The result will be linked as `./result`, which can then be used to serve
a website:

```bash
$ nix-build
$ python -m http.server --directory result # e.g.
```

Note that using Nix to build the website takes around 15 minutes, since
it will type-check the entire codebase from scratch every time.  For
interactive development, `nix-shell` will give you a shell with
everything you need to hack on the 1Lab, including Mikan and the
pre-built Shakefile as `1lab-shake`:

```bash
$ 1lab-shake all -j
```

Since `nix-shell` will load the derivation steps as environment
variables, you can use something like this to copy the static assets
into place:

```bash
$ eval "$installPhase"
$ python -m http.server --directory _build/site # e.g.
```

To hack on a file continuously, you can use "watch mode", which will
attempt to only check and build the changed file.

```bash
$ 1lab-shake all -w
```

Additionally, since the validity of the Mikan code is generally upheld
by `agda-mode`, you can use `--skip-agda` to only build the prose. Note
that this will disable checking the integrity of link targets, the
translation of `` `ref`{.Agda} `` spans, and the code blocks will be
right ugly.

Our build tools are routinely built for x86_64-linux and uploaded to
Cachix. If you have the Cachix CLI installed, simply run `cachix use
1lab`. Otherwise, add the following to your Nix configuration:

```
substituters = https://1lab.cachix.org
trusted-public-keys = 1lab.cachix.org-1:eYjd9F9RfibulS4OSFBYeaTMxWojPYLyMqgJHDvG1fs=
```

If you ever need to work on the Shakefile itself, `nix-shell -A shakefile`
will give you a shell with all the required Haskell dependencies and a
working Haskell Language Server installation. You can then use
`cabal run 1lab-shake -- all -j` to build the Shakefile and the 1Lab.

## Directly

If you're feeling brave, you can try to replicate one of the build
environments above. You will need:

- The `cabal-install` package manager. Using `stack` is no longer supported.

- A working LaTeX installation (TeXLive, etc) with the packages
  listed in `default.nix` (see `our-texlive`).

- [Poppler](https://poppler.freedesktop.org/) (for `pdftocairo`);
- [Dart Sass](https://github.com/sass/dart-sass) (for `sass`);
- [Node](https://nodejs.org/en/) + required Node modules. Run `npm ci` to install those.

You can then use cabal-install to build and run our specific version of
Mikan and our Shakefile. Follow the instructions in `cabal.project` to
pin Mikan to the appropriate version, then run:

```bash
$ cabal install Mikan -foptimise-heavily
# This will take quite a while!

$ cabal run 1lab-shake -- -j --skip-agda all
# the double dash separates cabal-install's arguments from our
# shakefile's.
```

To finish building the website, you will also need to manually install
the required assets: see the `installPhase` in `default.nix`.
