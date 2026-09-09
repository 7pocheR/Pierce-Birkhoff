# Lean formalization

The main construction formalizes the forty-label function in
[the 30-dimensional manuscript](../pb_counterexample_30d.pdf) on two symmetric
five by five real matrices. Their thirty upper-triangular entries are
independent real coordinates, and the final function is defined on all of
`Fin 30 → ℝ`. Symmetry is encoded by the coordinates; no determinant, rank,
positivity, or matrix-product condition restricts the domain.

## Main statements

The following declarations are in the namespace
`PBCounterexample.Collaborator30Main`, in
[Collaborator30Main.lean](PBCounterexample/Collaborator30Main.lean):

- `pierce_birkhoff_counterexample30`: there is a continuous function on all
  of `Fin 30 → ℝ` with a finite closed semialgebraic polynomial cover and no
  polynomial lattice representation.
- `explicit_quadratic_counterexample30`: the specified function `f30` is
  continuous, has a cover with 41 pieces and homogeneous quadratic polynomial
  labels, is positively homogeneous of degree two, and has no polynomial
  lattice representation.
- `no_finite_max_min_representation`: `f30` is not any nonempty finite maximum
  of nonempty finite minima of arbitrary real multivariate polynomials.

[Collaborator30Function.lean](PBCounterexample/Collaborator30Function.lean)
defines `qᵢⱼ,τ = (XY)ᵢᵢ + 4τ(XY)ᵢⱼ` for the twenty ordered pairs `i ≠ j`
and both signs `τ = ±1`. It uses raw `XY`, which need not be symmetric.
The function equals the minimum `h` of these forty labels when `h > 0` and
`det X > 0`, and equals zero otherwise. The closed cover has zero plus those
forty labels.

`IsPolynomialLattice`, defined in [Basic.lean](PBCounterexample/Basic.lean),
uses finite trees with unrestricted real polynomial leaves and the actual
real `max` and `min` operations. No bound on polynomial degree, real
coefficients, number of leaves, or expression depth is imposed.
`FiniteClosedPolynomialCover`, defined in
[Semialgebraic.lean](PBCounterexample/Semialgebraic.lean), requires closed
semialgebraic regions covering the entire coordinate space and polynomial
agreement at every point of every region. The degree-two assertion concerns
the labels, with zero homogeneous in the usual convention. The defining
inequalities also use `det X`, of degree five.

## Other included constructions

[SymmetricMain.lean](PBCounterexample/SymmetricMain.lean) provides a different
function on the same whole space `Fin 30 → ℝ`, using fifteen quadratic labels
and a cover with sixteen pieces. Its namespace is
`PBCounterexample.SymmetricMain`. The labels are defined in
[SymmetricFunction.lean](PBCounterexample/SymmetricFunction.lean) using
`(XY + YX)/2` and six specified vectors. This is not the forty-label function
in the linked PDF. Neither construction is claimed to have minimum possible
ambient dimension.

The original [Main.lean](PBCounterexample/Main.lean),
[PDF](../../72d/pierce_birkhoff_counterexample.pdf), and
[LaTeX source](../../72d/pierce_birkhoff_counterexample.tex) are retained for the
legacy 72-dimensional construction on two unrestricted six by six matrices.
Its main declarations are in `PBCounterexample`, without either new main
namespace. Its cover has 193 pieces and uses a degree-six determinant.

## Verification commands and their scope

The project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`. Dependency revisions are recorded
in `lake-manifest.json`. Install the pinned Lean toolchain through Elan.
A first installation can obtain the pinned mathlib build artifacts with
`lake exe cache get`.

From this directory, run `bash verify.sh`. The script requires Lake and
`rg`. It checks the proof sources, builds all published mathematical modules,
and runs `PBCounterexample/Audit.lean` together with these dedicated checks:

- `verification/Statements30.lean` prints and checks selected definitions
  and expanded final statements for the two 30-dimensional constructions.
  It does not itself establish that their mathematical interpretation agrees
  with the manuscript.
- `verification/FoundationTypes30.lean` compares the exact syntactic types
  and universe parameters of the allowed axioms `propext`,
  `Classical.choice`, and `Quot.sound` with explicitly constructed Lean
  expressions. It does not check coordinate, polynomial, or topology
  semantics.
- `verification/RawAudit30.lean` enumerates all declarations defined by the
  project modules in the complete import closures of both 30-dimensional
  constructions, including private declarations and declarations outside
  the public project namespace. It traverses stored types and proof bodies,
  including stored equation-theorem bodies, rather than relying only on
  cached axiom-dependency metadata. It checks for extra axioms and unsafe or
  partial dependencies of safe mathematical declarations. Generated runtime
  helpers are considered separately from the safe proof dependencies.

The legacy `PBCounterexample/Audit.lean` checks the original 72-dimensional
declarations and their axiom dependencies. It is not the new 30-dimensional
verification. These verification files are not imported by the mathematical
proofs.

### Builds and source correspondence

The normal Lake build is incremental: local artifacts that Lake considers
current may be reused. Disabling package-cache downloads does not force
existing local artifacts to be rebuilt. Downloading mathlib artifacts is
also not a source-only rebuild of mathlib.

To check the project sources without reusing their compiled artifacts,
build in a separate fresh checkout with no project build artifacts. This
still trusts any prebuilt dependency artifacts selected for that checkout.
A source-only rebuild extending to dependencies must also compile those
dependencies from their pinned sources. Neither procedure independently
verifies the compiler, kernel implementation, or runtime.

### Optional kernel replay

After building, run `lake env lean verification/TheoremReplay30.lean` to
replay the dependency closures of the six final theorems selected in that
file. It traverses their stored dependencies and checks the collected safe
declarations in an empty kernel environment using Lean's bundled replay
implementation. Its scope is those six theorem closures, not every
declaration in every project module as a separate root. In contrast,
`RawAudit30.lean` inspects all declarations in the complete 30-dimensional
project-module closures; that broader dependency inspection is not itself a
kernel replay.

An empty kernel environment is not a source rebuild. Replay checks the
compiled artifacts selected by the current `LEAN_PATH`; it does not prove
that they were produced from the displayed sources. It uses Lean's own
kernel, not an independent implementation, and permits declared axioms.
The separate axiom and axiom-type checks therefore remain necessary.

The older `verification/RawAudit.lean`,
`verification/FreshProofReplay.lean`, and the command
`lake env leanchecker --fresh PBCounterexample.Main` remain available for
the legacy 72-dimensional imported environment. They are not substitutes
for the checks of the new 30-dimensional statements.

### Trust and mathematical interpretation

The proofs use Lean's standard classical foundations, including `propext`,
`Classical.choice`, and `Quot.sound`; they are not claimed to be axiom-free.
The verification programs, selected dependency artifacts, Lean kernel, and
execution runtime remain part of the trust assumptions. Dependency
inspection, source rebuilding, and kernel replay address different aspects
of verification; none alone establishes the intended mathematical meaning
of a definition or correspondence with a PDF.

The 30-dimensional construction and the proof in the [main paper](../../paper.pdf)
have undergone careful human expert checking. Formal verification and
journal peer review are distinct from that mathematical checking.

## Proof organization

`Collaborator30Function.lean` proves the whole-space cover, continuity, and
homogeneity for the forty-label function. Positivity of both signed labels
implies strict row diagonal dominance of `XY`, hence invertibility of `X`;
this implication is proved, not assumed when constructing the closed cover.

The shared `Radial.lean`, `RadialPolynomial.lean`, and `RadialScalar.lean`
derive a finite degree-at-most-two sign condition from a hypothetical lattice
expression with arbitrary-degree leaves and positive degree-two homogeneity.
The degree bound is on the resulting sign tests, not on the proposed leaves.

`SymmetricOrbitVanishing.lean` and its dependencies classify degree-at-most-two
polynomials vanishing on the symmetric matrix orbit. `SymmetricGenericPoint.lean`
selects a common point for a finite polynomial family. `SymmetricPerturbation.lean`
constructs two paths with identical matrix products and different determinant
signs, and `SignTopology.lean` selects a positive parameter preserving the
required finite family of signs. `Collaborator30SignObstruction.lean` combines
these results for the forty-label function. The fifteen-label variant has
its own function and obstruction in `SymmetricFunction.lean` and
`SymmetricSignObstruction.lean`.

`Reindexing.lean` and `FiniteExpressions.lean` provide the coordinate
equivalences and finite maximum-of-minima interfaces for the main theorems.
