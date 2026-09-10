# Lean formalization

This project formalizes the explicit function in
`../pierce_birkhoff_counterexample.tex` on two independent six by six real
matrices, and transports it to the whole coordinate space `Fin 72 → ℝ`.

The main declarations in `PBCounterexample/Main.lean` are:

- `pierce_birkhoff_counterexample`: a continuous function on the whole space
  `Fin 72 → ℝ` with a finite closed semialgebraic polynomial cover and no
  polynomial lattice representation.
- `explicit_quadratic_counterexample72`: the explicit function `f72` has a
  cover with 193 pieces whose labels are homogeneous quadratic polynomials,
  and no polynomial lattice representation.
- `no_finite_max_min_representation`: `f72` is not any nonempty finite maximum
  of nonempty finite minima of real multivariate polynomials. The polynomial
  degrees are unrestricted.

`IsPolynomialLattice` uses finite trees with ordinary polynomial leaves and
the actual real `max` and `min` operations. `FiniteClosedPolynomialCover`
requires closed semialgebraic regions covering the entire coordinate space,
with polynomial agreement at every point of each region. The partition is
not asserted to be definable using quadratic inequalities alone: the
displayed cover also uses the degree-six determinant of the first matrix.

## Verification

The project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`. Dependency revisions are recorded
in `lake-manifest.json`.

From this directory, run `bash verify.sh`. The script requires Lake and
`rg`. It checks the proof sources, builds all project modules, and reruns
`PBCounterexample/Audit.lean`. Lake recomputes file hashes, but this remains
an incremental build: `--no-cache` disables downloading package build caches;
it does not force all existing local artifacts to be rebuilt.
A first installation can obtain the pinned
mathlib build artifacts with `lake exe cache get`; project proofs are still
built from their source in a fresh checkout with no project build artifacts.

`Audit.lean` is not imported by the mathematical proof. It checks that the
final and critical declarations exist as theorems and that their transitive
axiom dependencies are contained in `propext`, `Classical.choice`, and
`Quot.sound`. It prints the main theorem types for comparison with the
mathematical specification. These are the standard classical foundations
used here; the proof is not claimed to be axiom-free.

For a direct traversal of stored proof dependencies, run
`lake env lean verification/RawAudit.lean`. This verification-only program is
not imported by the mathematical proof. It enumerates declarations by their
defining project modules, including private names and declarations outside
the project namespace. It traverses actual types and proof bodies, including
duplicate stored equation-theorem bodies, rather than relying only on cached
axiom-dependency metadata. It rejects extra axioms and unsafe or partial
dependencies of safe mathematical declarations. Compiler-generated unsafe
runtime helpers are reported and examined separately; they must not be
reachable from the safe proof dependencies. This is a dependency inspection,
not itself a kernel replay or a source-to-artifact provenance check.

To replay exactly that complete mathematical dependency graph through the
kernel, run `lake env lean verification/FreshProofReplay.lean`. It performs
the same direct dependency traversal and then checks every collected safe
declaration in a newly empty kernel environment, using Lean's bundled replay
implementation. It requires every project root to retain its statement and
every supplied dependency to appear in the checked environment. This checks
the artifacts selected by the current `LEAN_PATH`; the word "fresh" refers
to the kernel environment, not to recompilation of source files.

For an additional kernel check after building, run
`lake env leanchecker --fresh PBCounterexample.Main`. This replays the safe,
nonpartial declarations in the entire imported environment, including
dependencies, from an empty kernel environment. It can be substantially more
expensive than an incremental build. It uses Lean's own kernel, not an
independent implementation, and it accepts declared axioms; the separate
axiom check remains necessary. It does not by itself establish that existing
build artifacts were produced from the displayed sources.

## Proof organization

`Function.lean` proves the whole-space cover, continuity, and quadratic
homogeneity. The three radial modules derive the finite quadratic sign
condition from arbitrary-degree polynomial lattice expressions.

`OrbitVanishing.lean` classifies all quadratic equations on the specified
matrix orbit. Its dependencies prove the polynomial decomposition, density
of invertible matrices, elimination of pure terms, explicit rank-one orbit
degenerations, and the bilinear classification.

`GenericOrbitPoint.lean` selects one common point for a finite polynomial
family. `Perturbation.lean` constructs the two paths, and `SignTopology.lean`
selects a common positive parameter preserving all required signs.
`SignObstruction.lean` combines these results into the contradiction.
`Reindexing.lean` and `FiniteExpressions.lean` provide the coordinate and
finite maximum-of-minima interfaces used in the final statement.
