# A piecewise quadratic function without a polynomial lattice representation

**Review status:** The work is currently being checked by our human expert;
that review has not yet been completed. No completed human expert review of
the 30-dimensional construction is claimed.

The main construction is an explicit function on the whole space
`Sym₅(ℝ) × Sym₅(ℝ)`, identified with `ℝ³⁰` by the thirty independent
upper-triangular entries of two symmetric real matrices. Its formal statement
asserts continuity, a cover by 41 closed semialgebraic sets with homogeneous
quadratic polynomial labels, and no finite maximum/minimum expression using
real polynomials of arbitrary degrees.

- [30-dimensional manuscript](pb_counterexample_30d.pdf)
- [Exact function and its forty labels](lean/PBCounterexample/Collaborator30Function.lean)
- [Final 30-dimensional statements](lean/PBCounterexample/Collaborator30Main.lean)
- [Lean project and verification instructions](lean/README.md)

The formula is the one in the linked 30-dimensional PDF. Put `P = XY` and
take the forty labels `qᵢⱼ,τ = Pᵢᵢ + 4τPᵢⱼ`, for all ordered pairs `i ≠ j`
and both signs `τ ∈ {−1, 1}`. Although `X` and `Y` are symmetric, `P` need
not be symmetric. Let `h` be the minimum of these forty labels. Define `f = h`
where `h > 0` and `det X > 0`, and `f = 0` elsewhere. The forty labels and
zero supply the 41 pieces of the closed polynomial cover.

The main existential theorem is
`PBCounterexample.Collaborator30Main.pierce_birkhoff_counterexample30`.
In the same namespace, `explicit_quadratic_counterexample30` gives the
properties of this specified function, and `no_finite_max_min_representation`
explicitly excludes every nonempty finite maximum of nonempty finite minima
of unrestricted real multivariate polynomials.

## Scope and other constructions

The statement concerns the classical whole-space Pierce-Birkhoff conjecture
with a finite closed semialgebraic polynomial cover, as in Conjecture 1.1
and Definition 1.2 of [Wagner (2010)](https://www.numdam.org/item/10.5802/afst.1283.pdf).
The quadratic degree bound applies to the polynomial labels, not to every
polynomial defining the pieces: the 30-dimensional cover also uses the
degree-five determinant of `X`. The polynomials in a proposed maximum/minimum
representation have no degree or coefficient restriction. No claim of
minimum possible ambient dimension is made.

A separate [15-label construction](lean/PBCounterexample/SymmetricMain.lean)
is also formalized on all of `ℝ³⁰`, with 16 closed pieces. Its labels use
`(XY + YX)/2` and six specified vectors, as defined in
[SymmetricFunction.lean](lean/PBCounterexample/SymmetricFunction.lean).
It is a different explicit function, not the forty-label formula in the PDF.

The original 72-dimensional construction is retained as legacy material:

- [Original PDF](pierce_birkhoff_counterexample.pdf)
- [Original LaTeX source](pierce_birkhoff_counterexample.tex)
- [Original final Lean statements](lean/PBCounterexample/Main.lean)

It concerns two unrestricted six by six matrices, 193 closed pieces, and a
degree-six determinant in the partition. These files do not describe the new
30-dimensional formula.

## Reproducing the formal checks

The Lean project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`.
Install the pinned toolchain through Elan, enter the `lean` directory, obtain
the dependency artifacts with `lake exe cache get`, and run `bash verify.sh`.
The script builds the published mathematical modules and runs the legacy
audit together with the dedicated 30-dimensional statement, foundational
axiom-type, and proof-dependency checks. The normal build is incremental;
it is not a source-only rebuild of every dependency.

The optional `lake env lean verification/TheoremReplay30.lean` checks the
dependency closures of six selected final theorems in an empty kernel
environment. It does not replay every project declaration as a root. See the
[Lean README](lean/README.md) for the scope of each check and the distinction
between rebuilding source, inspecting dependencies, and kernel replay.

These checks concern exact Lean declarations. They use Lean's standard
classical foundations and trust its implementation and runtime. Mathematical
comparison with the manuscript, human peer review, and verification by an
independent kernel implementation are separate matters.

## AI assistance

GPT-6 and Claude 5.1 assisted in the development and review of this work.
