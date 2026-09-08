# Pierce–Birkhoff conjecture is false

Zehua Lai, Lek-Heng Lim, Junyu Ren

The Pierce-Birkhoff conjecture is a classical, longstanding problem in real
algebraic geometry, with roots in Birkhoff and Pierce's 1956 work on
lattice-ordered rings [1]. It asks whether every continuous piecewise
polynomial function on `ℝⁿ`, with finitely many semialgebraic pieces, can be
expressed using finitely many maxima and minima of polynomials. The
counterexample here gives a negative answer even when all polynomial pieces
are quadratic, while allowing polynomials of arbitrary degrees in the
proposed representation.

**Human expert checking:** The 30-dimensional construction and its proof have
undergone careful human expert checking. We present this version because its
proof is conceptually simple and readily checked by hand.

## Manuscripts and formalizations

- **30 dimensions, main paper:** [PDF](pb_counterexample_30d.pdf),
  [LaTeX source](manuscript/pb_counterexample_30d.tex),
  [Lean project and verification instructions](lean/README.md).
- **5 dimensions, piecewise cubic:** [PDF](pb_counterexample5.pdf),
  [LaTeX source](pb_counterexample5.tex),
  [Lean project](lean5/README.md),
  [recorded formal verification](lean5/verification/RECORD.md).
- **6 dimensions, piecewise quadratic:** [PDF](pb_counterexample6.pdf),
  [LaTeX source](pb_counterexample6.tex), [Lean project](lean6/README.md).
- **7 dimensions, piecewise quadratic:** [PDF](pb_counterexample7.pdf),
  [LaTeX source](pb_counterexample7.tex), [Lean project](lean7/README.md).
- **72 dimensions, original construction:**
  [PDF](pierce_birkhoff_counterexample.pdf),
  [LaTeX source](pierce_birkhoff_counterexample.tex),
  [final Lean statements](lean/PBCounterexample/Main.lean).

All five examples have Lean formalizations. Human expert review of the
5-, 6-, and 7-dimensional proofs is ongoing. The 30-dimensional paper is
the version that has undergone careful human expert checking.

The `lean`, `lean5`, `lean6`, and `lean7` directories are separate Lean
projects; run each project's checks from its own directory. The
[5d](https://github.com/7pocheR/Pierce-Birkhoff/tree/5d),
[6d](https://github.com/7pocheR/Pierce-Birkhoff/tree/6d),
[7d](https://github.com/7pocheR/Pierce-Birkhoff/tree/7d), and
[72d](https://github.com/7pocheR/Pierce-Birkhoff/tree/72d) branches retain
their published versions.

To compile the main paper, run `latexmk -pdf pb_counterexample_30d.tex`
from the `manuscript` directory. Its bibliography and figure are included.

## The 30-dimensional construction

The main construction is an explicit function on the whole space
`Sym₅(ℝ) × Sym₅(ℝ)`, identified with `ℝ³⁰` by the thirty independent
upper-triangular entries of two symmetric real matrices. Its formal statement
asserts continuity, a cover by 41 closed semialgebraic sets with homogeneous
quadratic polynomial labels, and no finite maximum/minimum expression using
real polynomials of arbitrary degrees.

- [Exact function and its forty labels](lean/PBCounterexample/Collaborator30Function.lean)
- [Final 30-dimensional statements](lean/PBCounterexample/Collaborator30Main.lean)

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

## Reproducing the 30- and 72-dimensional formal checks

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

This work used GPT and Claude models in our multi-agent, multi-model setup.
Agents exchanged constructions, proof attempts, objections, and corrections,
with roles assigned dynamically across model families. Section 5 of the
[main paper](pb_counterexample_30d.pdf) describes the setup and human input.

## References

[1] Garrett Birkhoff and R. S. Pierce, *Lattice-ordered rings*,
Anais da Academia Brasileira de Ciências **28** (1956), 41–69.
For the history of the conjecture and its later formulation, see
[Lucas, Madden, Schaub, and Spivakovsky, Section 1](https://arxiv.org/pdf/math/0601671).
