# The 30-dimensional construction

This is the construction presented in the main paper. Its proof has undergone
careful human expert checking.

- [Paper (PDF)](pb_counterexample_30d.pdf)
- [LaTeX source](../paper.tex), with [bibliography and figure](../assets/)
- [Lean project and verification instructions](lean/README.md)
- [Exact function and its forty labels](lean/PBCounterexample/Collaborator30Function.lean)
- [Final formal statements](lean/PBCounterexample/Collaborator30Main.lean)

The function is defined on `Sym₅(ℝ) × Sym₅(ℝ)`, identified with `ℝ³⁰`.
Put `P = XY` and take the forty labels `qᵢⱼ,τ = Pᵢᵢ + 4τPᵢⱼ` for all
ordered pairs `i ≠ j` and both signs `τ ∈ {−1, 1}`. Let `h` be their
minimum. Define `f = h` where `h > 0` and `det X > 0`, and `f = 0`
elsewhere. The labels are quadratic; the displayed partition also uses
the degree-five determinant. Competing polynomial lattice representations
have no degree restriction.

The main theorem is
`PBCounterexample.Collaborator30Main.pierce_birkhoff_counterexample30`.
The same namespace contains `explicit_quadratic_counterexample30` for the
specified function and `no_finite_max_min_representation` for the explicit
finite max–min statement.

The Lean project also retains the earlier 15-label 30-dimensional variant
and shared modules from the original 72-dimensional construction. Its
[README](lean/README.md) distinguishes these functions and the scope of
verification. The original 72-dimensional manuscript and its separate Lean
project are in [72d](../72d/).

The PDF here is identical to the [main paper at the repository root](../paper.pdf).
Compile its source from the root with `latexmk -pdf paper.tex`.
