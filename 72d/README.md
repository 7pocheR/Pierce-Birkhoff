# The 72-dimensional construction

This is the original counterexample on two unrestricted six by six real
matrices. It has 193 closed semialgebraic pieces with homogeneous quadratic
labels and no finite maximum/minimum representation by real polynomials of
arbitrary degrees.

- [PDF](pierce_birkhoff_counterexample.pdf)
- [LaTeX source](pierce_birkhoff_counterexample.tex)
- [Lean project and verification instructions](lean/README.md)
- [Final formal statements](lean/PBCounterexample/Main.lean)

The defining partition also uses a degree-six determinant. The main Lean
theorem is `PBCounterexample.pierce_birkhoff_counterexample`.

The conceptually simpler, human-checked 30-dimensional proof is presented
in the [main paper](../paper.pdf). See the [repository README](../README.md)
for all constructions.
