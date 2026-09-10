# The 72-dimensional construction

**Parameters:** `n=72`, `d=6`, `k=2`, using ordinary total degree and the
[repository convention](../README.md).

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

The two matrices contribute 36 independent entries each. The determinant's
diagonal-product monomial has coefficient one, giving exact degree six.
Each of the 192 nonzero labels is a homogeneous quadratic containing
`XᵢᵢYᵢᵢ` with coefficient one. Their signs and pairwise comparison signs
have degree at most two; together with the determinant sign they give the
degree-six partition. On `(X,Y)=(tI₆,tI₆)` for `t>0`, the function equals
`t²`, so its quadratic degree is attained.

The conceptually simpler, human-checked 30-dimensional proof is presented
in the [main paper](../paper.pdf). See the [repository README](../README.md)
for all constructions.
