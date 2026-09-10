# A seven-variable piecewise quadratic counterexample

**Parameters:** `n=7`, `d=3`, `k=2`, using ordinary total degree and the
[repository convention](../README.md).

**Review status:** The proof is currently being checked by our human expert;
that review has not yet been completed.

This directory contains an explicit continuous function on all of `ℝ⁷`, with
six closed semialgebraic polynomial pieces: zero and five homogeneous
quadratics. Its complete Lean statement excludes every finite maximum/minimum
expression in real polynomials, with no restriction on their degrees,
coefficients or number.

- [Seven-variable manuscript](pb_counterexample7.pdf)
- [LaTeX source](pb_counterexample7.tex)
- [Finite exact certificate](verify_certificate7.py)
- [Final formal statements](lean/PBCounterexample/Gram7Main.lean)
- [Lean project and verification instructions](lean/README.md)

The seven independent coordinates parametrize a specified rational linear
space of pairs `(A,B)`, where `A` is a `3 × 3` matrix and `B` is a `2 × 3`
matrix. The matrix entries are linear functions of those seven coordinates.
Write `Q = AᵀA − BᵀB`, let `vᵢ = 4eᵢ − (1,1,1)` for `i < 3`,
and let `v₃ = (−1,−1,−1)`. The five labels are `−vᵢᵀQvⱼ` for the edges
`01, 02, 03, 12, 13`. If `h` is their minimum, the function is `h` where
`h > 0` and `det A > 0`, and zero elsewhere. The manuscript specifies the
coordinate matrix and proves all properties of this formula.

The main closed existential theorem is
`PBCounterexample.Gram7.pierce_birkhoff_fails_in_dimension_seven`.
The same namespace contains `counterexample` for the specified function and
`no_finite_max_min_representation` for the explicit finite max–min formulation.

## Scope

The domain is the whole seven-dimensional real affine space, not a proper
algebraic subset. The polynomial labels are quadratic; the displayed
partition also uses the cubic polynomial `det A`. For the independent
coordinates `(w₂,w₅,w₈,w₉,w₁₂,w₁₀,w₁₃) = (0,1,0,0,0,0,0)`, the
determinant is `−1/27` and the retained label `q₀₃` is `94/81`.
Thus the homogeneous determinant and quadratic labels attain the stated
maximum degrees. Their signs and pairwise label comparison signs give the
degree-three partition. No claim of minimum possible dimension, or of a
resolution of PB(3), is made.

The standalone `lean` project contains only the 35 mathematical modules
needed for this construction, together with an import wrapper and separate
verification programs. It does not import or rebuild a higher-dimensional
example. The other constructions are indexed in the [repository README](../README.md).
The human-written 30-dimensional proof is in the [main paper](../paper.pdf).

## Reproducing the checks

The Lean project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`. After installing the pinned
toolchain through Elan, enter `lean`, obtain dependency artifacts with
`lake exe cache get`, and run `bash verify.sh`. See the
[verification instructions](lean/README.md) for the precise scope.

The auxiliary arithmetic certificate can be run with
`python3 -B verify_certificate7.py`; it requires NumPy. Its printed ranks
are `7, 23, 5`, with nonzero minor residues `693, 349, 256` modulo `1009`.
The complete formal proof does not depend on trusting this Python program.

Formal verification concerns the exact Lean declarations and uses Lean's
standard classical foundations. Source-level mathematical review, human
peer review, and verification of Lean by an independent implementation are
separate matters.

## AI assistance

GPT-6 and Claude 5.1 assisted in the development and review of this work.
