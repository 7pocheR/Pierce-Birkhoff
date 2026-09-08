# A six-variable piecewise quadratic counterexample

**Review status:** The proof is currently being checked by our human expert;
that review has not yet been completed.

This branch contains an explicit continuous function on all of `ℝ⁶`, with
five closed semialgebraic polynomial pieces: zero and four homogeneous
quadratics. Its complete Lean statement excludes every finite maximum/minimum
expression in real polynomials, with no restriction on their degrees,
coefficients or number.

- [Six-variable manuscript](pb_counterexample6.pdf)
- [LaTeX source](pb_counterexample6.tex)
- [Finite exact certificate](verify_certificate6.py)
- [Final formal statements](lean6/PBCounterexample/Gram6Main.lean)
- [Lean project and verification instructions](lean6/README.md)

The six independent coordinates specify a rational `5 × 3` matrix `C`.
Let `A` be its first three rows, `β = diag(1,1,3,−1,−1)`, and `Q = CᵀβC`.
Set `vᵢ = 4eᵢ − (1,1,1)` for `i < 3` and `v₃ = (−1,−1,−1)`.
The four labels are `−vᵢᵀQvⱼ` for the edges `01, 03, 12, 13`.
If `h` is their minimum, the function is `h` where
`h > 0` and `det A > 0`, and zero elsewhere. The manuscript specifies the
coordinate matrix and proves all properties of this formula.

The main closed existential theorem is
`PBCounterexample.Gram6.exists_whole_space_counterexample`.
The same namespace contains `whole_space_counterexample` for the specified
function and `not_finite_sup_inf_polynomials` for the explicit finite
max–min formulation.

## Scope

The domain is the whole six-dimensional real affine space, not a proper
algebraic subset. The polynomial labels are quadratic; the displayed
partition also uses the cubic polynomial `det A`. No claim of minimum
possible dimension, or of a resolution of PB(3), is made.

The standalone `lean6` project contains only the 29 mathematical modules
needed for this construction, together with an import wrapper and separate
verification programs. It does not import or rebuild a higher-dimensional
example. The earlier `lean7` and `lean` projects and their manuscripts are
retained unchanged as legacy material. The collaborator's separate 30-dimensional
construction is available on the [main branch](https://github.com/7pocheR/Pierce-Birkhoff/tree/main).

## Reproducing the checks

The Lean project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`. After installing the pinned
toolchain through Elan, enter `lean6`, obtain dependency artifacts with
`lake exe cache get`, and run `bash verify.sh`. See the
[verification instructions](lean6/README.md) for the precise scope and the
differences between some intermediate manuscript and Lean arguments.

The auxiliary arithmetic certificate can be run with
`python3 -B verify_certificate6.py`; it requires SymPy and unoptimized Python.
It checks 50 exact algebraic assertions, including the quadratic-curve and
joint-kernel ranks `11` and `18`, with integer minor determinants `2³⁵` and `2⁶⁹`.
The complete formal proof does not depend on trusting this Python program.

Formal verification concerns the exact Lean declarations and uses Lean's
standard classical foundations. Source-level mathematical review, human
peer review, and verification of Lean by an independent implementation are
separate matters.

## AI assistance

GPT-6 and Claude 5.1 assisted in the development and review of this work.
