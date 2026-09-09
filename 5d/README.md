# A five-variable piecewise cubic counterexample

**Review status:** The proof is currently being checked by our human expert;
that review has not yet been completed.

This directory contains an explicit continuous function on all of `ℝ⁵`, with
five closed semialgebraic polynomial pieces: zero and four polynomials of
degree at most three. Its complete Lean statement excludes every finite
maximum/minimum expression in real polynomials, with no restriction on their
degrees, coefficients or number.

- [Five-variable manuscript](pb_counterexample5.pdf)
- [LaTeX source](pb_counterexample5.tex)
- [Final formal statements](lean/PBCounterexample/Gram5Main.lean)
- [Lean project and verification instructions](lean/README.md)
- [Recorded formal verification](lean/verification/RECORD.md)

The five independent coordinates are `(a,b,c,d,e)`. The manuscript specifies
a polynomial `5 × 3` matrix `C`, sets `Q = Cᵀ diag(1,1,3,−1,−1) C`, and
defines four polynomial labels from `Q`. Let `h` be their minimum and `D`
the signed determinant of the first three rows of `C`. The function is `h`
where `h > 0` and `D > 0`, and zero elsewhere. The implication
`h > 0 → D ≠ 0` gives continuity and the stated closed cover.

The proof constructs two actual real points for every finite collection
of proposed polynomial leaves. Weighted polynomial decomposition controls
all leaves, including those of arbitrarily high degree.

The main closed existential theorem is
`PBCounterexample.Gram5.exists_whole_space_counterexample`.
The same namespace contains `whole_space_counterexample` for the specified
function and `not_finite_sup_inf_polynomials` for the explicit finite
max–min formulation. Independent expanded statements bind the formal result
to the displayed function, cover and labels.

## Scope

The domain is the whole five-dimensional real affine space, not a proper
algebraic subset. The piece labels have degree at most three; the displayed
partition also uses the determinant polynomial `D`. No claim of minimum
possible dimension, or of a resolution of PB(3) or PB(4), is made.

The standalone `lean` project contains 24 implementation modules, an import
wrapper, three independent mathematical modules, and separate verification
programs. It does not import or rebuild a higher-dimensional example.
The other constructions are indexed in the [repository README](../README.md).
The human-written 30-dimensional proof is in the [main paper](../paper.pdf).

## Reproducing the checks

The project pins Lean `v4.34.0-rc1` and Mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`, together with all transitive
dependency revisions. On Linux, use `./verify.sh` from `lean` with the
requirements in its [README](lean/README.md).

The recorded completed run freshly compiled the released mathematical sources
and replayed their entire logical dependency closure in an initially empty
Lean kernel environment at trust level zero. Only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` were admitted. The
[verification record](lean/verification/RECORD.md) includes the complete
audit output and distinguishes this completed run from the portable shell
script, which has not itself completed an external reproduction.

Formal verification concerns the exact Lean declarations and uses Lean's
standard classical foundations. Source-level mathematical review, human
peer review, and verification of Lean by an independent implementation are
separate matters.

## AI assistance

GPT-6 assisted in the development and review of the five-dimensional work.
