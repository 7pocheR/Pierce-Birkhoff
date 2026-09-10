# An eight-variable counterexample on a quadratic partition

**Parameters:** `n=8`, `d=2`, `k=2`, using ordinary total degree and the
[repository convention](../README.md).

This construction gives a continuous function on all of `ℝ⁸`, with quadratic
polynomial pieces determined by quadratic sign conditions, and no finite
maximum/minimum representation by real polynomials of arbitrary degrees.
It gives a negative answer to the Pierce–Birkhoff question for quadratic
partitions.

- [Manuscript (PDF)](quadratic_partition_counterexample8.pdf)
- [LaTeX source](quadratic_partition_counterexample8.tex)
- [Explicit polynomial data](lean/PBCounterexample/Quadratic8Data.lean)
- [Final formal statements](lean/PBCounterexample/Quadratic8Main.lean)
- [Expanded statement checks](lean/verification/Statements8.lean)
- [Literal coordinate formula checks](lean/verification/Formula8.lean)
- [Lean project and verification instructions](lean/README.md)
- [Recorded formal verification and execution evidence](verification/RECORD.md)
- [Supplementary exact algebra checks](verify_cofactor_extension.py)

## Function and partition

The independent coordinates are `(x,y,z,u,v,r,s,t)`. Starting from the four
quadratic labels `qⱼ` of the [six-variable example](../n=6_d=3_k=2/), put
`c₁=x(−v+r/2)+y(z+u)`, `c₂=−(x²+y²)`, `E₁=s−c₁`, and `E₂=t−c₂`.
The sixteen labels are `Lⱼ,ₖ,ε=qⱼ+8εEₖ`, for four choices of `j`, two
choices of `k`, and `ε∈{−1,1}`. Let `H` be their minimum and let
`O=zs+(r/2)t`. The function is `H` where `H>0` and `O>0`, and zero
elsewhere. The determinant estimate in the manuscript proves that `O`
cannot vanish when `H>0`, giving continuity on the whole space.

The partition tests are `O`, the sixteen labels, and their 120 unordered
pairwise differences. Thus there are 137 supplied quadratic tests. Their
signs select one polynomial on each entire sign realization, including
all disconnected components and all zero signs. The count is of supplied
tests, not nonempty regions; no minimality or absence of redundant tests
is asserted. The same function admits a cover by 17 closed semialgebraic
polynomial pieces.

The final theorem is
`PBCounterexample.Quadratic8.whole_space_counterexample`.
It has no mathematical hypotheses and states continuity, the quadratic
sign partition, the closed cover, and nonrepresentation. The domain has
eight independent real coordinates. Restriction to the polynomial graph
`s=c₁, t=c₂` recovers the six-variable function and is used only in the
nonrepresentation proof. The representing polynomials have arbitrary real
coefficients and unrestricted degrees.

## Degrees

All partition tests have ordinary total degree at most two; `O` contains
`zs` with coefficient one, so the displayed partition has exact degree two.
All sixteen nonzero labels also have exact degree two. The coefficients
of `x²` in the four `qⱼ` are `2,2,2,−2`; its coefficients in `E₁,E₂` are
`0,1`. Thus none of the coefficients of `x²` in `qⱼ±8Eₖ` vanishes.

A quadratic piece is attained on a nonempty open region. The function is
continuous, nonnegative, and not identically zero, since the zero function
has a polynomial lattice representation. Its positive set is therefore
nonempty and open. Removing the zero sets of the nonzero pairwise label
differences leaves a point where one distinct polynomial is strictly
minimal, and it stays minimal in a neighborhood. Identical labels, if
present, can be grouped together. Consequently the function cannot be
described by finitely many affine labels: on that neighborhood, their
differences from the selected quadratic would be finitely many nonzero
polynomials whose zero sets cover an open set. This also justifies the
exact spline degree `k=2`. The frozen Lean theorem proves the degree
bounds; this paragraph supplies the elementary exactness argument.

## Verification

The project pins Lean `v4.34.0-rc1` and Mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`. The recorded run freshly built
all 35 project modules, checked the expanded statement and literal formula,
and replayed the mathematical dependency closure into an initially empty
Lean kernel environment at trust level zero. The only admitted axioms were
`propext`, `Classical.choice`, and `Quot.sound`. The
[verification record](verification/RECORD.md) specifies the source identity,
execution evidence, and scope of trust.

The complete Lean project is preserved unchanged from that run. Its inner
README refers to DSI because this project's substantial computation runs
there; external users do not need DSI access. With the pinned toolchain and
dependency artifacts, `bash verify.sh` from `lean` runs the documented
checks. This can use an incremental build. Reproducing the stronger fresh
build requires the separate Linux setup described in the verification
record. Historical machine paths in the execution logs are evidence of the
recorded run, not portable commands.

The supplementary Python file requires SymPy and checks exact algebraic
identities. It is outside the Lean source manifest and is not a premise of
the formal proof. No completed human expert review or minimum possible
counterexample dimension is claimed.
