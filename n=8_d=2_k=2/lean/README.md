# Eight-dimensional quadratic-partition formalization

This standalone Lean project defines a function on all of `Fin 8 → ℝ` in
`PBCounterexample/Quadratic8Data.lean`. Its final theorem is
`PBCounterexample.Quadratic8.whole_space_counterexample` in
`PBCounterexample/Quadratic8Main.lean`. It states, without mathematical
hypotheses, that this function is continuous, admits a partition specified
by 137 real polynomial sign tests of ordinary total degree at most two,
admits a cover by seventeen closed semialgebraic regions with quadratic
polynomial labels, and has no finite polynomial lattice representation.

A sign realization comprises every point with a specified assignment of
negative, zero, or positive signs to all tests. One quadratic polynomial
agrees with the function on the entire realization, including all connected
components. Empty realizations are permitted and have vacuous agreement.
The number 137 counts the supplied tests, not the number of nonempty regions;
no assertion that the list is minimal or free of redundant tests is made.

The obstruction concerns finite expressions built using maximum and minimum
from arbitrary `MvPolynomial (Fin 8) ℝ` leaves. Their coefficients are arbitrary
real numbers and their degrees are unrestricted. A separate theorem excludes
every nonempty finite maximum of nonempty finite minima of such polynomials.
The two additional coordinates are independent real variables. Polynomial
graph substitution is used only to transfer a hypothetical representation
to the established six-dimensional example.

## Mathematical modules

`Quadratic8Data` gives the explicit cofactors, sixteen labels, scalar minimum,
orientation, and exact graph restriction. `Quadratic8Geometry` proves a
quantitative determinant estimate and nonvanishing of the orientation on
the positive set of the minimum. `QuadraticSignPartition` constructs labels
on full sign realizations. `Quadratic8Partition` establishes the ordinary
total-degree bounds and the 137-test count. `Quadratic8Main` supplies continuity,
the closed cover, and the unconditional final theorem. The other 29 modules
are the six-dimensional proof and its dependencies.

The formal partition chooses a consistent minimizing label on a realization.
It need not choose the smallest index specified in the manuscript: minimizing
labels agree in value wherever they tie. The geometry uses a scalar algebraic
proof of the determinant estimate. The global equality of the signs of the
orientation and original determinant away from the graph is not separately
exported; nonvanishing and exact graph restriction suffice for the final result.

## Verification

Use the toolchain in `lean-toolchain` and the Mathlib revision in
`lake-manifest.json`. Obtain dependency artifacts with `lake exe cache get`,
then run `bash verify.sh`. The project requires substantial computation and
must be built on the DSI cluster under this repository's instructions.

The script checks a source manifest, builds the project, checks independently
stated interfaces in `verification/Statements8.lean`, checks the literal
coordinate formula in `verification/Formula8.lean`, and executes
`verification/TrustReplay8.lean`. All verification invocations use `--trust=0`.
It checks the source manifest again afterward. An incremental Lake build is
not a fresh source build; independent acceptance additionally requires an
empty project output directory and a search path excluding all previous
project artifacts.

The replay program enumerates all 34 mathematical project modules. It
traverses raw declaration types and proof bodies, rejects unsafe or partial
mathematical dependencies and unapproved axioms, and validates the exact
schemas, universe arities, and defining module origins of `propext`,
`Classical.choice`, and `Quot.sound`. It replays the entire dependency closure
into an initially empty Lean kernel environment at trust level zero.

Two compiler-generated partial implementations in `Radial` are accounted
for separately: `LatticeExpr.evalWith._unsafe_rec` and
`LatticeExpr.leaves._unsafe_rec`. Their complete stored and effective records,
parents, types, origins, and compiler metadata must satisfy exact checks.
They must be absent from every accepted mathematical dependency and from
the replayed environment. Their operational implementations are not accepted
as mathematical proofs.

Stored theorem bodies that differ from effective bodies are retained only
when all other declaration fields agree. Each retained body has a separate
raw dependency inspection with references back to its original name rejected,
then receives a fresh-name kernel check after the full dependency replay.
Negative controls exercise hidden axioms, missing dependencies, altered axiom
schemas, unsafe and partial references, changed records, circular stored
proofs, and invalid proofs. An invalid alternate proof must be rejected even
after a valid theorem of the same original name has been replayed.

The verification programs do not supply assumptions to the mathematical
proof. The two separate formula and interface checks require their own
successful execution logs; their declarations are outside the 34-module
project inventory. Source manifests bind the reported sources to the build
and audit executions. Successful replay remains relative to the pinned Lean
kernel, runtime, and standard axioms. It is not verification by a second
kernel implementation, and it does not replace review of mathematical
meaning. Build and audit outcomes are recorded in the internal campaign
checkpoint, separately from this description of the verification procedure.
