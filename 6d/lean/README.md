# Six-variable Lean formalization

This standalone project proves the whole-space six-variable assertion in
[Gram6Main.lean](PBCounterexample/Gram6Main.lean). The function and its closed
cover are defined in [Gram6Function.lean](PBCounterexample/Gram6Function.lean),
using the independent coordinates in
[Gram6Coordinates.lean](PBCounterexample/Gram6Coordinates.lean).

The final theorem has no mathematical hypotheses. It asserts the existence
of a continuous function on `Fin 6 → ℝ` with a five-region finite closed
semialgebraic cover, homogeneous quadratic labels, and no finite polynomial
lattice representation. The labels are zero and four quadratics. A separate
theorem excludes every nonempty finite maximum of nonempty finite minima.
Every polynomial allowed in a proposed representation has arbitrary real
coefficients and unrestricted degree.

## Build and verification

Install Elan and the toolchain in `lean-toolchain`. In this directory run
`lake exe cache get` to obtain the pinned dependency artifacts, followed by
`bash verify.sh`. Python is not required for the Lean proof. This project
contains 29 mathematical modules and a one-import library wrapper; neither
the build nor the verification imports a higher-dimensional example.

The verification script performs three distinct checks:

1. Source-manifest comparison followed by an ordinary incremental Lake build.
2. Explicit checks of the whole-space continuity, finite closed semialgebraic
   polynomial cover, and unrestricted polynomial expression statements in
   [Statements6.lean](verification/Statements6.lean).
3. Raw dependency inspection and replay into an initially empty Lean kernel
   environment in [TrustReplay6.lean](verification/TrustReplay6.lean).

Both verification programs are invoked with `--trust=0`. The source manifest
is checked again after execution. The replay program enumerates declarations
from all 29 imported project modules, including additional project-origin
kernel declarations, rather than inspecting only the final theorem. It
traverses raw types and proof bodies, rejects unsafe or partial dependencies
and unapproved axioms, and checks the standard types, universe arities, and
module origins of `propext`, `Classical.choice`, and `Quot.sound`.

Two compiler-generated partial implementations in `Radial` are accounted
for separately: `LatticeExpr.evalWith._unsafe_rec` and
`LatticeExpr.leaves._unsafe_rec`. Their complete stored and effective records,
including bodies, must agree; their exact parent definitions, module origins,
types, universe parameters, safety, and compiler metadata are checked. No
other unsafe or partial project record is permitted. Both implementations
must be absent from the full raw dependency closure of every safe project
declaration and every retained alternate proof. Their operational bodies
are not replayed mathematical proofs or permitted proof dependencies.

Unequal stored records are rejected except for theorem-body variants with
identical types and other declaration fields. Such variants are retained,
their raw dependencies are inspected separately, and any dependency back to
their original theorem name is rejected. After replaying the complete
effective dependency closure and all additional variant dependencies, each
retained body is independently kernel-checked under a fresh name. Neither
the type nor the proof body is replaced. This avoids treating a same-named
theorem already present in the environment as verification of another body.

Negative controls exercise hidden axioms, missing dependencies, altered
standard axiom interfaces, unsafe and partial declarations, operational-record
classification and forbidden reachability, expression
traversal, changed theorem records, circular variants, and invalid proofs.
In particular, the kernel must reject an invalid alternate body even after
a valid theorem with its original name has been replayed. The verification
programs are not imported by the mathematical proof.

`lake build` is incremental. An independent source-only project build
additionally requires a fresh output directory whose search path excludes
previous project artifacts. Reusing pinned dependency packages in such a
build does not rebuild Lean or Mathlib from source. Empty-kernel replay
checks the dependency declarations with the installed Lean kernel; it is
not verification by a second kernel implementation.

## Relation to the manuscript

The whole-space function, five-piece cover, continuity, and exclusion of
arbitrary-degree polynomial lattice expressions match the manuscript.
Some intermediate arguments use different formulations:

- The formal finite-sign theorem concerns homogeneous tests of degrees one
  and two at a fixed radial scale. This suffices for the final theorem; it
  does not assert the manuscript's stronger inhomogeneous degree-at-most-two
  intermediate statement with a selectable radial scale.
- The formal quadratic-kernel classification uses exact coefficient
  equations rather than accepting the companion program's matrix ranks.
- The formal radial argument takes ordinary real limits after clamping the
  normalized leaves, rather than using extended-real limits.

Thus the final counterexample is formalized, but not every intermediate
displayed assertion in the manuscript is exported as a Lean theorem.

## Trust and review status

The mathematical sources use ordinary Lean proofs and kernel-checked finite
decisions, without new axioms, placeholders, or native-decision shortcuts.
Successful checks still depend on Lean and its runtime. Agreement between
the definitions and the manuscript requires semantic review in addition
to compilation and dependency checking.

Human expert review of the proof remains ongoing. No completed human
endorsement, globally minimal dimension, or resolution of PB(3) is asserted.
