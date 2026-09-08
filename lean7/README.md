# Seven-variable Lean formalization

This standalone project proves the whole-space seven-variable assertion in
[Gram7Main.lean](PBCounterexample/Gram7Main.lean). The function and closed
cover are defined in [Gram7Function.lean](PBCounterexample/Gram7Function.lean),
using the independent coordinates in
[Gram7Coordinates.lean](PBCounterexample/Gram7Coordinates.lean).

The final theorem has no mathematical hypotheses. It asserts the existence
of a continuous function on `Fin 7 → ℝ` with a six-region finite closed
semialgebraic cover, homogeneous quadratic labels, and no finite polynomial
lattice representation. A separate theorem excludes every nonempty finite
maximum of nonempty finite minima. All auxiliary polynomials have arbitrary
real coefficients and unrestricted degree.

## Build and verification

Install Elan and the toolchain in `lean-toolchain`. In this directory run
`lake exe cache get` to obtain the pinned dependency artifacts, followed by
`bash verify.sh`. Python is not required for the Lean proof. The project
contains 35 mathematical modules and a one-import library wrapper; neither
the build nor the verification imports a higher-dimensional example.

The verification script performs three distinct checks:

1. SHA-256 comparison against the published source manifest, followed by the
   ordinary incremental Lake build.
2. Explicit proposition and definition checks in
   [Statements7.lean](verification/Statements7.lean), including the whole
   domain, the actual selecting formula, unrestricted expression types,
   and standard axiom summaries.
3. Raw dependency inspection and replay into an initially empty Lean kernel
   environment in [TrustReplay7.lean](verification/TrustReplay7.lean).

The last program enumerates every mathematical declaration from the 35
imported project modules, not only the final theorems. It checks stored
declaration types and duplicate bodies, follows raw proof/type dependencies,
rejects unsafe or partial mathematical dependencies and unapproved axioms,
replays the complete closure, and compares all replayed declaration types
and universe parameters. The only permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`; their standard interfaces are checked.

The program additionally tests that the kernel rejects an incorrect proof
of the final theorem and a nonexistent proof dependency. A separate test
checks that an unapproved axiom is identified by the allowlist. These
verification programs are not imported by the mathematical proof.

For these pinned sources the raw closure has 2,699 distinct mathematical
project declarations and 44,978 dependencies. Three compiler-generated
operational recursion implementations are reported separately; none is in
the mathematical dependency closure. The replay is therefore not a check
of every runtime implementation emitted by Lean's compiler.

`lake build` is incremental. A source-only check of the project additionally
requires compiling its mathematical modules into a fresh output directory
whose search path excludes previous project artifacts. Such a check does
not rebuild Lean or Mathlib from their sources. Empty-kernel replay instead
checks the imported dependency declarations with the installed Lean kernel.
Neither operation is verification by a second kernel implementation.

## Trust and review status

The mathematical sources use ordinary Lean proofs and kernel-checked finite
decisions, without new axioms, placeholders or native-decision shortcuts.
Successful checks still depend on the correctness of Lean and its runtime.
Agreement between the definitions and the manuscript requires semantic
review in addition to compiling the declarations.

Human expert review of the proof remains ongoing. No completed human
endorsement, global dimension-minimality result, or PB(3) resolution is
asserted.
