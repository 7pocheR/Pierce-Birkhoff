# Recorded verification of the eight-variable construction

This record describes a completed execution against the released Lean
sources. The raw evidence is retained in [final01](final01/). It is distinct
from instructions for performing a new verification run.

## Statement and source identity

The final theorem is
`PBCounterexample.Quadratic8.whole_space_counterexample` in
[Quadratic8Main.lean](../lean/PBCounterexample/Quadratic8Main.lean).
It concerns a function on all of `Fin 8 → ℝ`, with no graph constraint or
mathematical hypotheses. It asserts continuity, 137 polynomial sign tests
of ordinary total degree at most two with one quadratic label on each
entire sign realization, a cover by 17 closed semialgebraic polynomial
pieces, and absence of any finite polynomial lattice representation.
Representing leaves range over all real polynomials, without degree bounds.

The [source manifest](../lean/verification/source.sha256) has 47 entries.
Its SHA256 is
`eb494b5e11b32911665223d96bc647d22757b4fbe50cfc3f753332575fcd82cc`.
The entire released Lean project, including that manifest, is unchanged
from the accepted source snapshot. The manifest does not cover the outer
README, manuscript, supplementary Python certificate, or this record.

The pins are Lean `v4.34.0-rc1` and Mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`, with transitive dependency
revisions in [lake-manifest.json](../lean/lake-manifest.json).
The returned [manifest](final01/source.sha256),
[bundle check](final01/bundle-manifest-check.txt), and source checks
[before](final01/source-before.txt) and [after](final01/source-after.txt)
identify the checked files.

## Completed execution

The [build record](final01/fresh-build-logs/build.json) records commands,
compiler identity, source hashes, artifact hashes, and successful exit codes
for all 35 project modules: 34 mathematical modules and the import wrapper.
The build started with an empty project artifact directory and a search
path excluding prior project artifacts. Each compile invocation used
`--trust=0`. Initial and final source inventories and hashes agree.
The [build log](final01/fresh-build.log) and
[individual module logs](final01/fresh-build-logs/) are retained.
The five new mathematical modules produced no warnings or errors; inherited
modules produced lint and deprecation warnings.

The independently written
[statement checks](../lean/verification/Statements8.lean) and
[literal formula checks](../lean/verification/Formula8.lean) each compiled
with `--trust=0` and exited zero. Their outputs are
[Statements8.log](final01/Statements8.log) and
[Formula8.log](final01/Formula8.log), with matching exit-code files.
These are separate checks, outside the replay's 34-module inventory.

The [trust replay](../lean/verification/TrustReplay8.lean) inventoried 926
safe project roots and traversed 37,598 dependency constants, inspecting
raw declaration types and proof bodies. It then replayed the full closure
into an initially empty Lean kernel environment at trust level zero.
The final eight-variable theorems and their six-dimensional mathematical
dependencies are included. Declaration records were checked after replay.

Only `propext`, `Classical.choice`, and `Quot.sound` were admitted, with
explicit checks of their schemas, universe arities, and module origins.
No `sorry`, added axiom, native-decision axiom, or unsafe or partial
mathematical dependency was accepted. Two compiler-generated operational
records in `Radial` were checked separately and required to be absent from
the mathematical dependency closure and replayed environment.

One alternate stored theorem body differed from its effective body. Its
raw dependencies were checked separately, references to its original name
were rejected, and the exact stored body was kernel-checked under a fresh
name. All 57 raw negative controls and both kernel negative controls
passed; the latter checked rejection of an invalid proof and an invalid
alternate stored proof after the valid original theorem had been replayed.

The complete [TrustReplay8.log](final01/TrustReplay8.log) has SHA256
`831652683dbbc4ec7e9d3fbbb120d6b980c14951feeb02116df9fa7fc84f11d4`.
Its [exit code](final01/TrustReplay8.exit-code), the
[overall exit code](final01/exit-code), and the authoritative worker exit
code are all zero. The exact task script, worker log, and worker exit code
are in [worker](final01/worker/); execution identity is in
[execution.txt](final01/execution.txt).

## Reproduction and trust scope

With the pinned toolchain and dependency artifacts, run the checks described
in the [Lean README](../lean/README.md). Its `verify.sh` checks the source
manifest before and after a Lake build, statement/formula checks, and trust
replay. A Lake build can be incremental, so this script alone does not
recreate the fresh source build recorded above.

The stronger [fresh build driver](../lean/verification/build_fresh.py)
requires a source-only project, an initially empty project artifact
directory, and pinned dependency artifacts staged outside the project.
It rejects existing `.olean` files anywhere under the source project,
including ordinary cached packages. `LEAN_SYSROOT` must identify the pinned
toolchain, and `LEAN_PATH` must list the empty project output first, followed
by external dependency libraries with no old `PBCounterexample` artifacts.
As written, it requires Linux's `lib/lean/libleanshared.so`. It builds project
sources but does not prepare dependencies or run the separate verification
programs. The recorded worker script shows the executed setup; its Slurm
identifiers and absolute paths are historical, not portable prerequisites.

The project sources were freshly compiled. Lean and Mathlib were not
rebuilt from source: existing pinned toolchain and external library artifacts
were used, and relevant dependency declarations were replayed. Replay used
the same pinned Lean kernel and runtime, not a second implementation.
Classical choice is included explicitly among the admitted standard axioms.
Formal verification of the declarations, mathematical source review, and
human expert review are distinct. This record does not assert a completed
human expert review.
