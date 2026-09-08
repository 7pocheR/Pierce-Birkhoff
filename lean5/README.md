# Five-dimensional Lean formalization

`PBCounterexample.Gram5.whole_space_counterexample` states that the explicitly
defined function `PBCounterexample.Gram5.f` is continuous on all of `ℝ⁵`, has
a finite closed semialgebraic cover with five polynomial labels of degree
at most three, and has no finite expression formed by maxima and minima
of real polynomials. Competing polynomials have arbitrary degree and real
coefficients. `not_finite_sup_inf_polynomials` gives the corresponding explicit
finite supremum–infimum statement.

The library entry is `PBCounterexample.lean`. The main theorem is in
`PBCounterexample/Gram5Main.lean`. The three independent mathematical modules
state the construction and its intermediate claims separately, then bind
those statements to the implementation. Module names are part of the audit's
exact inventory and must be retained.

## Reproduction

Use a clean copy of this directory on Linux with Bash, Git, Python 3, GNU
coreutils, GNU time at `/usr/bin/time`, and `elan` installed. The pinned toolchain
is Lean `v4.34.0-rc1`, commit
`3447a668783dbce1a8fdb97101dd067687b2b418`; Mathlib is pinned to
`ffbfefaec67d01d561affd800125a281db8bb7f3`. All transitive dependency revisions
are fixed in `lake-manifest.json`. Internet access is needed to install the
toolchain, fetch those revisions, and obtain Mathlib's dependency cache.

Run `./verify.sh` from this directory. The same command is in
`verification/reproduce.txt` for copying. Set `PB5_VERIFY_TMPDIR` to an existing
directory when a different temporary filesystem is needed. Dependency caches
require several gigabytes of storage; provide at least 12 GiB of available
memory for the proof build and replay. Download and build times depend on
the machine and network.

The script creates a fresh temporary directory and retains its sources,
dependency checkouts, compiled output, command records, complete logs, and
exit statuses there. It prints that directory when it starts and when it
exits. The release directory must contain no `.lake`, `build`, or compiled
artifacts. Inherited Lean import paths are cleared. The script checks exact
source hashes and dependency revisions, rejects project modules in foreign
import paths, and records dependency artifact inventories and hashes before
and after verification.

All 24 implementation modules, the library wrapper, the three independent
mathematical modules, and the audit tool are compiled in dependency order
with `--trust=0`. The unchanged full entry then invokes `runAudit true` once.
It checks every stored and effective declaration in the 27 mathematical
modules, traverses their dependencies, checks standard axiom schemas and
deliberate negative controls, and replays the complete dependency closure
in an initially empty kernel environment at trust level zero. The raw-only
entry is included for diagnostics; it is not an additional required run.

A successful run has exit status zero, `FULL_VERIFICATION_TASK_EXIT=0`, and
complete `GRAM5_PROJECT_INVENTORY_OK`, `GRAM5_INDEPENDENT_RAW_AUDIT_OK`, and
`GRAM5_INDEPENDENT_EMPTY_KERNEL_REPLAY_OK` records in the retained logs.
`verification/check_audit_log.py` checks required output and counts; inspect
the complete logs as well. The accepted logical axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Lean's kernel and runtime remain part
of the trusted computing base.

The evidence for the completed execution is described separately in
[`verification/RECORD.md`](verification/RECORD.md). It distinguishes that
execution from use of this portable shell script. These formal statements
do not determine the least possible counterexample dimension or establish
universal positive results in dimensions three or four.
