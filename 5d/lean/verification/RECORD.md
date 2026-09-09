# Recorded verification

The source and configuration files identified by `source.sha256` completed
a fresh-source build and a full audit on September 8, 2026, on an x86-64 Linux
DSI compute node. The build used Lean `4.34.0-rc1`, commit
`3447a668783dbce1a8fdb97101dd067687b2b418`, and the dependency revisions in the
included `lake-manifest.json`. The sources in this package are byte-identical
to the frozen inputs of that execution.

The completed procedure compiled all 24 implementation modules, the library
wrapper, three independent mathematical modules, and the independent audit
tool into a previously empty project output directory. Every compilation
used `--trust=0 -j 4` and exited zero. The full entry then ran once, also with
`--trust=0 -j 4`, and exited zero. The complete task exited zero. Source and
dependency artifact identities were checked, and foreign import paths were
checked for project-module overrides.

`completed-run/complete-audit.log` is the complete, unedited 2,257-line audit
output, including the final resource report. Its recorded counts are:

- 27 mathematical modules and 932 stored records, distinct project roots,
  and effective project names; zero duplicate records or retained alternate
  stored proof bodies; zero unsafe or partial exemptions.
- 37,358 effective and combined dependency constants, including 8,144
  definitions and 27,262 theorems.
- 13 raw negative or traversal controls and two kernel negative controls.
- Three accepted standard axiom schemas: `propext`, `Classical.choice`, and
  `Quot.sound`; 19 printed final or intermediate theorem types.
- A complete empty-kernel replay of all 37,358 supplied constants, covering
  all 932 project roots.

The full audit reported 80.49 seconds of elapsed time and a peak resident
set of 6,980,416 KiB. The associated build, audit, and task exit-status files
are included unchanged. `build-summary.log` contains the original compilation
and audit boundary lines; it is an excerpt, not the complete task log.

The public `verify.sh` adapts the completed procedure to freshly fetched
official dependencies and independent temporary directories. It preserves
the original Lean sources, build order, exact mathematical module inventory,
and single full audit entry. Its static and lightweight checks do not
constitute another full build: this portable script has not itself completed
an external reproduction run. Such a run will record the identities of its
own pinned dependency artifacts; no byte identity with the original Linux
dependency cache is asserted.
