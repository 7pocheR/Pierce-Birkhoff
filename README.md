# A piecewise quadratic function without a polynomial lattice representation

**Review status:** The proof is currently being checked by our human expert;
that review has not yet been completed.

This repository contains the mathematical manuscript and Lean 4 formalization
of an explicit continuous function on the whole space of two independent
six by six real matrices, identified with real coordinate space of dimension
72. The function has a closed semialgebraic polynomial cover with 193 indexed
regions and homogeneous quadratic labels, but has no finite maximum/minimum
expression using real polynomials of arbitrary degrees.

- [PDF proof](pierce_birkhoff_counterexample.pdf)
- [LaTeX source](pierce_birkhoff_counterexample.tex)
- [Lean project and verification instructions](lean/README.md)
- [Final formal statements](lean/PBCounterexample/Main.lean)

The main Lean theorem is
`PBCounterexample.pierce_birkhoff_counterexample`.
`PBCounterexample.no_finite_max_min_representation` explicitly excludes every
nonempty finite maximum of nonempty finite minima of unrestricted real
multivariate polynomials.

## Scope

The statement concerns the classical whole-space Pierce-Birkhoff conjecture
with a finite closed semialgebraic polynomial cover, as in Conjecture 1.1
and Definition 1.2 of [Wagner (2010)](https://www.numdam.org/item/10.5802/afst.1283.pdf).
The degree bound applies to the polynomial labels, not to every polynomial
defining the partition. The displayed cover also uses a degree-six determinant.

## Reproducing the formal verification

The Lean project pins Lean `v4.34.0-rc1` and mathlib commit
`ffbfefaec67d01d561affd800125a281db8bb7f3`.
Install the pinned toolchain through Elan, enter the `lean` directory, obtain
the dependency artifacts with `lake exe cache get`, and run `bash verify.sh`.
See the [Lean README](lean/README.md) for the exact checks, additional kernel
replay, and their trust assumptions.

Formal verification concerns the exact Lean statements and uses Lean's
standard classical foundations. It is distinct from journal peer review
and from independent verification of the Lean implementation.

## AI assistance

GPT-6 and Claude 5.1 assisted in the development and review of this work.
