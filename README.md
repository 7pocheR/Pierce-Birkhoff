# Pierce–Birkhoff conjecture is false

**Zehua Lai, Lek-Heng Lim, Junyu Ren**

## Main paper

**[Read the paper (PDF)](paper.pdf)** · [LaTeX source](paper.tex)

We give an explicit 30-dimensional counterexample to the Pierce–Birkhoff
conjecture, a classical problem in real algebraic geometry with roots in
Birkhoff and Pierce's 1956 work [1]. The function is continuous and piecewise
quadratic on a finite semialgebraic partition, but has no finite maximum/minimum
representation using polynomials of arbitrary degrees.

The paper presents the conceptually simplest construction. **Its proof has
undergone careful human expert checking and is formalized in Lean.**
Section 5 describes our multi-agent, multi-model setup using GPT and Claude.

## Constructions and Lean formalizations

Each folder contains its manuscript, a separate Lean project, and verification
instructions.

- [n=30_d=5_k=2](n=30_d=5_k=2/): the construction in the main paper.
- [n=5_d=4_k=3](n=5_d=4_k=3/): five variables, a quartic partition, and cubic pieces.
- [n=6_d=3_k=2](n=6_d=3_k=2/): six variables, a cubic partition, and quadratic pieces.
- [n=7_d=3_k=2](n=7_d=3_k=2/): seven variables, a cubic partition, and quadratic pieces.
- [n=8_d=2_k=2](n=8_d=2_k=2/): eight variables, a quadratic partition, and quadratic pieces.
- [n=72_d=6_k=2](n=72_d=6_k=2/): the original construction.

The folder convention is `n=<n>_d=<d>_k=<k>`:

- `n` is the number of independent real variables. Each function is defined
  on the whole space `ℝⁿ`.
- `d` is the maximum ordinary total degree of the polynomial tests defining
  the displayed partition.
- `k` is the maximum ordinary total degree of the polynomial pieces of the
  spline. It denotes polynomial degree, not an order of differentiability.

These are the parameters of the constructions presented here. In particular,
`d` does not assert the minimum degree obtainable by repartitioning the same
function. Neither `d` nor `k` restricts the degrees of polynomials in a proposed
maximum/minimum representation: those degrees are arbitrary.

For the five earlier constructions, let `qᵢ` be the displayed nonzero labels
and `D` the determinant used to select the positive region. A full sign
partition uses `D`, every `qᵢ`, and every pairwise difference `qᵢ − qⱼ`.
Their signs determine whether the function is zero and otherwise which label
is minimal. One polynomial therefore agrees with the function on each entire
sign realization, including its disconnected components and all zero signs.
The determinant degrees are respectively 4, 3, 3, 5, and 6 in dimensions
5, 6, 7, 30, and 72. The five-variable labels are cubic; the others are
quadratic. Each construction's README gives the degree justification.

The eight-variable construction replaces the cubic determinant test by a
quadratic orientation polynomial using two independent cofactor coordinates.
Its Lean theorem supplies 137 quadratic sign tests and one quadratic label on
each entire sign realization, together with a cover by 17 closed semialgebraic
polynomial pieces. It gives a negative answer to the question for quadratic
partitions, with unrestricted degrees in competing polynomial representations.

Human expert review of the 5D, 6D, and 7D proofs is ongoing. No claim of
completed human expert review is made for the 8D proof. No claim of minimum
possible dimension is made. The former folders `5d`, `6d`, `7d`, `30d`, and
`72d` have been renamed according to the convention above; the existing
dimensional branches retain their published versions.

To compile the main paper, run `latexmk -pdf paper.tex` from the repository
root. The bibliography and figure are included in `assets/`. Run formal
checks from the relevant `n=<n>_d=<d>_k=<k>/lean` directory following its README.

## Reference

[1] Garrett Birkhoff and R. S. Pierce, *Lattice-ordered rings*,
Anais da Academia Brasileira de Ciências **28** (1956), 41–69.
For the history and later formulation, see
[Lucas, Madden, Schaub, and Spivakovsky, Section 1](https://arxiv.org/pdf/math/0601671).
