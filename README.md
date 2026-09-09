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

- [30d](30d/): the construction in the main paper, with quadratic pieces.
- [5d](5d/): five-dimensional construction, with cubic pieces.
- [6d](6d/): six-dimensional construction, with quadratic pieces.
- [7d](7d/): seven-dimensional construction, with quadratic pieces.
- [72d](72d/): the original construction, with quadratic pieces.

Human expert review of the 5D, 6D, and 7D proofs is ongoing. No claim of
minimum possible dimension is made. The existing dimensional branches retain
their published versions.

To compile the main paper, run `latexmk -pdf paper.tex` from the repository
root. The bibliography and figure are included in `assets/`. Run formal
checks from the relevant `<dimension>d/lean` directory following its README.

## Reference

[1] Garrett Birkhoff and R. S. Pierce, *Lattice-ordered rings*,
Anais da Academia Brasileira de Ciências **28** (1956), 41–69.
For the history and later formulation, see
[Lucas, Madden, Schaub, and Spivakovsky, Section 1](https://arxiv.org/pdf/math/0601671).
