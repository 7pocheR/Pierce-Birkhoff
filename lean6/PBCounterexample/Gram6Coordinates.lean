import PBCounterexample.GramSelection

/-!
# Six coordinates for a weighted Gram matrix

The positive part of the bilinear form has diagonal coefficients `1, 1, 3`.
The matrix polynomials below retain that coefficient and the original six
real coordinates.
-/

namespace PBCounterexample.Gram6

open Matrix MvPolynomial
open scoped BigOperators

abbrev Coord := Fin 6 → ℝ
abbrev Index := Fin 3
abbrev Row := Fin 2

noncomputable def aMatrix (w : Coord) : Matrix Index Index ℝ := !![
  w 0, -w 4 + w 5 / 2, -w 1;
  w 1, w 2 + w 3, w 0;
  w 2, w 5 / 2, 0]

noncomputable def bMatrix (w : Coord) : Matrix Row Index ℝ := !![
  w 3, -w 4 / 2 + w 5, -w 4 / 2;
  w 4, 2 * w 2 + w 3 / 2, w 3 / 2]

noncomputable def aPolynomial : Matrix Index Index (MvPolynomial (Fin 6) ℝ) := !![
  X 0, -X 4 + C (1/2) * X 5, -X 1;
  X 1, X 2 + X 3, X 0;
  X 2, C (1/2) * X 5, 0]

noncomputable def bPolynomial : Matrix Row Index (MvPolynomial (Fin 6) ℝ) := !![
  X 3, -(C (1/2) * X 4) + X 5, -(C (1/2) * X 4);
  X 4, C 2 * X 2 + C (1/2) * X 3, C (1/2) * X 3]

@[simp] theorem eval_aPolynomial (w : Coord) :
    aPolynomial.map (eval w) = aMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aPolynomial, aMatrix, Matrix.map_apply] <;> ring

@[simp] theorem eval_bPolynomial (w : Coord) :
    bPolynomial.map (eval w) = bMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bPolynomial, bMatrix, Matrix.map_apply] <;> ring

theorem aPolynomial_homogeneous (i j : Index) :
    (aPolynomial i j).IsHomogeneous 1 := by
  have hX (k : Fin 6) := MvPolynomial.isHomogeneous_X ℝ k
  have hhalf (k : Fin 6) := (hX k).C_mul (1/2 : ℝ)
  fin_cases i <;> fin_cases j
  · exact hX 0
  · exact ((hX 4).neg).add (hhalf 5)
  · exact (hX 1).neg
  · exact hX 1
  · exact (hX 2).add (hX 3)
  · exact hX 0
  · exact hX 2
  · exact hhalf 5
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem bPolynomial_homogeneous (i : Row) (j : Index) :
    (bPolynomial i j).IsHomogeneous 1 := by
  have hX (k : Fin 6) := MvPolynomial.isHomogeneous_X ℝ k
  have hhalf (k : Fin 6) := (hX k).C_mul (1/2 : ℝ)
  fin_cases i <;> fin_cases j
  · exact hX 3
  · exact ((hhalf 4).neg).add (hX 5)
  · exact (hhalf 4).neg
  · exact hX 4
  · exact ((hX 2).C_mul 2).add (hhalf 3)
  · exact hhalf 3

noncomputable def gramMatrix (w : Coord) : Matrix Index Index ℝ := fun i j =>
  aMatrix w 0 i * aMatrix w 0 j + aMatrix w 1 i * aMatrix w 1 j +
    3 * aMatrix w 2 i * aMatrix w 2 j -
    (bMatrix w 0 i * bMatrix w 0 j + bMatrix w 1 i * bMatrix w 1 j)

noncomputable def gramPolynomial : Matrix Index Index (MvPolynomial (Fin 6) ℝ) :=
  fun i j => aPolynomial 0 i * aPolynomial 0 j + aPolynomial 1 i * aPolynomial 1 j +
    C 3 * (aPolynomial 2 i * aPolynomial 2 j) -
    (bPolynomial 0 i * bPolynomial 0 j + bPolynomial 1 i * bPolynomial 1 j)

@[simp] theorem eval_gramPolynomial (w : Coord) (i j : Index) :
    eval w (gramPolynomial i j) = gramMatrix w i j := by
  have ha (r c : Index) : eval w (aPolynomial r c) = aMatrix w r c :=
    congrFun (congrFun (eval_aPolynomial w) r) c
  have hb (r : Row) (c : Index) : eval w (bPolynomial r c) = bMatrix w r c :=
    congrFun (congrFun (eval_bPolynomial w) r) c
  simp [gramPolynomial, gramMatrix, ha, hb, mul_assoc]

theorem gramPolynomial_homogeneous (i j : Index) :
    (gramPolynomial i j).IsHomogeneous 2 := by
  have ha (r : Index) := (aPolynomial_homogeneous r i).mul (aPolynomial_homogeneous r j)
  have hb (r : Row) := (bPolynomial_homogeneous r i).mul (bPolynomial_homogeneous r j)
  exact (((ha 0).add (ha 1)).add ((ha 2).C_mul 3)).sub ((hb 0).add (hb 1))

theorem gramMatrix_symmetric (w : Coord) : (gramMatrix w).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gramMatrix]
  ring

theorem gram_relation (w : Coord) :
    gramMatrix w 0 0 + gramMatrix w 1 1 - gramMatrix w 2 2 = 0 := by
  change (w 0 * w 0 + w 1 * w 1 + 3 * w 2 * w 2 - (w 3 * w 3 + w 4 * w 4)) +
    ((-w 4 + w 5/2) * (-w 4 + w 5/2) + (w 2 + w 3) * (w 2 + w 3) +
      3 * (w 5/2) * (w 5/2) -
      ((-w 4/2 + w 5) * (-w 4/2 + w 5) + (2*w 2 + w 3/2) * (2*w 2 + w 3/2))) -
    ((-w 1) * (-w 1) + w 0 * w 0 + 3 * 0 * 0 -
      ((-w 4/2) * (-w 4/2) + (w 3/2) * (w 3/2))) = 0
  ring

theorem gram_entry02 (w : Coord) : gramMatrix w 0 2 = 0 := by
  change w 0 * (-w 1) + w 1 * w 0 + 3 * w 2 * 0 -
    (w 3 * (-w 4/2) + w 4 * (w 3/2)) = 0
  ring

noncomputable def determinantPolynomial : MvPolynomial (Fin 6) ℝ := aPolynomial.det

@[simp] theorem eval_determinantPolynomial (w : Coord) :
    eval w determinantPolynomial = (aMatrix w).det := by
  rw [determinantPolynomial, ← eval_aPolynomial w]
  exact (eval w).map_det aPolynomial

end PBCounterexample.Gram6
