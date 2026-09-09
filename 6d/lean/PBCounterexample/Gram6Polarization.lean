import PBCounterexample.Gram6Coordinates

/-! Exact quadratic expansions of the weighted Gram matrix. -/

namespace PBCounterexample.Gram6

open Matrix

theorem aMatrix_add (v w : Coord) : aMatrix (v + w) = aMatrix v + aMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aMatrix, Matrix.add_apply, Pi.add_apply] <;> ring

theorem bMatrix_add (v w : Coord) : bMatrix (v + w) = bMatrix v + bMatrix w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bMatrix, Matrix.add_apply, Pi.add_apply] <;> ring

theorem aMatrix_smul (c : ℝ) (v : Coord) : aMatrix (c • v) = c • aMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aMatrix, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem bMatrix_smul (c : ℝ) (v : Coord) : bMatrix (c • v) = c • bMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bMatrix, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring

noncomputable def gramPolar (v w : Coord) : Matrix Index Index ℝ := fun i j =>
  aMatrix v 0 i * aMatrix w 0 j + aMatrix w 0 i * aMatrix v 0 j +
    aMatrix v 1 i * aMatrix w 1 j + aMatrix w 1 i * aMatrix v 1 j +
    3 * (aMatrix v 2 i * aMatrix w 2 j + aMatrix w 2 i * aMatrix v 2 j) -
    (bMatrix v 0 i * bMatrix w 0 j + bMatrix w 0 i * bMatrix v 0 j +
      bMatrix v 1 i * bMatrix w 1 j + bMatrix w 1 i * bMatrix v 1 j)

theorem gramPolar_comm (v w : Coord) : gramPolar v w = gramPolar w v := by
  ext i j
  simp only [gramPolar]
  ring

theorem gramPolar_add_right (v w z : Coord) :
    gramPolar v (w + z) = gramPolar v w + gramPolar v z := by
  ext i j
  simp only [gramPolar, aMatrix_add, bMatrix_add, Matrix.add_apply]
  ring

theorem gramPolar_smul_right (c : ℝ) (v w : Coord) :
    gramPolar v (c • w) = c • gramPolar v w := by
  ext i j
  simp only [gramPolar, aMatrix_smul, bMatrix_smul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gramPolar_smul_left (c : ℝ) (v w : Coord) :
    gramPolar (c • v) w = c • gramPolar v w := by
  rw [gramPolar_comm, gramPolar_smul_right, gramPolar_comm w v]

theorem gramMatrix_add_smul (v w : Coord) (c : ℝ) :
    gramMatrix (v + c • w) = gramMatrix v + c • gramPolar v w + c^2 • gramMatrix w := by
  ext i j
  simp only [gramMatrix, gramPolar, aMatrix_add, bMatrix_add,
    aMatrix_smul, bMatrix_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gramMatrix_add (v w : Coord) :
    gramMatrix (v + w) = gramMatrix v + gramPolar v w + gramMatrix w := by
  simpa only [one_smul, one_pow] using gramMatrix_add_smul v w 1

theorem gramPolar_self (v : Coord) : gramPolar v v = (2 : ℝ) • gramMatrix v := by
  ext i j
  simp only [gramPolar, gramMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gramMatrix_smul (c : ℝ) (v : Coord) :
    gramMatrix (c • v) = c^2 • gramMatrix v := by
  ext i j
  simp only [gramMatrix, aMatrix_smul, bMatrix_smul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gramPolar_symmetric (v w : Coord) : (gramPolar v w).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gramPolar]
  ring

theorem gramPolar_relation (v w : Coord) :
    gramPolar v w 0 0 + gramPolar v w 1 1 - gramPolar v w 2 2 = 0 := by
  have hv := gram_relation v
  have hw := gram_relation w
  have hvw := gram_relation (v + w)
  rw [gramMatrix_add] at hvw
  simp only [Matrix.add_apply] at hvw
  linarith only [hv, hw, hvw]

theorem gramPolar_entry02 (v w : Coord) : gramPolar v w 0 2 = 0 := by
  have h := gram_entry02 (v + w)
  rw [gramMatrix_add] at h
  simpa only [Matrix.add_apply, gram_entry02, zero_add, add_zero] using h

end PBCounterexample.Gram6
