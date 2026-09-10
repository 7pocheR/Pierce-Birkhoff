import PBCounterexample.Function
import PBCounterexample.OrbitGeometry

/-!
# Explicit perturbations of the rank-two orbit

The two choices of sign have identical matrix products. Their limits are the
same orbit point, and their first determinants have opposite signs.
-/

namespace PBCounterexample.Perturbation

open Matrix Filter Topology
open OrbitGeometry

def DX (η t : ℝ) : Mat := diagonal ![1, 1, t ^ 2, t ^ 2, t, η * t]

def DY (η t : ℝ) : Mat := diagonal ![t ^ 2, t ^ 2, 1, 1, t, η * t]

def matrixPath (U V : Matˣ) (η t : ℝ) : Pair := action U V (DX η t, DY η t)

def pointPath (U V : Matˣ) (η t : ℝ) : Function.Point :=
  Function.ofMatrices (matrixPath U V η t).1 (matrixPath U V η t).2

@[simp] theorem DX_zero (η : ℝ) : DX η 0 = D := by
  simp [DX, D]

@[simp] theorem DY_zero (η : ℝ) : DY η 0 = E := by
  simp [DY, E]

@[simp] theorem matrixPath_zero (U V : Matˣ) (η : ℝ) :
    matrixPath U V η 0 = action U V (D, E) := by
  simp [matrixPath]

@[simp] theorem pointPath_zero (U V : Matˣ) (η : ℝ) :
    pointPath U V η 0 =
      Function.ofMatrices (action U V (D, E)).1 (action U V (D, E)).2 := by
  simp [pointPath]

theorem continuous_DX (η : ℝ) : Continuous (DX η) := by
  unfold DX
  fun_prop

theorem continuous_DY (η : ℝ) : Continuous (DY η) := by
  unfold DY
  fun_prop

theorem continuous_matrixPath (U V : Matˣ) (η : ℝ) : Continuous (matrixPath U V η) :=
  (continuous_action U V).comp ((continuous_DX η).prodMk (continuous_DY η))

theorem continuous_ofMatrices :
    Continuous (fun z : Pair => Function.ofMatrices z.1 z.2) := by
  apply continuous_pi
  intro c
  rcases c with ⟨b, i, j⟩
  cases b <;> simp only [Function.ofMatrices, Bool.false_eq_true, ↓reduceIte]
  · fun_prop
  · fun_prop

theorem continuous_pointPath (U V : Matˣ) (η : ℝ) : Continuous (pointPath U V η) :=
  continuous_ofMatrices.comp (continuous_matrixPath U V η)

theorem pointPath_tendsto_zero (U V : Matˣ) (η : ℝ) :
    Tendsto (pointPath U V η) (𝓝 (0 : ℝ))
      (𝓝 (Function.ofMatrices (action U V (D, E)).1 (action U V (D, E)).2)) := by
  simpa using (continuous_pointPath U V η).tendsto 0

theorem pointPath_tendsto_zero_right (U V : Matˣ) (η : ℝ) :
    Tendsto (pointPath U V η) (𝓝[>] (0 : ℝ))
      (𝓝 (Function.ofMatrices (action U V (D, E)).1 (action U V (D, E)).2)) :=
  (pointPath_tendsto_zero U V η).mono_left nhdsWithin_le_nhds

theorem DX_mul_DY (η t : ℝ) (hη : η ^ 2 = 1) : DX η t * DY η t = t ^ 2 • (1 : Mat) := by
  rw [DX, DY, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply, hη] <;>
    nlinarith [hη]

theorem DY_mul_DX (η t : ℝ) (hη : η ^ 2 = 1) : DY η t * DX η t = t ^ 2 • (1 : Mat) := by
  rw [DY, DX, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply, hη] <;>
    nlinarith [hη]

theorem matrixPath_XY (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    (matrixPath U V η t).1 * (matrixPath U V η t).2 = t ^ 2 • (1 : Mat) := by
  change (↑U * DX η t * ↑(V⁻¹)) * (↑V * DY η t * ↑(U⁻¹)) = _
  calc
    _ = ↑U * (DX η t * DY η t) * ↑(U⁻¹) := by simp [Matrix.mul_assoc]
    _ = t ^ 2 • (1 : Mat) := by
      rw [DX_mul_DY η t hη]
      simp [Matrix.mul_smul, Matrix.smul_mul]

theorem matrixPath_YX (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    (matrixPath U V η t).2 * (matrixPath U V η t).1 = t ^ 2 • (1 : Mat) := by
  change (↑V * DY η t * ↑(U⁻¹)) * (↑U * DX η t * ↑(V⁻¹)) = _
  calc
    _ = ↑V * (DY η t * DX η t) * ↑(V⁻¹) := by simp [Matrix.mul_assoc]
    _ = t ^ 2 • (1 : Mat) := by
      rw [DY_mul_DX η t hη]
      simp [Matrix.mul_smul, Matrix.smul_mul]

theorem pointPath_XY (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    Function.X (pointPath U V η t) * Function.Y (pointPath U V η t) =
      t ^ 2 • (1 : Mat) := by
  simpa only [pointPath, Function.X_ofMatrices, Function.Y_ofMatrices] using
    matrixPath_XY U V η t hη

theorem pointPath_YX (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    Function.Y (pointPath U V η t) * Function.X (pointPath U V η t) =
      t ^ 2 • (1 : Mat) := by
  simpa only [pointPath, Function.X_ofMatrices, Function.Y_ofMatrices] using
    matrixPath_YX U V η t hη

theorem det_DX (η t : ℝ) : (DX η t).det = η * t ^ 6 := by
  simp [DX, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem det_DY (η t : ℝ) : (DY η t).det = η * t ^ 6 := by
  simp [DY, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem determinant_X_pointPath (U V : Matˣ) (η t : ℝ) :
    (Function.X (pointPath U V η t)).det =
      (↑U : Mat).det * (↑(V⁻¹) : Mat).det * η * t ^ 6 := by
  simp only [pointPath, Function.X_ofMatrices, matrixPath, action, Matrix.det_mul, det_DX]
  ring

theorem determinant_Y_pointPath (U V : Matˣ) (η t : ℝ) :
    (Function.Y (pointPath U V η t)).det =
      (↑V : Mat).det * (↑(U⁻¹) : Mat).det * η * t ^ 6 := by
  simp only [pointPath, Function.Y_ofMatrices, matrixPath, action, Matrix.det_mul, det_DY]
  ring

theorem det_inverse_positive (U : Matˣ) (hU : 0 < (↑U : Mat).det) :
    0 < (↑(U⁻¹) : Mat).det := by
  have heq : (↑U : Mat).det * (↑(U⁻¹) : Mat).det = 1 := by
    rw [← Matrix.det_mul]
    simp
  nlinarith

theorem determinant_X_plus_pos (U V : Matˣ)
    (hU : 0 < (↑U : Mat).det) (hV : 0 < (↑V : Mat).det)
    (t : ℝ) (ht : 0 < t) : 0 < (Function.X (pointPath U V 1 t)).det := by
  rw [determinant_X_pointPath]
  exact mul_pos (mul_pos (mul_pos hU (det_inverse_positive V hV)) zero_lt_one) (pow_pos ht 6)

theorem determinant_X_minus_neg (U V : Matˣ)
    (hU : 0 < (↑U : Mat).det) (hV : 0 < (↑V : Mat).det)
    (t : ℝ) (ht : 0 < t) : (Function.X (pointPath U V (-1) t)).det < 0 := by
  rw [determinant_X_pointPath]
  have hp := mul_pos (mul_pos hU (det_inverse_positive V hV)) (pow_pos ht 6)
  nlinarith

theorem q_pointPath (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) (a : Function.Label) :
    Function.q a (pointPath U V η t) = t ^ 2 := by
  rw [Function.q_eq, pointPath_XY U V η t hη]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ↓reduceIte, mul_one]
  have hsum : (∑ j : {j : Function.I // j ≠ a.1},
      Function.sign (a.2 j) * (t ^ 2 * if a.1 = (j : Function.I) then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [Ne.symm j.2]
  rw [hsum, sub_zero]

theorem h_pointPath (U V : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    Function.h (pointPath U V η t) = t ^ 2 := by
  obtain ⟨a, ha⟩ := Function.exists_h_eq_q (pointPath U V η t)
  rw [ha, q_pointPath U V η t hη a]

theorem f_plus (U V : Matˣ)
    (hU : 0 < (↑U : Mat).det) (hV : 0 < (↑V : Mat).det)
    (t : ℝ) (ht : 0 < t) : Function.f (pointPath U V 1 t) = t ^ 2 := by
  have hh := h_pointPath U V 1 t (by norm_num)
  rw [Function.f, ite_eq_left ⟨by rw [hh]; exact pow_pos ht 2,
    determinant_X_plus_pos U V hU hV t ht⟩, hh]

theorem f_minus (U V : Matˣ)
    (hU : 0 < (↑U : Mat).det) (hV : 0 < (↑V : Mat).det)
    (t : ℝ) (ht : 0 < t) : Function.f (pointPath U V (-1) t) = 0 := by
  have hd := determinant_X_minus_neg U V hU hV t ht
  simp [Function.f, not_lt_of_ge (le_of_lt hd)]

theorem f_plus_pos (U V : Matˣ)
    (hU : 0 < (↑U : Mat).det) (hV : 0 < (↑V : Mat).det)
    (t : ℝ) (ht : 0 < t) : 0 < Function.f (pointPath U V 1 t) := by
  rw [f_plus U V hU hV t ht]
  exact pow_pos ht 2

theorem product_functionals_equal (U V : Matˣ) (t : ℝ) (L M : Mat →ₗ[ℝ] ℝ) :
    L (Function.Y (pointPath U V 1 t) * Function.X (pointPath U V 1 t)) +
        M (Function.X (pointPath U V 1 t) * Function.Y (pointPath U V 1 t)) =
      L (Function.Y (pointPath U V (-1) t) * Function.X (pointPath U V (-1) t)) +
        M (Function.X (pointPath U V (-1) t) * Function.Y (pointPath U V (-1) t)) := by
  rw [pointPath_XY U V 1 t (by norm_num), pointPath_YX U V 1 t (by norm_num),
    pointPath_XY U V (-1) t (by norm_num), pointPath_YX U V (-1) t (by norm_num)]

end PBCounterexample.Perturbation
