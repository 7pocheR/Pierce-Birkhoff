import PBCounterexample.SymmetricFunction
import PBCounterexample.SymmetricGeometry

/-!
# Symmetric paths with equal products and opposite determinant signs
-/

namespace PBCounterexample.SymmetricPerturbation

open Matrix Filter Topology
open SymmetricGeometry

def DX (η t : ℝ) : Mat := diagonal ![1, 1, t ^ 2, t ^ 2, η * t]
def DY (η t : ℝ) : Mat := diagonal ![t ^ 2, t ^ 2, 1, 1, η * t]

def matrixPath (U : Matˣ) (η t : ℝ) : Pair := action U (DX η t, DY η t)

def pointPath (U : Matˣ) (η t : ℝ) : SymmetricFunction.Point :=
  SymmetricFunction.ofMatrices (matrixPath U η t).1 (matrixPath U η t).2

@[simp] theorem DX_zero (η : ℝ) : DX η 0 = D := by simp [DX, D]
@[simp] theorem DY_zero (η : ℝ) : DY η 0 = E := by simp [DY, E]

theorem matrixPath_symmetric (U : Matˣ) (η t : ℝ) :
    (matrixPath U η t).1.IsSymm ∧ (matrixPath U η t).2.IsSymm := by
  constructor
  · exact congruence_isSymm _ _ (isSymm_diagonal _)
  · simpa only [matrixPath, action, transpose_transpose] using
      congruence_isSymm (↑(U⁻¹) : Mat)ᵀ (DY η t) (isSymm_diagonal _)

@[simp] theorem X_pointPath (U : Matˣ) (η t : ℝ) :
    SymmetricFunction.X (pointPath U η t) = (matrixPath U η t).1 :=
  SymmetricFunction.X_ofMatrices _ _ (matrixPath_symmetric U η t).1

@[simp] theorem Y_pointPath (U : Matˣ) (η t : ℝ) :
    SymmetricFunction.Y (pointPath U η t) = (matrixPath U η t).2 :=
  SymmetricFunction.Y_ofMatrices _ _ (matrixPath_symmetric U η t).2

@[simp] theorem pointPath_zero (U : Matˣ) (η : ℝ) :
    pointPath U η 0 = SymmetricFunction.ofMatrices (action U (D, E)).1
      (action U (D, E)).2 := by
  simp [pointPath, matrixPath]

theorem continuous_DX (η : ℝ) : Continuous (DX η) := by unfold DX; fun_prop
theorem continuous_DY (η : ℝ) : Continuous (DY η) := by unfold DY; fun_prop

theorem continuous_matrixPath (U : Matˣ) (η : ℝ) : Continuous (matrixPath U η) :=
  (continuous_action U).comp ((continuous_DX η).prodMk (continuous_DY η))

theorem continuous_ofMatrices :
    Continuous (fun z : Pair => SymmetricFunction.ofMatrices z.1 z.2) := by
  apply continuous_pi
  intro c
  rcases c with ⟨b, ij⟩
  cases b <;> simp only [SymmetricFunction.ofMatrices, Bool.false_eq_true, ↓reduceIte]
  · fun_prop
  · fun_prop

theorem continuous_pointPath (U : Matˣ) (η : ℝ) : Continuous (pointPath U η) :=
  continuous_ofMatrices.comp (continuous_matrixPath U η)

theorem pointPath_tendsto_zero_right (U : Matˣ) (η : ℝ) :
    Tendsto (pointPath U η) (𝓝[>] (0 : ℝ))
      (𝓝 (SymmetricFunction.ofMatrices (action U (D, E)).1 (action U (D, E)).2)) := by
  have hh := (continuous_pointPath U η).tendsto 0
  rw [pointPath_zero] at hh
  exact hh.mono_left nhdsWithin_le_nhds

theorem DX_mul_DY (η t : ℝ) (hη : η ^ 2 = 1) : DX η t * DY η t = t ^ 2 • (1 : Mat) := by
  rw [DX, DY, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply, hη] <;>
    nlinarith [hη]

theorem matrixPath_XY (U : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    (matrixPath U η t).1 * (matrixPath U η t).2 = t ^ 2 • (1 : Mat) := by
  change ((U : Mat) * DX η t * (U : Mat)ᵀ) *
    ((↑(U⁻¹) : Mat)ᵀ * DY η t * (↑(U⁻¹) : Mat)) = _
  calc
    _ = (U : Mat) * (DX η t * ((U : Mat)ᵀ * (↑(U⁻¹) : Mat)ᵀ) * DY η t) *
        (↑(U⁻¹) : Mat) := by simp only [Matrix.mul_assoc]
    _ = t ^ 2 • (1 : Mat) := by
      rw [← transpose_mul]
      simp [DX_mul_DY η t hη, Matrix.mul_smul, Matrix.smul_mul]

theorem pointPath_XY (U : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    SymmetricFunction.X (pointPath U η t) * SymmetricFunction.Y (pointPath U η t) =
      t ^ 2 • (1 : Mat) := by
  rw [X_pointPath, Y_pointPath]
  exact matrixPath_XY U η t hη

theorem det_DX (η t : ℝ) : (DX η t).det = η * t ^ 5 := by
  simp [DX, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem determinant_X_pointPath (U : Matˣ) (η t : ℝ) :
    (SymmetricFunction.X (pointPath U η t)).det = (U : Mat).det ^ 2 * η * t ^ 5 := by
  simp only [X_pointPath, matrixPath, action, Matrix.det_mul, Matrix.det_transpose, det_DX]
  ring

theorem determinant_X_plus_pos (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    0 < (SymmetricFunction.X (pointPath U 1 t)).det := by
  rw [determinant_X_pointPath, mul_one]
  exact mul_pos (sq_pos_of_ne_zero (Matrix.isUnit_iff_isUnit_det _ |>.mp U.isUnit).ne_zero)
    (pow_pos ht 5)

theorem determinant_X_minus_neg (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    (SymmetricFunction.X (pointPath U (-1) t)).det < 0 := by
  rw [determinant_X_pointPath]
  have hp := mul_pos
    (sq_pos_of_ne_zero (Matrix.isUnit_iff_isUnit_det _ |>.mp U.isUnit).ne_zero) (pow_pos ht 5)
  nlinarith

theorem h_pointPath (U : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    SymmetricFunction.h (pointPath U η t) = t ^ 2 :=
  SymmetricFunction.h_of_scalar_product _ _ (sq_nonneg t) (pointPath_XY U η t hη)

theorem f_plus (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    SymmetricFunction.f (pointPath U 1 t) = t ^ 2 := by
  have hh := h_pointPath U 1 t (by norm_num)
  change (if 0 < SymmetricFunction.h _ ∧
    0 < MvPolynomial.eval _ SymmetricFunction.determinantPolynomial then
      SymmetricFunction.h _ else 0) = _
  rw [SymmetricFunction.eval_determinantPolynomial,
    if_pos ⟨by rw [hh]; exact pow_pos ht 2, determinant_X_plus_pos U t ht⟩, hh]

theorem f_minus (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    SymmetricFunction.f (pointPath U (-1) t) = 0 := by
  have hd := determinant_X_minus_neg U t ht
  change (if 0 < SymmetricFunction.h _ ∧
    0 < MvPolynomial.eval _ SymmetricFunction.determinantPolynomial then
      SymmetricFunction.h _ else 0) = 0
  rw [SymmetricFunction.eval_determinantPolynomial,
    if_neg (fun h => not_lt_of_ge (le_of_lt hd) h.2)]

theorem f_plus_pos (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    0 < SymmetricFunction.f (pointPath U 1 t) := by
  rw [f_plus U t ht]
  exact pow_pos ht 2

end PBCounterexample.SymmetricPerturbation
