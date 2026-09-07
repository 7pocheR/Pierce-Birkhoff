import PBCounterexample.MatrixSquareRoot2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Row-space projection identities for a real two-by-three matrix. -/

namespace PBCounterexample.RectangularGram

open Matrix
open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

abbrev Mat := Matrix (Fin 2) (Fin 3) ℝ

def rowGram (B : Mat) : Matrix (Fin 2) (Fin 2) ℝ := B * Bᵀ
def rowCross (B : Mat) : Fin 3 → ℝ := B 0 ⨯₃ B 1
def crossNormSquared (B : Mat) : ℝ := rowCross B ⬝ᵥ rowCross B
def unitNormal (B : Mat) : Fin 3 → ℝ := (Real.sqrt (crossNormSquared B))⁻¹ • rowCross B
def projection (B : Mat) : Matrix (Fin 3) (Fin 3) ℝ := Bᵀ * (rowGram B)⁻¹ * B

theorem rowGram_isSymm (B : Mat) : (rowGram B).IsSymm := by
  change (B * Bᵀ)ᵀ = B * Bᵀ
  simp

theorem rowGram_det (B : Mat) : (rowGram B).det = crossNormSquared B := by
  simp only [rowGram, Matrix.det_fin_two, crossNormSquared, rowCross,
    cross_dot_cross]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]

theorem adjugate_projection_identity (B : Mat) :
    Bᵀ * (rowGram B).adjugate * B + vecMulVec (rowCross B) (rowCross B) =
      crossNormSquared B • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowGram, rowCross, crossNormSquared, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply,
      cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.cons_val,
      Matrix.smul_apply, Matrix.one_apply]
  all_goals ring!

theorem unitNormal_outer (B : Mat) (hB : 0 < crossNormSquared B) :
    vecMulVec (unitNormal B) (unitNormal B) =
      (crossNormSquared B)⁻¹ • vecMulVec (rowCross B) (rowCross B) := by
  have hs := Real.sq_sqrt hB.le
  have hi : (Real.sqrt (crossNormSquared B))⁻¹ * (Real.sqrt (crossNormSquared B))⁻¹ =
      (crossNormSquared B)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← pow_two, hs]
  ext i j
  simp only [unitNormal, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  calc
    _ = ((Real.sqrt (crossNormSquared B))⁻¹ * (Real.sqrt (crossNormSquared B))⁻¹) *
        (rowCross B i * rowCross B j) := by ring
    _ = _ := by rw [hi]

theorem projection_add_normal (B : Mat) (hB : 0 < crossNormSquared B) :
    projection B + vecMulVec (unitNormal B) (unitNormal B) = 1 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => (crossNormSquared B)⁻¹ • A)
    (adjugate_projection_identity B)
  rw [smul_add, smul_smul, inv_mul_cancel₀ hB.ne', one_smul] at h
  rw [unitNormal_outer B hB]
  unfold projection
  rw [Matrix.inv_def, Ring.inverse_eq_inv, rowGram_det,
    Matrix.mul_smul, Matrix.smul_mul]
  exact h

theorem dot_row_unitNormal (B : Mat) (i : Fin 2) : B i ⬝ᵥ unitNormal B = 0 := by
  fin_cases i <;> simp [unitNormal, rowCross, dotProduct_smul]

theorem unitNormal_dot_self (B : Mat) (hB : 0 < crossNormSquared B) :
    unitNormal B ⬝ᵥ unitNormal B = 1 := by
  have hs := Real.sq_sqrt hB.le
  have hi : (Real.sqrt (crossNormSquared B))⁻¹ * (Real.sqrt (crossNormSquared B))⁻¹ =
      (crossNormSquared B)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← pow_two, hs]
  simp only [unitNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← mul_assoc, hi]
  exact inv_mul_cancel₀ hB.ne'

def stacked (B : Mat) (e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![B 0, B 1, e • unitNormal B]

theorem stacked_gram (B : Mat) (e : ℝ) :
    (stacked B e)ᵀ * stacked B e =
      Bᵀ * B + e^2 • vecMulVec (unitNormal B) (unitNormal B) := by
  ext i j
  change (∑ k : Fin 3, stacked B e k i * stacked B e k j) =
    (∑ k : Fin 2, B k i * B k j) + e^2 * (unitNormal B i * unitNormal B j)
  norm_num [stacked, Fin.sum_univ_succ, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
  ring

theorem stacked_det (B : Mat) (e : ℝ) (hB : 0 < crossNormSquared B) :
    (stacked B e).det = e * Real.sqrt (crossNormSquared B) := by
  have hs := Real.sq_sqrt hB.le
  have hn : Real.sqrt (crossNormSquared B) ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
  rw [stacked, ← triple_product_eq_det, triple_product_permutation,
    triple_product_permutation]
  simp only [smul_dotProduct, unitNormal, rowCross, smul_eq_mul]
  change e * ((Real.sqrt (crossNormSquared B))⁻¹ * crossNormSquared B) = _
  congr 1
  calc
    _ = (Real.sqrt (crossNormSquared B))⁻¹ * (Real.sqrt (crossNormSquared B))^2 := by rw [hs]
    _ = _ := by field_simp

/-- The Gram correction preserves a common scalar target before any additional
linear equations are imposed. -/
theorem corrected_gram (B : Mat) (e : ℝ)
    (O S : Matrix (Fin 3) (Fin 3) ℝ) (U : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : 0 < crossNormSquared B) (hO : Oᵀ * O = 1)
    (hU : Uᵀ * U = 1 - e^2 • (rowGram B)⁻¹) :
    (O * stacked B e * S)ᵀ * (O * stacked B e * S) -
        (U * B * S)ᵀ * (U * B * S) = e^2 • (Sᵀ * S) := by
  have hA : (O * stacked B e * S)ᵀ * (O * stacked B e * S) =
      Sᵀ * ((stacked B e)ᵀ * stacked B e) * S := by
    simp only [Matrix.transpose_mul]
    calc
      _ = Sᵀ * (stacked B e)ᵀ * (Oᵀ * O) * stacked B e * S := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hO]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hBB : (U * B * S)ᵀ * (U * B * S) = Sᵀ * (Bᵀ * (Uᵀ * U) * B) * S := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hA, hBB, stacked_gram, hU]
  have hinner : (Bᵀ * B + e^2 • vecMulVec (unitNormal B) (unitNormal B)) -
      Bᵀ * (1 - e^2 • (rowGram B)⁻¹) * B = e^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul]
    change (Bᵀ * B + e^2 • vecMulVec (unitNormal B) (unitNormal B)) -
      (Bᵀ * B - e^2 • projection B) = _
    calc
      _ = e^2 • (projection B + vecMulVec (unitNormal B) (unitNormal B)) := by
        rw [smul_add]
        abel
      _ = _ := by rw [projection_add_normal B hB]
  calc
    _ = Sᵀ * ((Bᵀ * B + e^2 • vecMulVec (unitNormal B) (unitNormal B)) -
        Bᵀ * (1 - e^2 • (rowGram B)⁻¹) * B) * S := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    _ = _ := by rw [hinner]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

theorem corrected_det (B : Mat) (e : ℝ)
    (O S : Matrix (Fin 3) (Fin 3) ℝ) (hB : 0 < crossNormSquared B)
    (hO : O.det = 1) :
    (O * stacked B e * S).det = e * Real.sqrt (crossNormSquared B) * S.det := by
  rw [Matrix.det_mul, Matrix.det_mul, hO, one_mul, stacked_det B e hB]

end

end PBCounterexample.RectangularGram
