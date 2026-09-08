import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-! An explicit smooth square root for real two-by-two matrices near the identity. -/

namespace PBCounterexample.MatrixSquareRoot2

open Matrix
open scoped Topology Matrix.Norms.Elementwise

noncomputable section

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def root (M : Mat) : Mat :=
  (Real.sqrt (M.trace + 2 * Real.sqrt M.det))⁻¹ •
    (M + Real.sqrt M.det • 1)

theorem numerator_square (M : Mat) (s : ℝ) (hs : s^2 = M.det) :
    (M + s • 1) * (M + s • 1) = (M.trace + 2*s) • M := by
  simp only [Matrix.det_fin_two] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.one_apply] <;>
    nlinarith [hs]

theorem root_mul_self (M : Mat) (hdet : 0 ≤ M.det)
    (htrace : 0 < M.trace + 2 * Real.sqrt M.det) : root M * root M = M := by
  have hs := Real.sq_sqrt hdet
  have hd := Real.sq_sqrt htrace.le
  have hd0 : Real.sqrt (M.trace + 2 * Real.sqrt M.det) ≠ 0 :=
    (Real.sqrt_pos.mpr htrace).ne'
  unfold root
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    numerator_square M (Real.sqrt M.det) hs, smul_smul]
  have he : (Real.sqrt (M.trace + 2 * Real.sqrt M.det))⁻¹ *
      (Real.sqrt (M.trace + 2 * Real.sqrt M.det))⁻¹ *
      (M.trace + 2 * Real.sqrt M.det) = 1 := by
    calc
      _ = (Real.sqrt (M.trace + 2 * Real.sqrt M.det))⁻¹ *
          (Real.sqrt (M.trace + 2 * Real.sqrt M.det))⁻¹ *
          (Real.sqrt (M.trace + 2 * Real.sqrt M.det))^2 := by rw [hd]
      _ = 1 := by field_simp
  rw [he, one_smul]

theorem root_isSymm (M : Mat) (hM : M.IsSymm) : (root M).IsSymm := by
  change (root M)ᵀ = root M
  simp only [root, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one]
  rw [show Mᵀ = M from hM]

theorem root_transpose_mul_self (M : Mat) (hM : M.IsSymm)
    (hdet : 0 ≤ M.det) (htrace : 0 < M.trace + 2 * Real.sqrt M.det) :
    (root M)ᵀ * root M = M := by
  rw [show (root M)ᵀ = root M from root_isSymm M hM]
  exact root_mul_self M hdet htrace

@[simp] theorem root_one : root (1 : Mat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [root, Matrix.trace, Matrix.diag, Fin.sum_univ_succ,
      Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply]

theorem root_contDiffAt {n : WithTop ℕ∞} (M : Mat) (hdet : M.det ≠ 0)
    (htrace : 0 < M.trace + 2 * Real.sqrt M.det) : ContDiffAt ℝ n root M := by
  have hdetfun : ContDiff ℝ n (fun A : Mat => A.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have htracefun : ContDiff ℝ n (fun A : Mat => A.trace) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
    fun_prop
  have hs : ContDiffAt ℝ n (fun A : Mat => Real.sqrt A.det) M :=
    hdetfun.contDiffAt.sqrt hdet
  have ht : ContDiffAt ℝ n (fun A : Mat => Real.sqrt (A.trace + 2 * Real.sqrt A.det)) M :=
    (htracefun.contDiffAt.add (contDiffAt_const.mul hs)).sqrt htrace.ne'
  exact (ht.inv (Real.sqrt_pos.mpr htrace).ne').smul
    (contDiffAt_id.add (hs.smul contDiffAt_const))

theorem root_contDiffAt_one {n : WithTop ℕ∞} : ContDiffAt ℝ n root (1 : Mat) := by
  apply root_contDiffAt
  · simp
  · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

end

end PBCounterexample.MatrixSquareRoot2
