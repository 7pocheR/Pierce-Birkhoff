import PBCounterexample.Gram7Chart
import PBCounterexample.ImplicitError
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp

/-!
# Real implicit family in the seven-variable Gram chart

The free parameter is C₁₁ + 1. The seven unknowns are ordered
k₀, k₁, k₂, t₀, t₁, C₀₁, C₁₀, and C₀₀ is fixed at one.
Only rows one through seven are used in the implicit equation.
-/

noncomputable section

namespace PBCounterexample.Gram7

open Filter Asymptotics
open scoped Matrix Topology ContDiff

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev ChartUnknown := Fin 7 → ℝ
abbrev ChartParameter := ℝ × ChartUnknown

def chartBase : ChartUnknown := 0

def chart (p : ChartParameter) : Ambient :=
  phi (p.2 0) (p.2 1) (p.2 2) (p.2 3) (p.2 4) 1 (p.2 5) (p.2 6) (-1+p.1)

def chartSystem (p : ChartParameter) : ChartUnknown := activeConstraints (chart p)

@[simp] theorem chart_base : chart (0, chartBase) =
    ![1,0,0,0,-1,0,0,0,0,1,0,0,0,-1,0] := by
  simpa [chart, chartBase] using (phi_base (R := ℝ))

@[simp] theorem chartSystem_base : chartSystem (0, chartBase) = 0 := by
  simp only [chartSystem, chart_base]
  ext i
  fin_cases i <;>
    norm_num [activeConstraints, constraints, constraintsMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val, Fin.succ]

theorem chart_contDiff : ContDiff ℝ ω chart := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply] <;> fun_prop

def activeConstraintsL : Ambient →L[ℝ] ChartUnknown :=
  (constraintsMatrix.submatrix Fin.succ id).mulVecLin.toContinuousLinearMap

@[simp] theorem activeConstraintsL_apply (a : Ambient) :
    activeConstraintsL a = activeConstraints a := rfl

theorem chartSystem_contDiff : ContDiff ℝ ω chartSystem :=
  activeConstraintsL.contDiff.comp chart_contDiff

def ambientChartDerivative : ChartParameter →L[ℝ] Ambient where
  toFun p := ![0, 2*p.2 2+p.2 5, p.2 3, 2*p.2 2+p.2 6, p.1, -p.2 4,
    -2*p.2 1, -2*p.2 0, 0, 0, p.2 5, p.2 3, p.2 6, p.1, -p.2 4]
  map_add' p q := by ext i; fin_cases i <;> simp [Matrix.cons_val, Fin.succ] <;> ring
  map_smul' r p := by ext i; fin_cases i <;> simp [Matrix.cons_val, Fin.succ] <;> ring
  cont := by fun_prop

theorem chart_hasFDerivAt :
    HasFDerivAt chart ambientChartDerivative (0, chartBase) := by
  have h0 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨0, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h1 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨1, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h2 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨2, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h3 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨3, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h4 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨4, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h5 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨5, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h6 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨6, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h7 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨7, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h8 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨8, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h9 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨9, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h10 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨10, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h11 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨11, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h12 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨12, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h13 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨13, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  have h14 := (show HasFDerivAt (𝕜 := ℝ)
      (fun p : ChartParameter => chart p (⟨14, by decide⟩ : Fin 15)) _ (0, chartBase) by
    simp only [chart, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, phiA_apply, phiB_apply,
      rotationNumerator, rotationDenominator, chartCV, Matrix.of_apply, pow_two]
    fun_prop)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · apply h0.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h1.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h2.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h3.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h4.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h5.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h6.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h7.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h8.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h9.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h10.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h11.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h12.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h13.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!
  · apply h14.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    norm_num [ambientChartDerivative, chartBase, Matrix.cons_val, Fin.succ] <;> ring!

def chartBaseDerivative : ChartParameter →L[ℝ] ChartUnknown :=
  activeConstraintsL.comp ambientChartDerivative

theorem chartSystem_hasFDerivAt :
    HasFDerivAt chartSystem chartBaseDerivative (0, chartBase) :=
  activeConstraintsL.hasFDerivAt.comp (0, chartBase) chart_hasFDerivAt

def baseJacobian : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, 0, 1260, -326, -490, -3, 815;
     0, -210, 0, 46, -35, 38, 25;
     0, 0, 180, -38, -10, 81, -55;
     0, 0, 0, 1, -1, 0, -1;
     -126, 0, 0, 23, -14, -30, -5;
     0, 0, 0, 66, 0, -17, -25;
     0, 0, 0, 4, -70, -53, 25]

def baseMinorFour (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a,b,c,d; 1,-1,0,-1; 66,0,-17,-25; 4,-70,-53,25]
theorem baseMinorFour_submatrix_det (a b c d : ℝ) (j : Fin 4) :
    ((baseMinorFour a b c d).submatrix Fin.succ j.succAbove).det = ![2940,1680,4620,-4620] j := by
  fin_cases j
  · have hm : (baseMinorFour a b c d).submatrix Fin.succ (⟨0, by decide⟩ : Fin 4).succAbove =
        !![-1,0,-1; 0,-17,-25; -70,-53,25] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hm]
    norm_num [Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.succ]
  · have hm : (baseMinorFour a b c d).submatrix Fin.succ (⟨1, by decide⟩ : Fin 4).succAbove =
        !![1,0,-1; 66,-17,-25; 4,-53,25] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hm]
    norm_num [Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.succ]
  · have hm : (baseMinorFour a b c d).submatrix Fin.succ (⟨2, by decide⟩ : Fin 4).succAbove =
        !![1,-1,-1; 66,0,-25; 4,-70,25] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hm]
    norm_num [Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.succ]
  · have hm : (baseMinorFour a b c d).submatrix Fin.succ (⟨3, by decide⟩ : Fin 4).succAbove =
        !![1,-1,0; 66,0,-17; 4,-70,-53] := by
      ext i k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hm]
    norm_num [Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.succ]
theorem baseMinorFour_det (a b c d : ℝ) :
    (baseMinorFour a b c d).det = 2940*a-1680*b+4620*c+4620*d := by
  rw [Matrix.det_succ_row_zero]
  have he : (fun j : Fin 4 => (-1 : ℝ)^(j : ℕ) * baseMinorFour a b c d 0 j *
      ((baseMinorFour a b c d).submatrix Fin.succ j.succAbove).det) =
      ![2940*a, -1680*b, 4620*c, 4620*d] := by
    ext j
    fin_cases j <;> rw [baseMinorFour_submatrix_det] <;>
      norm_num [baseMinorFour, Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Fin.succ] <;> ring!
  rw [he]
  norm_num [Fin.sum_univ_succ]
  ring

def baseMinorSix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1260,-326,-490,-3,815; -210,0,46,-35,38,25;
     0,180,-38,-10,81,-55; 0,0,1,-1,0,-1;
     0,0,66,0,-17,-25; 0,0,4,-70,-53,25]
def baseMinorFive : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1260,-326,-490,-3,815; 180,-38,-10,81,-55;
     0,1,-1,0,-1; 0,66,0,-17,-25; 0,4,-70,-53,25]

theorem baseMinorFive_det : baseMinorFive.det = -619164000 := by
  have hm0 : baseMinorFive.submatrix (⟨0, by decide⟩ : Fin 5).succAbove Fin.succ =
      baseMinorFour (-38) (-10) 81 (-55) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : baseMinorFive.submatrix (⟨1, by decide⟩ : Fin 5).succAbove Fin.succ =
      baseMinorFour (-326) (-490) (-3) 815 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column_zero]
  have he : (fun i : Fin 5 => (-1 : ℝ)^(i : ℕ) * baseMinorFive i 0 *
      (baseMinorFive.submatrix i.succAbove Fin.succ).det) =
      ![1260*(baseMinorFour (-38) (-10) 81 (-55)).det,
        -180*(baseMinorFour (-326) (-490) (-3) 815).det, 0, 0, 0] := by
    ext i
    fin_cases i
    · rw [hm0]
      norm_num [baseMinorFive, Matrix.cons_val, Fin.succ] <;> ring!
    · rw [hm1]
      norm_num [baseMinorFive, Matrix.cons_val, Fin.succ] <;> ring!
    all_goals norm_num [baseMinorFive, Matrix.cons_val, Fin.succ]
  rw [he]
  norm_num [Fin.sum_univ_succ, baseMinorFour_det]

theorem baseMinorSix_det : baseMinorSix.det = -130024440000 := by
  have hm : baseMinorSix.submatrix (⟨1, by decide⟩ : Fin 6).succAbove Fin.succ =
      baseMinorFive := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (⟨1, by decide⟩ : Fin 6)]
  · rw [hm, baseMinorFive_det]
    norm_num [baseMinorSix, Matrix.cons_val, Fin.succ]
  · intro i _ hi
    fin_cases i <;> first | exact (hi rfl).elim |
      norm_num [baseMinorSix, Matrix.cons_val, Fin.succ]
  · simp

theorem baseJacobian_det : baseJacobian.det = 16383079440000 := by
  have hm : baseJacobian.submatrix (⟨4, by decide⟩ : Fin 7).succAbove Fin.succ =
      baseMinorSix := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (⟨4, by decide⟩ : Fin 7)]
  · rw [hm, baseMinorSix_det]
    norm_num [baseJacobian, Matrix.cons_val, Fin.succ]
  · intro i _ hi
    fin_cases i <;> first | exact (hi rfl).elim |
      norm_num [baseJacobian, Matrix.cons_val, Fin.succ]
  · simp

def baseJacobianL : ChartUnknown →L[ℝ] ChartUnknown :=
  baseJacobian.mulVecLin.toContinuousLinearMap

@[simp] theorem baseJacobianL_apply (v : ChartUnknown) :
    baseJacobianL v = baseJacobian *ᵥ v := rfl

theorem chartBaseDerivative_vertical :
    chartBaseDerivative.comp (ContinuousLinearMap.inr ℝ ℝ ChartUnknown) =
      baseJacobianL := by
  ext v i
  fin_cases i <;>
    norm_num [chartBaseDerivative, activeConstraintsL, ambientChartDerivative,
      baseJacobianL, baseJacobian, constraintsMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val, Fin.succ] <;> ring!

theorem chartSystem_vertical_derivative :
    (fderiv ℝ chartSystem (0, chartBase)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown) = baseJacobianL := by
  rw [chartSystem_hasFDerivAt.fderiv, chartBaseDerivative_vertical]

theorem baseJacobianL_isInvertible : baseJacobianL.IsInvertible := by
  have hdet : IsUnit baseJacobian.det := by rw [baseJacobian_det]; norm_num
  let g : ChartUnknown →L[ℝ] ChartUnknown :=
    baseJacobian⁻¹.mulVecLin.toContinuousLinearMap
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := g)
  · ext v i
    change (baseJacobian *ᵥ (baseJacobian⁻¹ *ᵥ v)) i = v i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · ext v i
    change (baseJacobian⁻¹ *ᵥ (baseJacobian *ᵥ v)) i = v i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem baseJacobianL_inverse_apply (v : ChartUnknown) :
    baseJacobianL.inverse v = baseJacobian⁻¹ *ᵥ v := by
  apply baseJacobianL_isInvertible.injective
  rw [baseJacobianL_isInvertible.self_apply_inverse, baseJacobianL_apply,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv, Matrix.one_mulVec]
  rw [baseJacobian_det]
  norm_num

theorem chartSystem_vertical_isInvertible :
    ((fderiv ℝ chartSystem (0, chartBase)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible := by
  rw [chartSystem_vertical_derivative]
  exact baseJacobianL_isInvertible

def implicitUnknown : ℝ → ChartUnknown :=
  chartSystem_contDiff.contDiffAt.implicitFunction (by simp : (ω : ℕ∞ω) ≠ 0)
    chartSystem_vertical_isInvertible

@[simp] theorem implicitUnknown_zero : implicitUnknown 0 = chartBase :=
  chartSystem_contDiff.contDiffAt.implicitFunction_apply_self _ _

theorem implicitUnknown_contDiffAt : ContDiffAt ℝ ω implicitUnknown 0 :=
  chartSystem_contDiff.contDiffAt.contDiffAt_implicitFunction _ _

theorem implicitUnknown_tendsto : Tendsto implicitUnknown (𝓝 0) (𝓝 chartBase) := by
  simpa using implicitUnknown_contDiffAt.continuousAt.tendsto

theorem implicitUnknown_solves :
    ∀ᶠ t in 𝓝 (0 : ℝ), chartSystem (t, implicitUnknown t) = 0 := by
  simpa only [chartSystem_base, implicitUnknown] using
    chartSystem_contDiff.contDiffAt.eventually_apply_implicitFunction
      (by simp : (ω : ℕ∞ω) ≠ 0) chartSystem_vertical_isInvertible

def chartCMatrix (p : ChartParameter) : Matrix Row Row ℝ :=
  !![1, p.2 5; p.2 6, -1+p.1]

theorem chartCMatrix_det_continuous : Continuous (fun p => (chartCMatrix p).det) := by
  simp only [chartCMatrix, Matrix.det_fin_two, Matrix.cons_val, Fin.succ]
  fun_prop

@[simp] theorem chartCMatrix_det_base : (chartCMatrix (0, chartBase)).det = -1 := by
  norm_num [chartCMatrix, chartBase, Matrix.det_fin_two]

theorem chart_omittedFactor_continuous : Continuous (fun p => omittedFactor (chart p)) := by
  have hc (i : Fin 15) : Continuous (fun p => chart p i) :=
    (continuous_pi_iff.mp chart_contDiff.continuous) i
  unfold omittedFactor ambient coordinates Matrix.mulVec dotProduct
  fun_prop

@[simp] theorem chart_omittedFactor_base : omittedFactor (chart (0, chartBase)) = 2 := by
  have hc : constraints (chart (0, chartBase)) = 0 := by
    rw [chart_base]
    ext i
    fin_cases i <;> norm_num [constraints, constraintsMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val, Fin.succ]
  have hz := congrFun hc (0 : Fin 8)
  rw [constraints_zero_row] at hz
  have hf : chart (0, chartBase) 0 = 1 := by rw [chart_base]; rfl
  unfold omittedFactor omittedDefect at *
  norm_num only [Pi.zero_apply] at hz
  linarith!

theorem chart_trace_zero (p : ChartParameter) : ambientTrace (chart p) = 0 := by
  have h := ambient_phi_gram_zero (p.2 0) (p.2 1) (p.2 2)
    (p.2 3) (p.2 4) 1 (p.2 5) (p.2 6) (-1+p.1)
  simp only [ambientTrace, chart, h, Matrix.zero_apply, add_zero, sub_zero]

theorem implicitUnknown_omittedFactor_pos :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < omittedFactor (chart (t, implicitUnknown t)) := by
  have h := (chart_omittedFactor_continuous.continuousAt
    (x := (0, chartBase))).tendsto.comp (tendsto_id.prodMk_nhds implicitUnknown_tendsto)
  rw [chart_omittedFactor_base] at h
  exact h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 2))

theorem implicitUnknown_cdet_neg :
    ∀ᶠ t in 𝓝 (0 : ℝ), (chartCMatrix (t, implicitUnknown t)).det < 0 := by
  have h := (chartCMatrix_det_continuous.continuousAt
    (x := (0, chartBase))).tendsto.comp (tendsto_id.prodMk_nhds implicitUnknown_tendsto)
  rw [chartCMatrix_det_base] at h
  exact h.eventually (gt_mem_nhds (by norm_num : (-1 : ℝ) < 0))

theorem eventually_chartSystem_vertical_isInvertible :
    ∀ᶠ p in 𝓝 (0, chartBase),
      ((fderiv ℝ chartSystem p).comp
        (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible := by
  have hc : Continuous (fun p : ChartParameter =>
      (fderiv ℝ chartSystem p).comp (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)) :=
    (chartSystem_contDiff.continuous_fderiv (by simp)).clm_comp continuous_const
  have hb : IsUnit baseJacobianL :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr baseJacobianL_isInvertible.bijective
  have hn := (hc.continuousAt (x := (0, chartBase))).tendsto
  rw [chartSystem_vertical_derivative] at hn
  have he := hn.eventually (Units.isOpen.mem_nhds hb)
  filter_upwards [he] with p hp
  obtain ⟨e, he⟩ := hp
  exact ⟨ContinuousLinearEquiv.ofUnit e, he⟩

theorem implicitUnknown_vertical_isInvertible :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ((fderiv ℝ chartSystem (t, implicitUnknown t)).comp
        (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible :=
  (tendsto_id.prodMk_nhds implicitUnknown_tendsto).eventually
    eventually_chartSystem_vertical_isInvertible

def implicitChart (t : ℝ) : Ambient := chart (t, implicitUnknown t)

theorem implicitChart_contDiffAt : ContDiffAt ℝ ω implicitChart 0 :=
  chart_contDiff.contDiffAt.comp 0 (contDiffAt_id.prodMk implicitUnknown_contDiffAt)

@[simp] theorem implicitChart_zero : implicitChart 0 =
    ![1,0,0,0,-1,0,0,0,0,1,0,0,0,-1,0] := by
  simp [implicitChart]

theorem implicitChart_gram_zero (t : ℝ) : ambientGram (implicitChart t) = 0 :=
  ambient_phi_gram_zero _ _ _ _ _ _ _ _ _

theorem implicitChart_constraints :
    ∀ᶠ t in 𝓝 (0 : ℝ), constraints (implicitChart t) = 0 := by
  filter_upwards [implicitUnknown_solves, implicitUnknown_omittedFactor_pos] with t ht hp
  exact constraints_eq_zero_of_active_trace _ ht (chart_trace_zero _) (ne_of_gt hp)

theorem implicitChart_rank_two :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (ambientA (implicitChart t)).rank = 2 ∧ (ambientB (implicitChart t)).rank = 2 := by
  filter_upwards [implicitUnknown_cdet_neg] with t ht
  have hC : 1*(-1+t) - implicitUnknown t 5 * implicitUnknown t 6 ≠ 0 := by
    simpa [chartCMatrix, Matrix.det_fin_two] using (ne_of_lt ht)
  constructor
  · simpa [implicitChart, chart] using phiA_rank_two
      (implicitUnknown t 0) (implicitUnknown t 1) (implicitUnknown t 2)
      (implicitUnknown t 3) (implicitUnknown t 4) 1
      (implicitUnknown t 5) (implicitUnknown t 6) (-1+t) hC
  · simpa [implicitChart, chart] using phiB_rank_two
      (implicitUnknown t 0) (implicitUnknown t 1) (implicitUnknown t 2)
      (implicitUnknown t 3) (implicitUnknown t 4) 1
      (implicitUnknown t 5) (implicitUnknown t 6) (-1+t) hC

theorem implicitUnknown_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ ∞ implicitUnknown (Metric.ball 0 δ) ∧
      ∀ t ∈ Metric.ball (0 : ℝ) δ,
        constraints (implicitChart t) = 0 ∧
        0 < omittedFactor (implicitChart t) ∧
        (chartCMatrix (t, implicitUnknown t)).det < 0 ∧
        ((fderiv ℝ chartSystem (t, implicitUnknown t)).comp
          (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible := by
  have hs := implicitUnknown_contDiffAt.eventually (by simp : (ω : ℕ∞ω) ≠ ∞)
  have hall := implicitChart_constraints.and (implicitUnknown_omittedFactor_pos.and
    (implicitUnknown_cdet_neg.and (implicitUnknown_vertical_isInvertible.and hs)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro t ht
    exact ((hball t ht).2.2.2.2.of_le (by simp)).contDiffWithinAt
  · intro t ht
    exact ⟨(hball t ht).1, (hball t ht).2.1, (hball t ht).2.2.1,
      (hball t ht).2.2.2.1⟩

def baseCurve (t : ℝ) : Coord := coordinates (implicitChart t)

theorem baseCurve_contDiffAt : ContDiffAt ℝ ω baseCurve 0 := by
  apply contDiffAt_pi.mpr
  intro i
  exact (contDiffAt_pi.mp implicitChart_contDiffAt) (negativeIndex i)

@[simp] theorem baseCurve_zero : baseCurve 0 = ![0,0,0,1,0,0,-1] := by
  ext i
  fin_cases i <;> norm_num [baseCurve, implicitChart_zero, coordinates,
    negativeIndex, Matrix.cons_val, Fin.succ] <;> rfl

theorem ambient_baseCurve :
    ∀ᶠ t in 𝓝 (0 : ℝ), ambient (baseCurve t) = implicitChart t := by
  filter_upwards [implicitChart_constraints] with t ht
  exact ambient_coordinates_of_constraints _ ht

theorem baseCurve_gram_zero :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (aMatrix (baseCurve t))ᵀ * aMatrix (baseCurve t) -
        (bMatrix (baseCurve t))ᵀ * bMatrix (baseCurve t) = 0 := by
  filter_upwards [ambient_baseCurve] with t ht
  simpa [aMatrix, bMatrix, ht, ambientGram] using implicitChart_gram_zero t

def normalizedChartSystem (p : ChartParameter) : ChartUnknown :=
  baseJacobianL.inverse (chartSystem p)

theorem normalizedChartSystem_eq (p : ChartParameter) :
    normalizedChartSystem p = baseJacobian⁻¹ *ᵥ activeConstraints (chart p) :=
  baseJacobianL_inverse_apply _

theorem normalizedChartSystem_hasStrictFDerivAt :
    HasStrictFDerivAt normalizedChartSystem
      (baseJacobianL.inverse.comp chartBaseDerivative) (0, chartBase) := by
  apply baseJacobianL.inverse.hasStrictFDerivAt.comp
  convert chartSystem_contDiff.contDiffAt.hasStrictFDerivAt (by simp : (ω : ℕ∞ω) ≠ 0)
    using 1
  exact chartSystem_hasFDerivAt.fderiv.symm

theorem normalizedChartSystem_vertical (v : ChartUnknown) :
    (baseJacobianL.inverse.comp chartBaseDerivative) (0, v) = v := by
  have h := congrArg (fun f : ChartUnknown →L[ℝ] ChartUnknown => f v)
    chartBaseDerivative_vertical
  change chartBaseDerivative (0, v) = baseJacobianL v at h
  simp only [ContinuousLinearMap.comp_apply, h]
  exact baseJacobianL_isInvertible.inverse_apply_self v

theorem implicitUnknown_error_le_twice_normalized_residual
    {a : ℝ → ChartUnknown} (ha : Tendsto a (𝓝 0) (𝓝 chartBase)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ‖a t - implicitUnknown t‖ ≤
      2 * ‖normalizedChartSystem (t, a t)‖ := by
  apply eventually_implicit_error_le_twice_residual
    normalizedChartSystem_hasStrictFDerivAt normalizedChartSystem_vertical
    tendsto_id ha implicitUnknown_tendsto
  filter_upwards [implicitUnknown_solves] with t ht
  simp [normalizedChartSystem, ht]

theorem implicitUnknown_error_isBigO_normalized_residual
    {a : ℝ → ChartUnknown} (ha : Tendsto a (𝓝 0) (𝓝 chartBase)) :
    (fun t => a t - implicitUnknown t) =O[𝓝 0]
      (fun t => normalizedChartSystem (t, a t)) :=
  IsBigO.of_bound 2 (implicitUnknown_error_le_twice_normalized_residual ha)

theorem implicitUnknown_error_isBigO_of_residual
    {a : ℝ → ChartUnknown} (ha : Tendsto a (𝓝 0) (𝓝 chartBase))
    {N : ℕ} (hres : (fun t => chartSystem (t, a t)) =O[𝓝 0] (fun t : ℝ => t^N)) :
    (fun t => a t - implicitUnknown t) =O[𝓝 0] (fun t : ℝ => t^N) := by
  exact (implicitUnknown_error_isBigO_normalized_residual ha).trans
    ((baseJacobianL.inverse.isBigO_comp (fun t => chartSystem (t, a t)) (𝓝 0)).trans hres)

/-- The residual-order hypothesis must be proved for the chosen polynomial
approximation; the conclusion concerns the actual real implicit solution. -/
theorem polynomialApproximation_error_isBigO
    (a : Fin 7 → Polynomial ℝ)
    (hbase : (fun i => (a i).eval 0) = chartBase)
    (N : ℕ)
    (hres : (fun t => chartSystem (t, fun i => (a i).eval t)) =O[𝓝 0]
      (fun t : ℝ => t^N)) :
    (fun t => (fun i => (a i).eval t) - implicitUnknown t) =O[𝓝 0]
      (fun t : ℝ => t^N) := by
  have hc : Continuous (fun t : ℝ => fun i => (a i).eval t) :=
    continuous_pi fun i => (a i).continuous
  apply implicitUnknown_error_isBigO_of_residual _ hres
  simpa only [hbase] using (hc.continuousAt (x := 0)).tendsto

/-- A separately established residual order is preserved after applying a
continuously differentiable function of the chart parameters. -/
theorem chartFunctionApproximation_error_isBigO
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : ChartParameter → Y) (hF : ContDiffAt ℝ 1 F (0, chartBase))
    {a : ℝ → ChartUnknown} (ha : Tendsto a (𝓝 0) (𝓝 chartBase))
    {N : ℕ}
    (hres : (fun t => chartSystem (t, a t)) =O[𝓝 0] (fun t : ℝ => t^N)) :
    (fun t => F (t, a t) - F (t, implicitUnknown t)) =O[𝓝 0]
      (fun t : ℝ => t^N) := by
  have h := (hF.hasStrictFDerivAt (by norm_num)).isBigO_sub.comp_tendsto
    ((tendsto_id.prodMk_nhds ha).prodMk_nhds
      (tendsto_id.prodMk_nhds implicitUnknown_tendsto))
  have hb : (fun t => F (t, a t) - F (t, implicitUnknown t)) =O[𝓝 0]
      (fun t => a t - implicitUnknown t) := by
    simpa [Asymptotics.IsBigO_def, Asymptotics.IsBigOWith_def, Prod.norm_def] using h
  exact hb.trans (implicitUnknown_error_isBigO_of_residual ha hres)

theorem implicitChartApproximation_error_isBigO
    {a : ℝ → ChartUnknown} (ha : Tendsto a (𝓝 0) (𝓝 chartBase))
    {N : ℕ}
    (hres : (fun t => chartSystem (t, a t)) =O[𝓝 0] (fun t : ℝ => t^N)) :
    (fun t => chart (t, a t) - implicitChart t) =O[𝓝 0] (fun t : ℝ => t^N) :=
  chartFunctionApproximation_error_isBigO chart
    (chart_contDiff.contDiffAt.of_le (by simp)) ha hres

end PBCounterexample.Gram7
