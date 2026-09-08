import PBCounterexample.Gram7Implicit
import PBCounterexample.Gram7Function
import PBCounterexample.RectangularGram

/-! The fixed Gram target and the signed correction of the seven-variable chart. -/

noncomputable section

namespace PBCounterexample.Gram7

open Matrix Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def targetR : Matrix Index Index ℝ := !![1,1/4,0; 1/4,1,0; 0,0,2]

def targetS : Matrix Index Index ℝ :=
  !![1,1/4,0; 0,Real.sqrt 15/4,0; 0,0,Real.sqrt 2]

theorem targetS_transpose_mul : targetSᵀ * targetS = targetR := by
  have h15 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [targetS, targetR, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> nlinarith

theorem targetS_det : targetS.det = Real.sqrt 15 * Real.sqrt 2 / 4 := by
  norm_num [targetS, Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.succ]
  ring

theorem targetS_det_pos : 0 < targetS.det := by
  rw [targetS_det]
  positivity

theorem targetS_inverse : targetS⁻¹ =
    !![1,-(Real.sqrt 15)⁻¹,0; 0,4*(Real.sqrt 15)⁻¹,0;
       0,0,(Real.sqrt 2)⁻¹] := by
  apply Matrix.inv_eq_right_inv
  have h15 : Real.sqrt 15 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [targetS, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      h15, h2] <;> field_simp <;> ring

theorem targetS_inverse_mul : targetS⁻¹ * targetS = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr targetS_det_pos.ne')

theorem targetR_trace : targetR 0 0 + targetR 1 1 - targetR 2 2 = 0 := by
  norm_num [targetR, Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.succ]

theorem target_laplacian :
    GramSelection.simplex * targetR * GramSelection.simplexᵀ =
      !![21/2,-3/2,-17/2,-1/2; -3/2,21/2,-17/2,-1/2;
         -17/2,-17/2,41/2,-7/2; -1/2,-1/2,-7/2,9/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [GramSelection.simplex, targetR, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ]

theorem target_label_ge_half (a : Label) :
    (1 : ℝ)/2 ≤ -(GramSelection.simplex * targetR * GramSelection.simplexᵀ)
      a.val.val.1 a.val.val.2 := by
  rw [target_laplacian]
  rcases a with ⟨⟨⟨i,j⟩,hij⟩,hne⟩
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]

theorem eval_qPolynomial_of_target {z : Coord} {s : ℝ}
    (hg : gramMatrix z = s • targetR) (a : Label) :
    MvPolynomial.eval z (qPolynomial a) =
      s * (-(GramSelection.simplex * targetR * GramSelection.simplexᵀ)
        a.val.val.1 a.val.val.2) := by
  simp only [qPolynomial, allQuadratics, GramSelection.eval_qPolynomial,
    GramSelection.laplacian, gramSelection_gram_eq, hg, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem minimum_of_target {z : Coord} (e : ℝ)
    (hg : gramMatrix z = e^2 • targetR) : minimum z = e^2/2 := by
  apply le_antisymm
  · have h := PolynomialSelection.minimum_le qPolynomial z
      (⟨edge03, by decide⟩ : Label)
    rw [eval_qPolynomial_of_target hg, target_laplacian] at h
    change PolynomialSelection.minimum qPolynomial z ≤ e^2 * (-((-1 : ℝ)/2)) at h
    have hh : (-((-1 : ℝ)/2)) = (1 : ℝ)/2 := by norm_num
    rw [hh] at h
    simpa only [minimum, div_eq_mul_inv, one_mul] using h
  · apply (PolynomialSelection.le_minimum_iff qPolynomial z _).mpr
    intro a
    rw [eval_qPolynomial_of_target hg]
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (target_label_ge_half a) (sq_nonneg e)

theorem path_f_eq_of_target {z : Coord} (e : ℝ) (he : e ≠ 0)
    (hg : gramMatrix z = e^2 • targetR) (hd : 0 < (aMatrix z).det) :
    f z = e^2/2 := by
  have hm : PolynomialSelection.minimum qPolynomial z = e^2/2 := minimum_of_target e hg
  have hd' : 0 < MvPolynomial.eval z determinantPolynomial := by
    simpa [determinantPolynomial] using hd
  change PolynomialSelection.f qPolynomial determinantPolynomial z = _
  rw [PolynomialSelection.f, hm, if_pos ⟨div_pos (sq_pos_of_ne_zero he) (by norm_num), hd'⟩]

theorem path_f_zero_of_det_nonpos {z : Coord} (hd : (aMatrix z).det ≤ 0) : f z = 0 := by
  have hd' : MvPolynomial.eval z determinantPolynomial ≤ 0 := by
    simpa [determinantPolynomial] using hd
  simp [f, PolynomialSelection.f, not_lt_of_ge hd']

def packMatrices (A : Matrix Index Index ℝ) (B : Matrix Row Index ℝ) : Ambient :=
  ![A 0 0,A 0 1,A 0 2,A 1 0,A 1 1,A 1 2,A 2 0,A 2 1,A 2 2,
    B 0 0,B 0 1,B 0 2,B 1 0,B 1 1,B 1 2]

@[simp] theorem ambientA_pack (A : Matrix Index Index ℝ) (B : Matrix Row Index ℝ) :
    ambientA (packMatrices A B) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem ambientB_pack (A : Matrix Index Index ℝ) (B : Matrix Row Index ℝ) :
    ambientB (packMatrices A B) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem pack_ambient (a : Ambient) : packMatrices (ambientA a) (ambientB a) = a := by
  ext i
  fin_cases i <;> rfl

theorem packMatrices_smul (r : ℝ) (A : Matrix Index Index ℝ) (B : Matrix Row Index ℝ) :
    packMatrices (r • A) (r • B) = r • packMatrices A B := by
  ext i
  fin_cases i <;> rfl

def chartRotation (p : ChartParameter) : Matrix Index Index ℝ :=
  (rotationDenominator (p.2 0) (p.2 1) (p.2 2))⁻¹ •
    rotationNumerator (p.2 0) (p.2 1) (p.2 2)

theorem chartRotation_orthogonal (p : ChartParameter) :
    (chartRotation p)ᵀ * chartRotation p = 1 := by
  have hd := (rotationDenominator_pos (p.2 0) (p.2 1) (p.2 2)).ne'
  simp only [chartRotation, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, rotationNumerator_transpose_mul]
  have h : (rotationDenominator (p.2 0) (p.2 1) (p.2 2))⁻¹ *
      (rotationDenominator (p.2 0) (p.2 1) (p.2 2))⁻¹ *
      (rotationDenominator (p.2 0) (p.2 1) (p.2 2))^2 = 1 := by field_simp
  rw [← mul_assoc, h, one_smul]

theorem chartRotation_det (p : ChartParameter) : (chartRotation p).det = 1 := by
  have hd := (rotationDenominator_pos (p.2 0) (p.2 1) (p.2 2)).ne'
  rw [chartRotation, Matrix.det_smul, rotationNumerator_det]
  simp only [Fintype.card_fin]
  field_simp

theorem stacked_zero_mul (B : RectangularGram.Mat) (S : Matrix Index Index ℝ) :
    RectangularGram.stacked B 0 * S = RectangularGram.stacked (B * S) 0 := by
  ext i j
  change (∑ k : Index, RectangularGram.stacked B 0 i k * S k j) =
    RectangularGram.stacked (B * S) 0 i j
  fin_cases i <;>
    simp [RectangularGram.stacked, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ]

theorem stacked_zero_smul (r : ℝ) (B : RectangularGram.Mat) :
    RectangularGram.stacked (r • B) 0 = r • RectangularGram.stacked B 0 := by
  ext i j
  change RectangularGram.stacked (r • B) 0 i j = r * RectangularGram.stacked B 0 i j
  fin_cases i <;> simp [RectangularGram.stacked, Matrix.smul_apply,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ]

theorem chartRotation_stacked (p : ChartParameter) :
    chartRotation p * RectangularGram.stacked (ambientB (chart p)) 0 =
      ambientA (chart p) := by
  have he : RectangularGram.stacked (ambientB (chart p)) 0 =
      rotationDenominator (p.2 0) (p.2 1) (p.2 2) •
        chartEmbedding (p.2 3) (p.2 4) 1 (p.2 5) (p.2 6) (-1+p.1) := by
    rw [chart, ambientB_phi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RectangularGram.stacked, phiB_apply, chartCV, chartEmbedding]
  rw [he, chartRotation, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ (rotationDenominator_pos (p.2 0) (p.2 1) (p.2 2)).ne', one_smul]
  exact (ambientA_phi _ _ _ _ _ _ _ _ _).symm

def scaledBPrime (ρ : ℝ) (p : ChartParameter) : RectangularGram.Mat :=
  (ρ • ambientB (chart p)) * targetS⁻¹

theorem scaledBPrime_mul_S (ρ : ℝ) (p : ChartParameter) :
    scaledBPrime ρ p * targetS = ρ • ambientB (chart p) := by
  rw [scaledBPrime, Matrix.mul_assoc, targetS_inverse_mul, Matrix.mul_one]

theorem scaledBPrime_cross_third (ρ : ℝ) (p : ChartParameter) :
    RectangularGram.rowCross (scaledBPrime ρ p) 2 =
      4 * (Real.sqrt 15)⁻¹ * ρ^2 *
        (rotationDenominator (p.2 0) (p.2 1) (p.2 2))^2 * (chartCMatrix p).det := by
  rw [scaledBPrime, targetS_inverse]
  simp only [chart, ambientB_phi]
  norm_num [RectangularGram.rowCross, cross_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, phiB_apply, chartCV, chartCMatrix, Matrix.det_fin_two,
    Matrix.smul_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.succ]
  ring!

theorem scaledBPrime_cross_pos (ρ : ℝ) (hρ : ρ ≠ 0) (p : ChartParameter)
    (hC : (chartCMatrix p).det ≠ 0) :
    0 < RectangularGram.crossNormSquared (scaledBPrime ρ p) := by
  have hn : RectangularGram.rowCross (scaledBPrime ρ p) 2 ≠ 0 := by
    rw [scaledBPrime_cross_third]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne')) (pow_ne_zero _ hρ))
      (pow_ne_zero _ (rotationDenominator_pos (p.2 0) (p.2 1) (p.2 2)).ne')) hC
  have hs := sq_pos_of_ne_zero hn
  have h0 := sq_nonneg (RectangularGram.rowCross (scaledBPrime ρ p) 0)
  have h1 := sq_nonneg (RectangularGram.rowCross (scaledBPrime ρ p) 1)
  unfold RectangularGram.crossNormSquared dotProduct
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  nlinarith!

def correctionMatrix (ρ t : ℝ) (p : ChartParameter) : Matrix Row Row ℝ :=
  1 - p.1^2 • (RectangularGram.rowGram (scaledBPrime ρ (t,p.2)))⁻¹

def correctionRoot (ρ t : ℝ) (p : ChartParameter) : Matrix Row Row ℝ :=
  MatrixSquareRoot2.root (correctionMatrix ρ t p)

def correctedA (ρ t : ℝ) (p : ChartParameter) : Matrix Index Index ℝ :=
  chartRotation (t,p.2) * RectangularGram.stacked (scaledBPrime ρ (t,p.2)) p.1 * targetS

def correctedB (ρ t : ℝ) (p : ChartParameter) : Matrix Row Index ℝ :=
  correctionRoot ρ t p * scaledBPrime ρ (t,p.2) * targetS

def correctedAmbient (ρ t : ℝ) (p : ChartParameter) : Ambient :=
  packMatrices (correctedA ρ t p) (correctedB ρ t p)

@[simp] theorem correctionMatrix_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctionMatrix ρ t (0,u) = 1 := by simp [correctionMatrix]

@[simp] theorem correctionRoot_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctionRoot ρ t (0,u) = 1 := by simp [correctionRoot]

theorem correctedA_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctedA ρ t (0,u) = ρ • ambientA (chart (t,u)) := by
  rw [correctedA, Matrix.mul_assoc, stacked_zero_mul, scaledBPrime_mul_S,
    stacked_zero_smul, Matrix.mul_smul, chartRotation_stacked]

theorem correctedB_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctedB ρ t (0,u) = ρ • ambientB (chart (t,u)) := by
  rw [correctedB, correctionRoot_zero, Matrix.one_mul, scaledBPrime_mul_S]

theorem correctedAmbient_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctedAmbient ρ t (0,u) = ρ • chart (t,u) := by
  rw [correctedAmbient, correctedA_zero, correctedB_zero, packMatrices_smul, pack_ambient]

theorem correctionMatrix_isSymm (ρ t : ℝ) (p : ChartParameter) :
    (correctionMatrix ρ t p).IsSymm := by
  change (correctionMatrix ρ t p)ᵀ = correctionMatrix ρ t p
  simp only [correctionMatrix, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul]
  rw [show ((RectangularGram.rowGram (scaledBPrime ρ (t,p.2)))⁻¹)ᵀ =
      (RectangularGram.rowGram (scaledBPrime ρ (t,p.2)))⁻¹ from
    (RectangularGram.rowGram_isSymm _).inv]

theorem correctedAmbient_gram (ρ t : ℝ) (p : ChartParameter)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,p.2)))
    (hdet : 0 ≤ (correctionMatrix ρ t p).det)
    (htrace : 0 < (correctionMatrix ρ t p).trace +
      2 * Real.sqrt (correctionMatrix ρ t p).det) :
    ambientGram (correctedAmbient ρ t p) = p.1^2 • targetR := by
  simp only [ambientGram, correctedAmbient, ambientA_pack, ambientB_pack,
    correctedA, correctedB]
  have hU : (correctionRoot ρ t p)ᵀ * correctionRoot ρ t p =
      1 - p.1^2 • (RectangularGram.rowGram (scaledBPrime ρ (t,p.2)))⁻¹ :=
    MatrixSquareRoot2.root_transpose_mul_self _ (correctionMatrix_isSymm ρ t p) hdet htrace
  simpa only [targetS_transpose_mul] using
    RectangularGram.corrected_gram _ _ (chartRotation (t,p.2)) targetS
      (correctionRoot ρ t p) hB (chartRotation_orthogonal _) hU

theorem correctedA_det (ρ t : ℝ) (p : ChartParameter)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,p.2))) :
    (correctedA ρ t p).det =
      p.1 * Real.sqrt (RectangularGram.crossNormSquared (scaledBPrime ρ (t,p.2))) *
        targetS.det :=
  RectangularGram.corrected_det _ _ _ _ hB (chartRotation_det _)

end PBCounterexample.Gram7
