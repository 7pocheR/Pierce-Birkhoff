import PBCounterexample.Gram7PathData

/-! Local smoothness of the explicit signed matrix correction. -/

noncomputable section

namespace PBCounterexample.Gram7

open Matrix Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem pathMatrix_contDiffAt_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    {k : ℕ∞ω} {a : E} {A : E → Matrix m n ℝ} {B : E → Matrix n r ℝ}
    (hA : ContDiffAt ℝ k A a) (hB : ContDiffAt ℝ k B a) :
    ContDiffAt ℝ k (fun p => A p * B p) a := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ k (fun p => ∑ l, A p i l * B p l j) a
  exact ContDiffAt.sum fun l _ =>
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hA i)) l).mul
      ((contDiffAt_pi.mp (contDiffAt_pi.mp hB l)) j)

theorem pathMatrix_contDiffAt_transpose
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : Type*} [Fintype m] [Fintype n]
    {k : ℕ∞ω} {a : E} {A : E → Matrix m n ℝ}
    (hA : ContDiffAt ℝ k A a) : ContDiffAt ℝ k (fun p => (A p)ᵀ) a := by
  exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA j)) i

theorem pathMatrix_contDiffAt_det_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ∞ω} {a : E} {A : E → Matrix Row Row ℝ}
    (hA : ContDiffAt ℝ k A a) : ContDiffAt ℝ k (fun p => (A p).det) a := by
  have h (i j : Row) := (contDiffAt_pi.mp (contDiffAt_pi.mp hA i)) j
  simpa only [Matrix.det_fin_two] using ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))

theorem pathMatrix_contDiffAt_inv_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ∞ω} {a : E} {A : E → Matrix Row Row ℝ}
    (hA : ContDiffAt ℝ k A a) (hdet : (A a).det ≠ 0) :
    ContDiffAt ℝ k (fun p => (A p)⁻¹) a := by
  have hd : ContDiffAt ℝ k (fun p => ((A p).det)⁻¹) a :=
    (pathMatrix_contDiffAt_det_two hA).inv hdet
  have hadj : ContDiffAt ℝ k (fun p => (A p).adjugate) a := by
    have h (i j : Row) := (contDiffAt_pi.mp (contDiffAt_pi.mp hA i)) j
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.adjugate_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply] <;> fun_prop
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact hd.smul hadj

theorem chartRotation_contDiff : ContDiff ℝ ω chartRotation := by
  have hd : ContDiff ℝ ω
      (fun p : ChartParameter => rotationDenominator (p.2 0) (p.2 1) (p.2 2)) := by
    unfold rotationDenominator
    fun_prop
  have hT : ContDiff ℝ ω
      (fun p : ChartParameter => rotationNumerator (p.2 0) (p.2 1) (p.2 2)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [rotationNumerator, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply] <;> fun_prop
  exact (hd.inv fun p => (rotationDenominator_pos _ _ _).ne').smul hT

theorem scaledBPrime_contDiff (ρ : ℝ) : ContDiff ℝ ω (scaledBPrime ρ) := by
  have hB : ContDiff ℝ ω (fun p => ambientB (chart p)) := by
    exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j =>
      contDiff_pi.mp chart_contDiff (bIndex i j)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact pathMatrix_contDiffAt_mul (hB.contDiffAt.const_smul ρ) contDiffAt_const

theorem pathRowCross_contDiff : ContDiff ℝ ω RectangularGram.rowCross := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [RectangularGram.rowCross, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem pathCrossNormSquared_contDiff : ContDiff ℝ ω RectangularGram.crossNormSquared := by
  unfold RectangularGram.crossNormSquared dotProduct
  exact ContDiff.sum fun i _ =>
    (contDiff_pi.mp pathRowCross_contDiff i).mul (contDiff_pi.mp pathRowCross_contDiff i)

theorem pathUnitNormal_contDiffAt (B : RectangularGram.Mat)
    (hB : 0 < RectangularGram.crossNormSquared B) :
    ContDiffAt ℝ ω RectangularGram.unitNormal B := by
  exact ((pathCrossNormSquared_contDiff.contDiffAt.sqrt hB.ne').inv
    (Real.sqrt_pos.mpr hB).ne').smul pathRowCross_contDiff.contDiffAt

theorem correctionMatrix_contDiffAt (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    ContDiffAt ℝ ω (correctionMatrix ρ t) (0,u) := by
  have hP : ContDiffAt ℝ ω (fun p : ChartParameter => scaledBPrime ρ (t,p.2)) (0,u) :=
    (scaledBPrime_contDiff ρ).contDiffAt.comp (0,u) (contDiffAt_const.prodMk contDiffAt_snd)
  have hG : ContDiffAt ℝ ω
      (fun p : ChartParameter => RectangularGram.rowGram (scaledBPrime ρ (t,p.2))) (0,u) :=
    pathMatrix_contDiffAt_mul hP (pathMatrix_contDiffAt_transpose hP)
  have hd : (RectangularGram.rowGram (scaledBPrime ρ (t,u))).det ≠ 0 := by
    rw [RectangularGram.rowGram_det]
    exact hB.ne'
  exact contDiffAt_const.sub ((contDiffAt_fst.pow 2).smul
    (pathMatrix_contDiffAt_inv_two hG hd))

theorem correctionRoot_contDiffAt (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    ContDiffAt ℝ ω (correctionRoot ρ t) (0,u) := by
  apply ContDiffAt.comp (0,u) _ (correctionMatrix_contDiffAt ρ t u hB)
  simpa only [correctionMatrix_zero] using
    (MatrixSquareRoot2.root_contDiffAt_one (n := ω))

theorem correctedAmbient_contDiffAt (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    ContDiffAt ℝ ω (correctedAmbient ρ t) (0,u) := by
  have hP : ContDiffAt ℝ ω (fun p : ChartParameter => scaledBPrime ρ (t,p.2)) (0,u) :=
    (scaledBPrime_contDiff ρ).contDiffAt.comp (0,u) (contDiffAt_const.prodMk contDiffAt_snd)
  have hO : ContDiffAt ℝ ω (fun p : ChartParameter => chartRotation (t,p.2)) (0,u) :=
    chartRotation_contDiff.contDiffAt.comp (0,u) (contDiffAt_const.prodMk contDiffAt_snd)
  have hn : ContDiffAt ℝ ω
      (fun p : ChartParameter => RectangularGram.unitNormal (scaledBPrime ρ (t,p.2))) (0,u) :=
    ContDiffAt.fun_comp (g := RectangularGram.unitNormal) (0,u)
      (pathUnitNormal_contDiffAt (scaledBPrime ρ (t,u)) hB) hP
  have hstack : ContDiffAt ℝ ω
      (fun p : ChartParameter => RectangularGram.stacked (scaledBPrime ρ (t,p.2)) p.1)
      (0,u) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_pi.mp hP 0
    · exact contDiffAt_pi.mp hP 1
    · exact contDiffAt_fst.smul hn
  have hA : ContDiffAt ℝ ω (correctedA ρ t) (0,u) :=
    pathMatrix_contDiffAt_mul (pathMatrix_contDiffAt_mul hO hstack) contDiffAt_const
  have hBB : ContDiffAt ℝ ω (correctedB ρ t) (0,u) :=
    pathMatrix_contDiffAt_mul
      (pathMatrix_contDiffAt_mul (correctionRoot_contDiffAt ρ t u hB) hP) contDiffAt_const
  have hAi (i j : Index) := contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j
  have hBi (i : Row) (j : Index) := contDiffAt_pi.mp (contDiffAt_pi.mp hBB i) j
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp only [correctedAmbient, packMatrices, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop

theorem correction_conditions_eventually (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    ∀ᶠ p : ChartParameter in 𝓝 (0,u),
      0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,p.2)) ∧
      0 < (correctionMatrix ρ t p).det ∧
      0 < (correctionMatrix ρ t p).trace + 2 * Real.sqrt (correctionMatrix ρ t p).det := by
  have hP : Continuous (fun p : ChartParameter => scaledBPrime ρ (t,p.2)) :=
    (scaledBPrime_contDiff ρ).continuous.comp (continuous_const.prodMk continuous_snd)
  have hcross := (pathCrossNormSquared_contDiff.continuous.comp hP).continuousAt (x := (0,u))
  have hM := (correctionMatrix_contDiffAt ρ t u hB).continuousAt
  have hd := (pathMatrix_contDiffAt_det_two
    (correctionMatrix_contDiffAt ρ t u hB)).continuousAt
  have htr : ContinuousAt (fun p => (correctionMatrix ρ t p).trace) (0,u) := by
    have htrace : Continuous (fun M : Matrix Row Row ℝ => M.trace) := by
      unfold Matrix.trace Matrix.diag
      fun_prop
    exact htrace.continuousAt.comp hM
  have hp := hcross.eventually (lt_mem_nhds hB)
  have hdp := hd.eventually (lt_mem_nhds (by simp : (0 : ℝ) < (correctionMatrix ρ t (0,u)).det))
  have ht := (htr.add (continuousAt_const.mul hd.sqrt)).eventually
    (lt_mem_nhds (by norm_num [correctionMatrix_zero, Matrix.trace, Matrix.diag,
      Fin.sum_univ_succ] : (0 : ℝ) < (correctionMatrix ρ t (0,u)).trace +
        2 * Real.sqrt (correctionMatrix ρ t (0,u)).det))
  exact hp.and (hdp.and ht)

end PBCounterexample.Gram7
