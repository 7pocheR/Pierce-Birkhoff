import PBCounterexample.Gram7PathSmooth

/-! Signed real paths in the fixed seven-dimensional space. -/

noncomputable section

namespace PBCounterexample.Gram7

open Matrix Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def correctedSystem (ρ t : ℝ) (p : ChartParameter) : ChartUnknown :=
  activeConstraints (correctedAmbient ρ t p)

theorem correctedSystem_zero (ρ t : ℝ) (u : ChartUnknown) :
    correctedSystem ρ t (0,u) = ρ • chartSystem (t,u) := by
  rw [correctedSystem, correctedAmbient_zero]
  exact activeConstraintsL.map_smul ρ (chart (t,u))

theorem correctedSystem_contDiffAt (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    ContDiffAt ℝ ω (correctedSystem ρ t) (0,u) :=
  activeConstraintsL.contDiff.contDiffAt.comp (0,u)
    (correctedAmbient_contDiffAt ρ t u hB)

theorem correctedSystem_vertical_derivative (ρ t : ℝ) (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u))) :
    (fderiv ℝ (correctedSystem ρ t) (0,u)).comp
        (ContinuousLinearMap.inr ℝ ℝ ChartUnknown) =
      ρ • (fderiv ℝ chartSystem (t,u)).comp
        (ContinuousLinearMap.inr ℝ ℝ ChartUnknown) := by
  have h₁ := ((correctedSystem_contDiffAt ρ t u hB).differentiableAt
    (by simp : (ω : ℕ∞ω) ≠ 0)).hasFDerivAt.comp u
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) u)
  have h₂ := ((chartSystem_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp u
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t u)).const_smul ρ
  simp only [Function.comp_def, correctedSystem_zero] at h₁
  exact h₁.unique h₂

theorem path_smul_isInvertible (ρ : ℝ) (hρ : ρ ≠ 0)
    (D : ChartUnknown →L[ℝ] ChartUnknown) (hD : D.IsInvertible) :
    (ρ • D).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := ρ⁻¹ • D.inverse)
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_smul, hD.self_apply_inverse, smul_smul, mul_inv_cancel₀ hρ, one_smul,
      inv_mul_cancel₀ hρ, ContinuousLinearMap.id_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_smul, hD.inverse_apply_self, smul_smul, inv_mul_cancel₀ hρ, one_smul,
      mul_inv_cancel₀ hρ, ContinuousLinearMap.id_apply]

theorem correctedSystem_vertical_isInvertible (ρ t : ℝ) (hρ : ρ ≠ 0)
    (u : ChartUnknown)
    (hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u)))
    (hD : ((fderiv ℝ chartSystem (t,u)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible) :
    ((fderiv ℝ (correctedSystem ρ t) (0,u)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible := by
  rw [correctedSystem_vertical_derivative ρ t u hB]
  exact path_smul_isInvertible ρ hρ _ hD

theorem path_coordinates_smul (ρ : ℝ) (a : Ambient) :
    coordinates (ρ • a) = ρ • coordinates a := rfl

theorem path_omittedFactor_smul (ρ : ℝ) (a : Ambient) :
    omittedFactor (ρ • a) = ρ * omittedFactor a := by
  rw [omittedFactor, path_coordinates_smul, ambient_smul]
  change ρ * a 0 + ρ * ambient (coordinates a) 0 = ρ * omittedFactor a
  unfold omittedFactor
  ring

theorem path_omittedFactor_continuous : Continuous omittedFactor := by
  unfold omittedFactor ambient coordinates Matrix.mulVec dotProduct
  fun_prop

theorem path_exists_continuous_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg : ContDiffAt ℝ ω g 0) :
    ∃ x : ℝ → E, Continuous x ∧ x =ᶠ[𝓝 0] g := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hg.eventually (by simp : (ω : ℕ∞ω) ≠ ∞))
  have hgc : ContinuousOn g (Metric.ball 0 δ) :=
    fun y hy => (hball y hy).continuousAt.continuousWithinAt
  let c : ℝ → ℝ := fun e => max (-δ/2) (min (δ/2) e)
  have hc : Continuous c := by unfold c; fun_prop
  have hmem (e : ℝ) : c e ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor
    · exact lt_of_lt_of_le (by linarith : -δ < -δ/2) (le_max_left _ _)
    · have hh : c e ≤ δ/2 := max_le (by linarith) (min_le_left _ _)
      linarith
  refine ⟨g ∘ c, hgc.comp_continuous hc hmem, ?_⟩
  have he : ∀ᶠ e : ℝ in 𝓝 0, e ∈ Metric.ball 0 (δ/2) :=
    Metric.ball_mem_nhds 0 (by linarith)
  filter_upwards [he] with e he
  have hh := abs_lt.mp (show |e| < δ/2 by simpa [Metric.mem_ball, Real.dist_eq] using he)
  have hce : c e = e := by
    dsimp [c]
    rw [min_eq_right (le_of_lt hh.2)]
    apply max_eq_right
    linarith [hh.1]
  simp only [Function.comp_apply, hce]

theorem exists_signed_path_of_local_conditions (t ρ : ℝ) (hρ : 0 < ρ)
    (hsol : chartSystem (t, implicitUnknown t) = 0)
    (hfactor : 0 < omittedFactor (implicitChart t))
    (hC : (chartCMatrix (t, implicitUnknown t)).det < 0)
    (hD : ((fderiv ℝ chartSystem (t, implicitUnknown t)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown)).IsInvertible) :
    ∃ x : ℝ → Coord, Continuous x ∧ x 0 = ρ • baseCurve t ∧
      ∀ᶠ e in 𝓝 (0 : ℝ),
        gramMatrix (x e) = e^2 • targetR ∧
        (0 < e → 0 < (aMatrix (x e)).det ∧ f (x e) = e^2/2) ∧
        (e < 0 → (aMatrix (x e)).det < 0 ∧ f (x e) = 0) := by
  let u := implicitUnknown t
  have hB : 0 < RectangularGram.crossNormSquared (scaledBPrime ρ (t,u)) :=
    scaledBPrime_cross_pos ρ hρ.ne' (t,u) hC.ne
  have hc := correctedSystem_contDiffAt ρ t u hB
  have hi := correctedSystem_vertical_isInvertible ρ t hρ.ne' u hB hD
  let v : ℝ → ChartUnknown := hc.implicitFunction (by simp : (ω : ℕ∞ω) ≠ 0) hi
  have hv0 : v 0 = u := hc.implicitFunction_apply_self _ _
  have hv : ContDiffAt ℝ ω v 0 := hc.contDiffAt_implicitFunction _ _
  have hvlim : Tendsto (fun e => (e,v e)) (𝓝 0) (𝓝 (0,u)) := by
    simpa only [id_eq, hv0] using (contDiffAt_id.prodMk hv).continuousAt.tendsto
  have hs : ∀ᶠ e in 𝓝 (0 : ℝ), correctedSystem ρ t (e,v e) = 0 := by
    have hz : correctedSystem ρ t (0,u) = 0 := by
      rw [correctedSystem_zero, hsol, smul_zero]
    simpa only [hz, v] using hc.eventually_apply_implicitFunction
      (by simp : (ω : ℕ∞ω) ≠ 0) hi
  let a : ℝ → Ambient := fun e => correctedAmbient ρ t (e,v e)
  have ha0 : a 0 = ρ • implicitChart t := by
    simp only [a, hv0, correctedAmbient_zero]
    rfl
  have ha : ContDiffAt ℝ ω a 0 := by
    apply ContDiffAt.fun_comp (g := correctedAmbient ρ t)
      (f := fun e : ℝ => (e,v e)) 0
    · simpa only [hv0] using correctedAmbient_contDiffAt ρ t u hB
    · simpa only [id_eq] using contDiffAt_id.prodMk hv
  have hconds := hvlim.eventually (correction_conditions_eventually ρ t u hB)
  have hgram : ∀ᶠ e in 𝓝 (0 : ℝ), ambientGram (a e) = e^2 • targetR := by
    filter_upwards [hconds] with e he
    exact correctedAmbient_gram ρ t (e,v e) he.1 he.2.1.le he.2.2
  have hfaclim : Tendsto (fun e => omittedFactor (a e)) (𝓝 0)
      (𝓝 (ρ * omittedFactor (implicitChart t))) := by
    simpa only [Function.comp_def, ha0, path_omittedFactor_smul] using
      (path_omittedFactor_continuous.continuousAt.comp ha.continuousAt).tendsto
  have hfac := hfaclim.eventually (lt_mem_nhds (mul_pos hρ hfactor))
  have hfull : ∀ᶠ e in 𝓝 (0 : ℝ), constraints (a e) = 0 := by
    filter_upwards [hs, hgram, hfac] with e he hg hf
    apply constraints_eq_zero_of_active_trace (a e) he _ hf.ne'
    simp only [ambientTrace, hg, Matrix.smul_apply, smul_eq_mul]
    norm_num [targetR, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  let z : ℝ → Coord := fun e => coordinates (a e)
  have hz : ContDiffAt ℝ ω z 0 :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mp ha (negativeIndex i)
  have hz0 : z 0 = ρ • baseCurve t := by
    change coordinates (a 0) = _
    rw [ha0, path_coordinates_smul]
    rfl
  have hamb : ∀ᶠ e in 𝓝 (0 : ℝ), ambient (z e) = a e := by
    filter_upwards [hfull] with e he
    exact ambient_coordinates_of_constraints _ he
  have hzprop : ∀ᶠ e in 𝓝 (0 : ℝ),
      gramMatrix (z e) = e^2 • targetR ∧
      (0 < e → 0 < (aMatrix (z e)).det ∧ f (z e) = e^2/2) ∧
      (e < 0 → (aMatrix (z e)).det < 0 ∧ f (z e) = 0) := by
    filter_upwards [hamb, hgram, hconds] with e he hg hc
    have hgz : gramMatrix (z e) = e^2 • targetR := by
      simpa only [gramMatrix, aMatrix, bMatrix, he, ambientGram] using hg
    have hdet : (aMatrix (z e)).det =
        e * Real.sqrt (RectangularGram.crossNormSquared (scaledBPrime ρ (t,v e))) *
          targetS.det := by
      rw [aMatrix, he]
      simpa only [a, correctedAmbient, ambientA_pack] using
        correctedA_det ρ t (e,v e) hc.1
    have hp : 0 < Real.sqrt (RectangularGram.crossNormSquared (scaledBPrime ρ (t,v e))) :=
      Real.sqrt_pos.mpr hc.1
    refine ⟨hgz, ?_, ?_⟩
    · intro hpos
      have hdpos : 0 < (aMatrix (z e)).det := by
        rw [hdet]
        exact mul_pos (mul_pos hpos hp) targetS_det_pos
      exact ⟨hdpos, path_f_eq_of_target e hpos.ne' hgz hdpos⟩
    · intro hneg
      have hdneg : (aMatrix (z e)).det < 0 := by
        rw [hdet]
        exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hp) targetS_det_pos
      exact ⟨hdneg, path_f_zero_of_det_nonpos hdneg.le⟩
  obtain ⟨x,hx,hxeq⟩ := path_exists_continuous_extension z hz
  refine ⟨x,hx,hxeq.eq_of_nhds.trans hz0, ?_⟩
  filter_upwards [hxeq, hzprop] with e he hp
  simpa only [he] using hp

theorem signed_paths_eventually :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ ρ : ℝ, 0 < ρ →
      ∃ x : ℝ → Coord, Continuous x ∧ x 0 = ρ • baseCurve t ∧
        ∀ᶠ e in 𝓝 (0 : ℝ),
          gramMatrix (x e) = e^2 • targetR ∧
          (0 < e → 0 < (aMatrix (x e)).det ∧ f (x e) = e^2/2) ∧
          (e < 0 → (aMatrix (x e)).det < 0 ∧ f (x e) = 0) := by
  filter_upwards [implicitUnknown_solves, implicitUnknown_omittedFactor_pos,
    implicitUnknown_cdet_neg, implicitUnknown_vertical_isInvertible] with t hs hf hC hD
  intro ρ hρ
  exact exists_signed_path_of_local_conditions t ρ hρ hs hf hC hD

theorem signed_path_pairs_eventually :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ ρ : ℝ, 0 < ρ →
      ∃ x : ℝ → Coord, Continuous x ∧ x 0 = ρ • baseCurve t ∧
        ∀ᶠ e in 𝓝 (0 : ℝ), 0 < e →
          gramMatrix (x e) = e^2 • targetR ∧
          gramMatrix (x (-e)) = e^2 • targetR ∧
          0 < (aMatrix (x e)).det ∧ (aMatrix (x (-e))).det < 0 ∧
          f (x e) = e^2/2 ∧ f (x (-e)) = 0 := by
  filter_upwards [signed_paths_eventually] with t ht
  intro ρ hρ
  obtain ⟨x,hx,hx0,hp⟩ := ht ρ hρ
  refine ⟨x,hx,hx0, ?_⟩
  have hneg : Tendsto (fun e : ℝ => -e) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
  have hn := hneg.eventually hp
  filter_upwards [hp, hn] with e he hne
  intro hpos
  have hs := he.2.1 hpos
  have hsneg := hne.2.2 (neg_neg_of_pos hpos)
  exact ⟨he.1, by simpa only [neg_sq] using hne.1, hs.1, hsneg.1, hs.2, hsneg.2⟩

end PBCounterexample.Gram7
