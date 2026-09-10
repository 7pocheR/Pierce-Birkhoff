import PBCounterexample.Gram6FiniteParameters
import PBCounterexample.Gram6LocalPaths
import PBCounterexample.Gram6Function

/-! Agreement of every finite homogeneous test family and unrestricted nonrepresentation. -/

namespace PBCounterexample.Gram6

open Matrix MvPolynomial Filter
open scoped Topology ContDiff

private theorem sign_add_eq_of_abs_lt {a b : ℝ} (ha : a ≠ 0) (hb : |b| < |a|) :
    a + b ≠ 0 ∧ Real.sign (a + b) = Real.sign a := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hab : a + b < 0 := by
      rw [abs_of_neg ha] at hb
      have h := (abs_lt.mp hb).2
      linarith only [h]
    exact ⟨ne_of_lt hab, by rw [Real.sign_of_neg hab, Real.sign_of_neg ha]⟩
  · have hab : 0 < a + b := by
      rw [abs_of_pos ha] at hb
      have h := (abs_lt.mp hb).1
      linarith only [h]
    exact ⟨ne_of_gt hab, by rw [Real.sign_of_pos hab, Real.sign_of_pos ha]⟩

private theorem pos_of_real_sign_eq_one {a : ℝ} (h : Real.sign a = 1) : 0 < a := by
  by_contra ha
  rcases lt_or_eq_of_le (le_of_not_gt ha) with ha | ha
  · rw [Real.sign_of_neg ha] at h
    norm_num at h
  · rw [ha, Real.sign_zero] at h
    norm_num at h

private theorem nonpos_of_real_sign_eq_neg_one {a : ℝ} (h : Real.sign a = -1) : a ≤ 0 := by
  by_contra ha
  rw [Real.sign_of_pos (lt_of_not_ge ha)] at h
  norm_num at h

theorem exists_same_homogeneous_signs_different_f
    (S : Finset (MvPolynomial (Fin 6) ℝ))
    (hS : ∀ p ∈ S, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2) :
    ∃ v w : Coord,
      (∀ p ∈ S, Real.sign (eval v p) = Real.sign (eval w p)) ∧
      0 < f v ∧ f w = 0 := by
  classical
  obtain ⟨t, δ, hδ, hparameters⟩ := exists_finite_homogeneous_parameters S hS
  obtain ⟨zPlus, zMinus, hp0, hm0, hp, hm, hpt, hmt, hQ⟩ :=
    exists_opposite_corrected_gram_paths t 1 δ (by norm_num) hδ
  let v : ℝ → Coord := fun ε =>
    curve t + ε • (normalDirection t 1 + δ • kernelDirection t + zPlus ε)
  let w : ℝ → Coord := fun ε =>
    curve t + ε • (normalDirection t 1 + (-δ) • kernelDirection t + zMinus ε)
  have hv0 : v 0 = curve t := by simp only [v, zero_smul, add_zero]
  have hw0 : w 0 = curve t := by simp only [w, zero_smul, add_zero]
  have hvD : HasDerivAt v (normalDirection t 1 + δ • kernelDirection t) 0 :=
    hasDerivAt_corrected_point (curve t) (normalDirection t 1 + δ • kernelDirection t)
      zPlus hp0 hp
  have hwD : HasDerivAt w (normalDirection t 1 + (-δ) • kernelDirection t) 0 :=
    hasDerivAt_corrected_point (curve t) (normalDirection t 1 + (-δ) • kernelDirection t)
      zMinus hm0 hm
  have hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (curve t)) := by
    simpa only [hv0] using hvD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 (curve t)) := by
    simpa only [hw0] using hwD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGram : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      gramMatrix (v ε) = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget ∧
      gramMatrix (w ε) = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget := by
    simpa only [v, w, one_smul, sub_eq_add_neg, neg_smul] using
      hQ.filter_mono nhdsWithin_le_nhds
  have heach : ∀ p ∈ S, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.sign (eval (v ε) p) = Real.sign (eval (w ε) p) := by
    intro p hpS
    rcases hparameters p hpS with hpzero | hpbase | ⟨hp2, hpc, hpvariation | hpGram⟩
    · exact Filter.Eventually.of_forall fun ε => by simp only [hpzero, map_zero]
    · have hvs := eventually_real_sign_eq_of_tendsto
        (((MvPolynomial.continuous_eval p).tendsto (curve t)).comp hv) hpbase
      have hws := eventually_real_sign_eq_of_tendsto
        (((MvPolynomial.continuous_eval p).tendsto (curve t)).comp hw) hpbase
      filter_upwards [hvs, hws] with ε hvε hwε
      exact hvε.trans hwε.symm
    · let a := quadraticVariation p (curve t) (normalDirection t 1)
      let b := δ * quadraticVariation p (curve t) (kernelDirection t)
      have ha : a ≠ 0 := hpvariation.1
      have hb : |b| < |a| := by
        have hbhalf : |b| < |a| / 2 := by
          simpa only [a, b, abs_mul, abs_of_pos hδ] using hpvariation.2
        exact lt_trans hbhalf (half_lt_self (abs_pos.mpr ha))
      obtain ⟨hap, hsp⟩ := sign_add_eq_of_abs_lt ha hb
      obtain ⟨ham, hsm⟩ := sign_add_eq_of_abs_lt (b := -b) ha
        (by simpa only [abs_neg] using hb)
      have hdp : HasDerivAt (fun ε => eval (v ε) p) (a + b) 0 := by
        simpa only [hv0, quadraticVariation_add_right, quadraticVariation_smul_right, a, b] using
          hasDerivAt_eval_homogeneous_two p hp2 hvD
      have hdm : HasDerivAt (fun ε => eval (w ε) p) (a + -b) 0 := by
        simpa only [hw0, quadraticVariation_add_right, quadraticVariation_smul_right,
          a, b, neg_mul] using hasDerivAt_eval_homogeneous_two p hp2 hwD
      have hpbase0 : eval (v 0) p = 0 := by rw [hv0]; exact hpc t
      have hmbase0 : eval (w 0) p = 0 := by rw [hw0]; exact hpc t
      have hvs := eventually_real_sign_eq_of_hasDerivAt_zero hdp hpbase0 hap
      have hws := eventually_real_sign_eq_of_hasDerivAt_zero hdm hmbase0 ham
      filter_upwards [hvs, hws] with ε hvε hwε
      exact (hvε.trans hsp).trans (hwε.trans hsm).symm
    · obtain ⟨a, b, c, hpGram⟩ := hpGram
      filter_upwards [hGram] with ε hε
      apply congrArg Real.sign
      rw [hpGram]
      simp only [map_add, map_mul, eval_C, eval_gramPolynomial, hε.1, hε.2]
  have hsigns : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ S,
      Real.sign (eval (v ε) p) = Real.sign (eval (w ε) p) :=
    (Filter.eventually_all_finset S).mpr heach
  have hDP : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sign ((aMatrix (v ε)).det) = 1 := by
    simpa only [v, Real.sign_of_pos hδ] using
      eventually_corrected_determinant_sign t δ (ne_of_gt hδ) zPlus hp0 hp
  have hDM : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sign ((aMatrix (w ε)).det) = -1 := by
    simpa only [w, Real.sign_of_neg (neg_neg_of_pos hδ)] using
      eventually_corrected_determinant_sign t (-δ) (neg_ne_zero.mpr (ne_of_gt hδ))
        zMinus hm0 hm
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ (∀ p ∈ S, Real.sign (eval (v ε) p) = Real.sign (eval (w ε) p)) ∧
      (gramMatrix (v ε) = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget ∧
        gramMatrix (w ε) = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget) ∧
      Real.sign ((aMatrix (v ε)).det) = 1 ∧ Real.sign ((aMatrix (w ε)).det) = -1 := by
    filter_upwards [self_mem_nhdsWithin, hsigns, hGram, hDP, hDM] with ε hε hs hq hdP hdM
    exact ⟨hε, hs, hq, hdP, hdM⟩
  obtain ⟨ε, hε, hs, hq, hdP, hdM⟩ := hall.exists
  refine ⟨v ε, w ε, hs, ?_, ?_⟩
  · rw [f_of_gram_target_positive_determinant (v ε) ε δ hε hδ hq.1
      (pos_of_real_sign_eq_one hdP)]
    positivity
  · exact f_zero_of_nonpositive_determinant (w ε) (nonpos_of_real_sign_eq_neg_one hdM)

/-- Every finite expression in arbitrary real polynomial leaves is excluded. -/
theorem not_isPolynomialLattice : ¬ IsPolynomialLattice f := by
  intro hrep
  have hhom : ∀ (r : ℝ), 0 < r → ∀ z : Coord,
      f (fun i => r * z i) = r^2 * f z := by
    intro r hr z
    have hscale : (fun i => r * z i) = r • z := by
      ext i
      rfl
    rw [hscale]
    exact f_positive_homogeneous r hr z
  obtain ⟨S, hS, hsign⟩ := homogeneous_lattice_finite_homogeneous_sign_condition f hhom hrep
  obtain ⟨v, w, hp, hv, hw⟩ := exists_same_homogeneous_signs_different_f S hS
  have h := hsign v w hp
  rw [Real.sign_of_pos hv, hw, Real.sign_zero] at h
  norm_num at h

end PBCounterexample.Gram6
