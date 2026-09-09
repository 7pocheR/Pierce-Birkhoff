import PBCounterexample.Gram7Avoidance
import PBCounterexample.Gram7LocalPaths
import PBCounterexample.RadialTests

/-! The seven-variable function has no polynomial lattice representation. -/

noncomputable section

namespace PBCounterexample.Gram7

open Filter
open scoped Topology

theorem finite_homogeneous_tests_do_not_determine_sign
    (s : Finset (MvPolynomial (Fin 7) ℝ))
    (hs : ∀ p ∈ s, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2) :
    ∃ z w : Coord,
      (∀ p ∈ s, Real.sign (MvPolynomial.eval z p) =
        Real.sign (MvPolynomial.eval w p)) ∧
      Real.sign (f z) ≠ Real.sign (f w) := by
  let U : Set ℝ := {t | ∃ x : ℝ → Coord,
    Continuous x ∧ x 0 = baseCurve t ∧
      ∀ᶠ e in 𝓝 (0 : ℝ), 0 < e →
        gramMatrix (x e) = e^2 • targetR ∧
        gramMatrix (x (-e)) = e^2 • targetR ∧
        0 < (aMatrix (x e)).det ∧ (aMatrix (x (-e))).det < 0 ∧
        f (x e) = e^2/2 ∧ f (x (-e)) = 0}
  have hU : U ∈ 𝓝 (0 : ℝ) := by
    filter_upwards [signed_path_pairs_eventually] with t ht
    simpa only [U, Set.mem_ofPred_eq, one_smul] using ht 1 (by norm_num)
  obtain ⟨t, htU, _, ht⟩ := exists_positive_time_avoid_homogeneous_tests s hs U hU
  obtain ⟨x, hx, hx0, hxprop⟩ := htU
  have ha : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 (baseCurve t)) := by
    simpa only [hx0] using (hx.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun e : ℝ => x (-e))
      (𝓝[>] (0 : ℝ)) (𝓝 (baseCurve t)) := by
    have hc := (hx.comp continuous_neg).tendsto (0 : ℝ)
    simpa only [Function.comp_def, neg_zero, hx0] using hc.mono_left nhdsWithin_le_nhds
  have htests : ∀ p ∈ s,
      (∀ᶠ e in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (x e) p = MvPolynomial.eval (x (-e)) p) ∨
      MvPolynomial.eval (baseCurve t) p ≠ 0 := by
    intro p hp
    rcases ht p hp with hmem | hne
    · left
      filter_upwards [hxprop.filter_mono nhdsWithin_le_nhds,
        show ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e from self_mem_nhdsWithin] with e he hepos
      have hg := he hepos
      exact eval_eq_of_mem_gramQuadraticSpan_of_gram_eq hmem (hg.1.trans hg.2.1.symm)
    · exact Or.inr hne
  obtain ⟨e, he, hepos, hesigns⟩ :=
    exists_positive_time_same_polynomial_signs_of_eventual s
      x (fun e => x (-e)) (baseCurve t) ha hb htests _ hxprop
  have hv := he hepos
  refine ⟨x e, x (-e), hesigns, ?_⟩
  rw [hv.2.2.2.2.1, hv.2.2.2.2.2, Real.sign_zero,
    Real.sign_of_pos (by positivity : (0 : ℝ) < e^2/2)]
  norm_num

theorem not_isPolynomialLattice_f : ¬ IsPolynomialLattice f := by
  intro hrep
  have hhom : ∀ (t : ℝ), 0 < t → ∀ z : Coord,
      f (fun i => t * z i) = t^2 * f z := by
    intro t ht z
    exact f_positive_homogeneous t ht z
  obtain ⟨s, hs, hdetermines⟩ :=
    homogeneous_lattice_finite_homogeneous_sign_condition f hhom hrep
  obtain ⟨z, w, hsame, hdifferent⟩ := finite_homogeneous_tests_do_not_determine_sign s hs
  exact hdifferent (hdetermines z w hsame)

end PBCounterexample.Gram7
