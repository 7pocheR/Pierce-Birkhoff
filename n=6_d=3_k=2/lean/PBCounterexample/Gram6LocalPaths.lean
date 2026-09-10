import PBCounterexample.Gram6Implicit
import PBCounterexample.Gram6Function
import PBCounterexample.Gram6DeterminantVariations
import PBCounterexample.SignTopology
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Determinant signs and exact values on the actual corrected real paths. -/

namespace PBCounterexample

open Filter
open scoped Topology ContDiff

theorem real_sign_mul_of_pos_left (a b : ℝ) (ha : 0 < a) :
    Real.sign (a*b) = Real.sign b := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), Real.sign_of_neg hb]
  · simp only [mul_zero]
  · rw [Real.sign_of_pos (mul_pos ha hb), Real.sign_of_pos hb]

theorem eventually_real_sign_eq_of_hasDerivAt_zero
    {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hg0 : g 0 = 0) (hd : d ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sign (g ε) = Real.sign d := by
  have ht : Tendsto (fun ε : ℝ => ε⁻¹ * g ε) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, hg0, sub_zero, smul_eq_mul] using
      hg.tendsto_slope_zero_right
  have hs := eventually_real_sign_eq_of_tendsto ht hd
  filter_upwards [hs, self_mem_nhdsWithin] with ε hε hpos
  rw [real_sign_mul_of_pos_left ε⁻¹ (g ε) (inv_pos.mpr hpos)] at hε
  exact hε

namespace Gram6

open Matrix MvPolynomial

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

theorem determinant_curve (t : ℝ) : (aMatrix (curve t)).det = 0 := by
  norm_num [determinant_explicit, curve, Matrix.cons_val,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem determinantLinearTerm_add_right (v w z : Coord) :
    determinantLinearTerm v (w+z) =
      determinantLinearTerm v w + determinantLinearTerm v z := by
  simp only [determinantLinearTerm, Pi.add_apply]
  ring

theorem hasDerivAt_corrected_point (v y : Coord) (z : ℝ → Coord)
    (hz0 : z 0 = 0) (hz : ContDiffAt ℝ ∞ z 0) :
    HasDerivAt (fun ε : ℝ => v + ε • (y + z ε)) y 0 := by
  have hzd := (hz.differentiableAt (by simp)).hasDerivAt
  simpa only [Pi.smul_apply, id_eq, hz0, add_zero, zero_smul,
    one_smul, zero_add] using!
      (((hasDerivAt_id (0 : ℝ)).smul (hzd.const_add y)).const_add v)

theorem hasDerivAt_determinant_corrected_point (v y : Coord) (z : ℝ → Coord)
    (hz0 : z 0 = 0) (hz : ContDiffAt ℝ ∞ z 0) :
    HasDerivAt (fun ε : ℝ => (aMatrix (v + ε • (y + z ε))).det)
      (determinantLinearTerm v y) 0 := by
  have hD : ContDiff ℝ 1 (fun w : Coord => (aMatrix w).det) := by
    simp only [determinant_explicit]
    fun_prop
  have hlinear : HasDerivAt (fun ε : ℝ => v + ε • y) y 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const y).const_add v)
  have hfirst := (hD.differentiable_one v).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hlinear (by simp)
  have hvalue := hfirst.unique (hasDerivAt_determinant_line v y)
  have hpath := (hD.differentiable_one v).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_corrected_point v y z hz0 hz) (by simp)
  simpa only [Function.comp_def] using! (hpath.congr_deriv hvalue)

theorem determinantLinearTerm_normal_add_kernel (t δ : ℝ) :
    determinantLinearTerm (curve t)
      (normalDirection t 1 + δ • kernelDirection t) =
        δ * determinantLinearTerm (curve t) (kernelDirection t) := by
  have hn := determinantLinearTerm_base_normal t 1
  simp only [one_smul] at hn
  rw [determinantLinearTerm_add_right, determinantLinearTerm_smul_right, hn, zero_add]

theorem eventually_corrected_determinant_sign (t δ : ℝ) (hδ : δ ≠ 0)
    (z : ℝ → Coord) (hz0 : z 0 = 0) (hz : ContDiffAt ℝ ∞ z 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.sign ((aMatrix (curve t + ε •
        (normalDirection t 1 + δ • kernelDirection t + z ε))).det) =
        Real.sign δ := by
  have hj : 0 < determinantLinearTerm (curve t) (kernelDirection t) := by
    simpa only [one_smul] using
      determinantLinearTerm_base_kernelDirection_pos t 1 (by norm_num)
  have hd := hasDerivAt_determinant_corrected_point (curve t)
    (normalDirection t 1 + δ • kernelDirection t) z hz0 hz
  rw [determinantLinearTerm_normal_add_kernel] at hd
  have hzero : (aMatrix (curve t + (0 : ℝ) •
      (normalDirection t 1 + δ • kernelDirection t + z 0))).det = 0 := by
    simpa only [zero_smul, add_zero] using determinant_curve t
  have hs := eventually_real_sign_eq_of_hasDerivAt_zero hd hzero
    (mul_ne_zero hδ (ne_of_gt hj))
  simpa only [mul_comm δ (determinantLinearTerm (curve t) (kernelDirection t)),
    real_sign_mul_of_pos_left _ δ hj] using hs

theorem eval_labelPolynomial_of_gram_target (w : Coord) (ε δ : ℝ)
    (hQ : gramMatrix w = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget)
    (i : Fin 4) :
    eval w (labelPolynomial i) =
      ![(3/2)*ε^2*δ^2, (1/2)*ε^2*δ^2,
        16*ε+(17/2)*ε^2*δ^2, (1/2)*ε^2*δ^2] i := by
  fin_cases i <;>
    norm_num [labelPolynomial, eval_gramPolynomial, hQ, rankOneTarget,
      interiorTarget, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] <;> ring

theorem minimum_of_gram_target (w : Coord) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hQ : gramMatrix w = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget) :
    minimum w = (1/2)*ε^2*δ^2 := by
  have hnonneg : 0 ≤ ε^2*δ^2 := mul_nonneg (sq_nonneg ε) (sq_nonneg δ)
  have hlower (a : Label) : (1/2)*ε^2*δ^2 ≤ eval w (qPolynomial a) := by
    obtain ⟨i, hi⟩ := fourEdges_covers a
    change (1/2)*ε^2*δ^2 ≤ eval w (allQuadratics a.val)
    rw [← hi, allQuadratics_fourEdges, eval_labelPolynomial_of_gram_target w ε δ hQ]
    fin_cases i <;> norm_num [Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> nlinarith
  have heq : eval w (qPolynomial ⟨edge03, by decide⟩) = (1/2)*ε^2*δ^2 := by
    change eval w (allQuadratics (fourEdges 1)) = _
    rw [allQuadratics_fourEdges, eval_labelPolynomial_of_gram_target w ε δ hQ]
    rfl
  apply le_antisymm
  · exact (PolynomialSelection.minimum_le qPolynomial w ⟨edge03, by decide⟩).trans_eq heq
  · exact (PolynomialSelection.le_minimum_iff qPolynomial w _).mpr hlower

theorem f_of_gram_target_positive_determinant (w : Coord) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hQ : gramMatrix w = ε • rankOneTarget + (ε^2*δ^2) • interiorTarget)
    (hD : 0 < (aMatrix w).det) : f w = (1/2)*ε^2*δ^2 := by
  have hm := minimum_of_gram_target w ε δ (le_of_lt hε) hQ
  have hp : 0 < minimum w := by rw [hm]; positivity
  change (if 0 < minimum w ∧ 0 < eval w determinantPolynomial then minimum w else 0) = _
  rw [eval_determinantPolynomial, if_pos ⟨hp, hD⟩, hm]

theorem f_zero_of_nonpositive_determinant (w : Coord)
    (hD : (aMatrix w).det ≤ 0) : f w = 0 := by
  change (if 0 < minimum w ∧ 0 < eval w determinantPolynomial then minimum w else 0) = 0
  rw [eval_determinantPolynomial, if_neg (fun h => not_lt_of_ge hD h.2)]

end Gram6
end PBCounterexample
