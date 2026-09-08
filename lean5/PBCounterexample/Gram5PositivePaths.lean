import PBCounterexample.Gram5Scaling

/-! Actual positive-height and zero-height points on the two corrected paths. -/

namespace PBCounterexample.Gram5

open Filter
open scoped Topology

noncomputable section

theorem eventually_pos_of_div_pow_tendsto {g : ℝ → ℝ} {L : ℝ} (m : ℕ)
    (hL : 0 < L) (hg : Tendsto (fun t : ℝ => g t/t^m) (𝓝[>] 0) (𝓝 L)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t := by
  filter_upwards [hg.eventually (eventually_gt_nhds hL), self_mem_nhdsWithin] with t h ht
  change 0 < t at ht
  exact (div_pos_iff_of_pos_right (pow_pos ht m)).mp h

theorem eventually_neg_of_div_pow_tendsto {g : ℝ → ℝ} {L : ℝ} (m : ℕ)
    (hL : L < 0) (hg : Tendsto (fun t : ℝ => g t/t^m) (𝓝[>] 0) (𝓝 L)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, g t < 0 := by
  filter_upwards [hg.eventually (eventually_lt_nhds hL), self_mem_nhdsWithin] with t h ht
  change 0 < t at ht
  have := (div_lt_iff₀ (pow_pos ht m)).mp h
  simpa only [zero_mul] using this

theorem eventually_gt_higher_power {g : ℝ → ℝ} {L : ℝ} (m k : ℕ) (c : ℝ)
    (hmk : m < k) (hL : 0 < L)
    (hg : Tendsto (fun t : ℝ => g t/t^m) (𝓝[>] 0) (𝓝 L)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, c*t^k < g t := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun t : ℝ => c*t^(k-m)) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa [Nat.sub_ne_zero_of_lt hmk] using Tendsto.const_mul c (ht.pow (k-m))
  have hdiff : Tendsto (fun t : ℝ => (g t-c*t^k)/t^m) (𝓝[>] 0) (𝓝 L) := by
    have hh : Tendsto (fun t : ℝ => g t/t^m-c*t^(k-m)) (𝓝[>] 0) (𝓝 L) := by
      simpa only [sub_zero] using hg.sub hpow
    apply (tendsto_congr' ?_).2 hh
    filter_upwards [self_mem_nhdsWithin] with t htpos
    change 0 < t at htpos
    have hdecomp : t^k = t^(k-m)*t^m := by rw [← pow_add, Nat.sub_add_cancel hmk.le]
    rw [hdecomp]
    field_simp [ne_of_gt htpos] <;> ring
  filter_upwards [eventually_pos_of_div_pow_tendsto m hL hdiff] with t ht
  linarith

theorem eventually_abs_lt_radius {r : ℝ} (hr : 0 < r) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, |t| < r := by
  have ht : Tendsto (fun t : ℝ => |t|) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  exact ht.eventually (eventually_lt_nhds hr)

namespace CorrectionFamily

variable {δ σ : ℝ} (F : CorrectionFamily δ σ)

theorem eventually_leadingG_pos (hσ : σ*δ < 1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < MvPolynomial.eval (F.point ε 0) leadingG := by
  apply eventually_pos_of_div_pow_tendsto 1 (by linarith : 0 < 1-σ*δ)
  simpa only [pow_one] using F.tendsto_leadingG_div

theorem eventually_leadingDeterminant_pos (hσ : 0 < σ*δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < MvPolynomial.eval (F.point ε 0) leadingDeterminant := by
  apply eventually_pos_of_div_pow_tendsto 1 hσ
  simpa only [pow_one] using F.tendsto_leadingDeterminant_div

theorem eventually_leadingDeterminant_neg (hσ : σ*δ < 0) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, MvPolynomial.eval (F.point ε 0) leadingDeterminant < 0 := by
  apply eventually_neg_of_div_pow_tendsto 1 hσ
  simpa only [pow_one] using F.tendsto_leadingDeterminant_div

theorem eventually_minimum_eq (ε : ℝ) (hε : |ε| < F.radius)
    (hg : 0 < MvPolynomial.eval (F.point ε 0) leadingG) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, minimum (F.scaledPoint ε t) = 6*t^16*ε^2*δ^2 := by
  have hv := (F.tendsto_point_lambda ε hε).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hq : ∀ᶠ t : ℝ in 𝓝[>] 0, 6*ε^2*δ^2*t^16 < q 2 (F.scaledPoint ε t) := by
    exact eventually_gt_higher_power 12 16 (6*ε^2*δ^2) (by norm_num)
      (mul_pos (by norm_num) hg) (tendsto_q_two_div hv)
  filter_upwards [hq, eventually_abs_lt_radius F.radius_pos,
    self_mem_nhdsWithin] with t hq2 ht htpos
  change 0 < t at htpos
  have h0 := F.matched_q_zero ε t hε ht
  have h1 := F.matched_q_one ε t hε ht
  have h3 := F.matched_q_three ε t hε ht
  apply le_antisymm
  · simpa only [h1] using minimum_le (F.scaledPoint ε t) 1
  · apply (le_minimum_iff _ _).mpr
    intro i
    fin_cases i
    · change 6*t^16*ε^2*δ^2 ≤ q 0 (F.scaledPoint ε t)
      rw [h0]
      have hnonneg : 0 ≤ t^16*ε^2*δ^2 := by positivity
      nlinarith
    · exact h1.ge
    · change 6*t^16*ε^2*δ^2 ≤ q 2 (F.scaledPoint ε t)
      nlinarith
    · exact h3.ge

theorem eventually_f_positive_height (ε : ℝ) (hε0 : 0 < ε) (hδ : 0 < δ)
    (hε : |ε| < F.radius)
    (hg : 0 < MvPolynomial.eval (F.point ε 0) leadingG)
    (hG : 0 < MvPolynomial.eval (F.point ε 0) leadingDeterminant) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      f (F.scaledPoint ε t) = 6*t^16*ε^2*δ^2 ∧ 0 < f (F.scaledPoint ε t) := by
  have hv := (F.tendsto_point_lambda ε hε).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hD := eventually_pos_of_div_pow_tendsto 18
    (mul_pos (by norm_num) hG) (tendsto_determinant_div hv)
  filter_upwards [F.eventually_minimum_eq ε hε hg, hD,
    self_mem_nhdsWithin] with t hm hD htpos
  change 0 < t at htpos
  have hh : 0 < minimum (F.scaledPoint ε t) := by rw [hm]; positivity
  have hf := f_of_positive hh hD
  exact ⟨hf.trans hm, hf.symm ▸ hh⟩

theorem eventually_f_zero (ε : ℝ) (hε : |ε| < F.radius)
    (hG : MvPolynomial.eval (F.point ε 0) leadingDeterminant < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, f (F.scaledPoint ε t) = 0 := by
  have hv := (F.tendsto_point_lambda ε hε).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hD := eventually_neg_of_div_pow_tendsto 18
    (mul_neg_of_pos_of_neg (by norm_num) hG) (tendsto_determinant_div hv)
  filter_upwards [hD] with t ht
  exact f_of_determinant_nonpos ht.le

end CorrectionFamily

end

end PBCounterexample.Gram5
