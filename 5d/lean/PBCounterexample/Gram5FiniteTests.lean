import PBCounterexample.Gram5PositivePaths

/-! Finite simultaneous choices for real polynomial tests and quadratic offsets. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology

noncomputable section

def SameStrictSign (x y : ℝ) : Prop := (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)

private theorem sameStrictSign_of_tendsto {u v : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hu : Tendsto u (𝓝[>] 0) (𝓝 r))
    (hv : Tendsto v (𝓝[>] 0) (𝓝 r)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, SameStrictSign (u t) (v t) := by
  rcases lt_or_gt_of_ne hr with hr | hr
  · filter_upwards [hu.eventually (eventually_lt_nhds hr),
      hv.eventually (eventually_lt_nhds hr)] with t ht hu
    exact Or.inr ⟨ht, hu⟩
  · filter_upwards [hu.eventually (eventually_gt_nhds hr),
      hv.eventually (eventually_gt_nhds hr)] with t ht hu
    exact Or.inl ⟨ht, hu⟩

theorem exists_delta_finite_tests (S : Finset Poly) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ ∀ H ∈ S,
      differential H normalDirection ≠ 0 →
        SameStrictSign
          (differential H (normalDirection + δ • signDirection))
          (differential H (normalDirection + (-δ) • signDirection)) := by
  have ht : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have htest (H : Poly) : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      differential H normalDirection ≠ 0 →
        SameStrictSign
          (differential H (normalDirection + δ • signDirection))
          (differential H (normalDirection + (-δ) • signDirection)) := by
    by_cases hH : differential H normalDirection = 0
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hH)
    have hplus : Tendsto
        (fun δ : ℝ => differential H (normalDirection + δ • signDirection))
        (𝓝[>] 0) (𝓝 (differential H normalDirection)) := by
      simpa only [map_add, map_smul, smul_eq_mul, mul_zero, zero_mul, add_zero] using
        (tendsto_const_nhds.add (Tendsto.mul_const (differential H signDirection) ht))
    have hminus : Tendsto
        (fun δ : ℝ => differential H (normalDirection + (-δ) • signDirection))
        (𝓝[>] 0) (𝓝 (differential H normalDirection)) := by
      simpa only [map_add, map_smul, smul_eq_mul, neg_zero, mul_zero, zero_mul, add_zero] using
        (tendsto_const_nhds.add (Tendsto.mul_const (differential H signDirection) ht.neg))
    filter_upwards [sameStrictSign_of_tendsto hH hplus hminus] with δ hδ
    exact fun _ => hδ
  have hall := (eventually_all_finset S).mpr (fun H _ => htest H)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1/2 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hfinal : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ δ < 1/2 ∧ ∀ H ∈ S, differential H normalDirection ≠ 0 →
        SameStrictSign (differential H (normalDirection + δ • signDirection))
          (differential H (normalDirection + (-δ) • signDirection)) := by
    filter_upwards [self_mem_nhdsWithin, hb, hall] with δ hδ hb hh
    exact ⟨hδ, hb, hh⟩
  exact hfinal.exists

namespace CorrectionFamily

variable {δ σ : ℝ} (F : CorrectionFamily δ σ)

def shiftedTest (H : Poly) (c ε : ℝ) : ℝ :=
  eval (F.point ε 0) H + c*ε^2*δ^2

theorem tendsto_shiftedTest (H : Poly) (c : ℝ) :
    Tendsto (F.shiftedTest H c) (𝓝[>] 0) (𝓝 (eval basePoint H)) := by
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hp := (F.tendsto_eval_point_epsilon H).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [shiftedTest] using! hp.add
    (Tendsto.mul_const (δ^2) (Tendsto.const_mul c (ht.pow 2)))

theorem tendsto_shiftedTest_div (H : Poly) (c : ℝ) (hH : eval basePoint H = 0) :
    Tendsto (fun ε : ℝ => F.shiftedTest H c ε/ε) (𝓝[>] 0)
      (𝓝 (differential H (normalDirection + (σ*δ) • signDirection))) := by
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (F.tendsto_eval_point_div H hH).add
    (Tendsto.mul_const (δ^2) (Tendsto.const_mul c ht))
  have hh' : Tendsto (fun ε : ℝ => eval (F.point ε 0) H/ε + c*ε*δ^2)
      (𝓝[>] 0) (𝓝 (differential H (normalDirection + (σ*δ) • signDirection))) := by
    simpa only [mul_zero, zero_mul, add_zero] using hh
  apply (tendsto_congr' ?_).2 hh'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  unfold shiftedTest
  field_simp [ne_of_gt hε] <;> ring

end CorrectionFamily

theorem eventually_sameStrictSign_shifted {δ : ℝ}
    (Fplus : CorrectionFamily δ 1) (Fminus : CorrectionFamily δ (-1))
    (H : Poly) (c : ℝ)
    (hH : eval basePoint H ≠ 0 ∨
      SameStrictSign (differential H (normalDirection + δ • signDirection))
        (differential H (normalDirection + (-δ) • signDirection))) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SameStrictSign (Fplus.shiftedTest H c ε) (Fminus.shiftedTest H c ε) := by
  by_cases hvalue : eval basePoint H = 0
  · have hd := hH.resolve_left (not_not.mpr hvalue)
    have hp := Fplus.tendsto_shiftedTest_div H c hvalue
    have hm := Fminus.tendsto_shiftedTest_div H c hvalue
    simp only [one_mul, neg_one_mul] at hp hm
    rcases hd with ⟨hp0, hm0⟩ | ⟨hp0, hm0⟩
    · have heplus := eventually_pos_of_div_pow_tendsto 1 hp0 (by simpa only [pow_one] using hp)
      have heminus := eventually_pos_of_div_pow_tendsto 1 hm0 (by simpa only [pow_one] using hm)
      filter_upwards [heplus, heminus] with ε hεp hεm
      exact Or.inl ⟨hεp, hεm⟩
    · have heplus := eventually_neg_of_div_pow_tendsto 1 hp0 (by simpa only [pow_one] using hp)
      have heminus := eventually_neg_of_div_pow_tendsto 1 hm0 (by simpa only [pow_one] using hm)
      filter_upwards [heplus, heminus] with ε hεp hεm
      exact Or.inr ⟨hεp, hεm⟩
  · exact sameStrictSign_of_tendsto hvalue (Fplus.tendsto_shiftedTest H c)
      (Fminus.tendsto_shiftedTest H c)

end

end PBCounterexample.Gram5
