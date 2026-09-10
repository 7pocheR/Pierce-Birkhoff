import PBCounterexample.Gram5LeafDecomposition
import PBCounterexample.Gram5FiniteTests

/-! Normalized limits and threshold transfer for unrestricted polynomial leaves. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology

noncomputable section

namespace LeafDecomposition

variable {P : Poly} (L : LeafDecomposition P)

theorem first_component_or_zero :
    (∃ m : ℕ, m ≤ 16 ∧ component L.remainder m ≠ 0 ∧
      ∀ n < m, component L.remainder n = 0) ∨
    (∀ n ≤ 16, component L.remainder n = 0) := by
  classical
  by_cases h : ∃ m : ℕ, m ≤ 16 ∧ component L.remainder m ≠ 0
  · left
    have hbound : Nat.find h ≤ 16 := (Nat.find_spec h).1
    refine ⟨Nat.find h, hbound, (Nat.find_spec h).2, ?_⟩
    intro n hn
    by_contra hne
    exact Nat.find_min h hn ⟨by omega, hne⟩
  · right
    push_neg at h
    exact h

def effectiveValue {δ σ : ℝ} (F : CorrectionFamily δ σ) (m : ℕ) (ε : ℝ) : ℝ :=
  eval (F.point ε 0) (component L.remainder m) +
    if m = 16 then L.commonCoefficient*ε^2*δ^2 else 0

theorem tendsto_eval_div_first {δ σ : ℝ} (F : CorrectionFamily δ σ)
    (ε : ℝ) (hε : |ε| < F.radius) (m : ℕ) (hm : m ≤ 16)
    (hbelow : ∀ n < m, component L.remainder n = 0) :
    Tendsto (fun t : ℝ => eval (F.scaledPoint ε t) P/t^m)
      (𝓝[>] 0) (𝓝 (L.effectiveValue F m ε)) := by
  have hv := (F.tendsto_point_lambda ε hε).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hR := WeightedPolynomial.tendsto_eval_scale_div weights L.remainder m hbelow hv
  change Tendsto (fun t : ℝ => eval (F.scaledPoint ε t) L.remainder/t^m)
    (𝓝[>] 0) (𝓝 (eval (F.point ε 0) (component L.remainder m))) at hR
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hoffset : Tendsto
      (fun t : ℝ => t^(16-m)*L.commonCoefficient*ε^2*δ^2)
      (𝓝[>] 0) (𝓝 (if m = 16 then L.commonCoefficient*ε^2*δ^2 else 0)) := by
    by_cases hm16 : m = 16
    · subst m
      simpa using (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => L.commonCoefficient*ε^2*δ^2) (𝓝[>] 0)
        (𝓝 (L.commonCoefficient*ε^2*δ^2)))
    · have hpos : 0 < 16-m := by omega
      simpa [hm16, zero_pow (ne_of_gt hpos)] using
        (((ht.pow (16-m)).mul_const L.commonCoefficient).mul_const (ε^2)).mul_const (δ^2)
  have hsum := hR.add hoffset
  change Tendsto (fun t : ℝ => eval (F.scaledPoint ε t) L.remainder/t^m +
    t^(16-m)*L.commonCoefficient*ε^2*δ^2) (𝓝[>] 0)
    (𝓝 (L.effectiveValue F m ε)) at hsum
  apply (tendsto_congr' ?_).2 hsum
  filter_upwards [eventually_abs_lt_radius F.radius_pos, self_mem_nhdsWithin]
    with t htbound htpos
  change 0 < t at htpos
  rw [L.eval_scaled F ε t hε htbound]
  have hpower : t^16 = t^(16-m)*t^m := by rw [← pow_add, Nat.sub_add_cancel hm]
  rw [hpower]
  field_simp [ne_of_gt htpos]

theorem tendsto_eval_div_zero {δ σ : ℝ} (F : CorrectionFamily δ σ)
    (ε : ℝ) (hε : |ε| < F.radius)
    (hthrough : ∀ n ≤ 16, component L.remainder n = 0) :
    Tendsto (fun t : ℝ => eval (F.scaledPoint ε t) P/t^16)
      (𝓝[>] 0) (𝓝 (L.commonCoefficient*ε^2*δ^2)) := by
  have hh := L.tendsto_eval_div_first F ε hε 16 le_rfl
    (fun n hn => hthrough n hn.le)
  simpa [effectiveValue, hthrough 16 le_rfl] using hh

theorem eventually_transfer_first {δ : ℝ}
    (Fplus : CorrectionFamily δ 1) (Fminus : CorrectionFamily δ (-1))
    (ε : ℝ) (hεp : |ε| < Fplus.radius) (hεm : |ε| < Fminus.radius)
    (m : ℕ) (hm : m ≤ 16) (hbelow : ∀ n < m, component L.remainder n = 0)
    (hsign : SameStrictSign (L.effectiveValue Fplus m ε)
      (L.effectiveValue Fminus m ε)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      6*t^16*ε^2*δ^2 ≤ eval (Fplus.scaledPoint ε t) P →
        0 < eval (Fminus.scaledPoint ε t) P := by
  rcases hsign with ⟨hp, hm'⟩ | ⟨hp, hm'⟩
  · filter_upwards [eventually_pos_of_div_pow_tendsto m hm'
      (L.tendsto_eval_div_first Fminus ε hεm m hm hbelow)] with t ht
    exact fun _ => ht
  · filter_upwards [eventually_neg_of_div_pow_tendsto m hp
      (L.tendsto_eval_div_first Fplus ε hεp m hm hbelow)] with t ht
    intro hlarge
    have hn : 0 ≤ 6*t^16*ε^2*δ^2 := by positivity
    exact False.elim (not_le_of_gt ht (le_trans hn hlarge))

theorem eventually_transfer_zero {δ : ℝ}
    (Fplus : CorrectionFamily δ 1) (Fminus : CorrectionFamily δ (-1))
    (ε : ℝ) (hε0 : 0 < ε) (hδ : 0 < δ)
    (hεp : |ε| < Fplus.radius) (hεm : |ε| < Fminus.radius)
    (hthrough : ∀ n ≤ 16, component L.remainder n = 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      6*t^16*ε^2*δ^2 ≤ eval (Fplus.scaledPoint ε t) P →
        0 < eval (Fminus.scaledPoint ε t) P := by
  by_cases hc : 0 < L.commonCoefficient
  · have hlimit : 0 < L.commonCoefficient*ε^2*δ^2 := by positivity
    filter_upwards [eventually_pos_of_div_pow_tendsto 16 hlimit
      (L.tendsto_eval_div_zero Fminus ε hεm hthrough)] with t ht
    exact fun _ => ht
  · have hc' : L.commonCoefficient ≤ 0 := le_of_not_gt hc
    have hcoefficient : 0 < 6-L.commonCoefficient := by linarith
    have hgap : 0 < (6-L.commonCoefficient)*ε^2*δ^2 := by positivity
    have hlim : Tendsto
        (fun t : ℝ => (6*t^16*ε^2*δ^2-eval (Fplus.scaledPoint ε t) P)/t^16)
        (𝓝[>] 0) (𝓝 ((6-L.commonCoefficient)*ε^2*δ^2)) := by
      have hh := (tendsto_const_nhds (x := 6*ε^2*δ^2)).sub
        (L.tendsto_eval_div_zero Fplus ε hεp hthrough)
      have heq : 6*ε^2*δ^2-L.commonCoefficient*ε^2*δ^2 =
          (6-L.commonCoefficient)*ε^2*δ^2 := by ring
      rw [heq] at hh
      apply (tendsto_congr' ?_).2 hh
      filter_upwards [self_mem_nhdsWithin] with t htpos
      change 0 < t at htpos
      field_simp [ne_of_gt htpos]
    filter_upwards [eventually_pos_of_div_pow_tendsto 16 hgap hlim] with t ht
    intro hlarge
    exact False.elim (not_le_of_gt (sub_pos.mp ht) hlarge)

end LeafDecomposition

end

end PBCounterexample.Gram5
