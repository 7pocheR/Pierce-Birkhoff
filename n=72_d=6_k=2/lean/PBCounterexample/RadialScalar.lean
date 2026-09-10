import Mathlib.Data.Real.Sign
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Clamping and quadratic radial limits

Clamping a real number to `[-1, 1]` preserves minimum, maximum, and its
comparison with zero. It permits radial limits to be taken in the real line
even when individual normalized polynomial leaves diverge.
-/

namespace PBCounterexample.Radial

open Filter Topology

def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem continuous_clip : Continuous clip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem monotone_clip : Monotone clip := by
  intro x y h
  exact max_le_max le_rfl (min_le_min le_rfl h)

theorem clip_max (x y : ℝ) : clip (max x y) = max (clip x) (clip y) :=
  monotone_clip.map_max

theorem clip_min (x y : ℝ) : clip (min x y) = min (clip x) (clip y) :=
  monotone_clip.map_min

@[simp] theorem clip_zero : clip 0 = 0 := by
  norm_num [clip]

theorem clip_eq_one_of_one_le {x : ℝ} (h : 1 ≤ x) : clip x = 1 := by
  simp [clip, min_eq_left h]

theorem clip_eq_neg_one_of_le {x : ℝ} (h : x ≤ -1) : clip x = -1 := by
  have hx : x ≤ 1 := le_trans h (by norm_num)
  simp [clip, min_eq_right hx, max_eq_left h]

theorem clip_pos_iff (x : ℝ) : 0 < clip x ↔ 0 < x := by
  simp [clip, lt_max_iff, lt_min_iff]

theorem clip_neg_iff (x : ℝ) : clip x < 0 ↔ x < 0 := by
  simp [clip, max_lt_iff, min_lt_iff]

theorem clip_eq_zero_iff (x : ℝ) : clip x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have := (clip_neg_iff x).2 hx
      linarith
    · exact hx
    · have := (clip_pos_iff x).2 hx
      linarith
  · rintro rfl
    exact clip_zero

theorem sign_clip (x : ℝ) : Real.sign (clip x) = Real.sign x := by
  simp only [Real.sign, clip_neg_iff, clip_pos_iff]

theorem monotone_realSign : Monotone Real.sign := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [Real.sign_of_neg, Real.sign_of_pos] <;> linarith

theorem tendsto_clip_quadratic_of_constant_pos (a b : ℝ) (r : ℝ → ℝ)
    (hr : ContinuousAt r 0) (ha : 0 < a) :
    Tendsto (fun t : ℝ => clip ((a + t * (b + t * r t)) / t ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun t : ℝ => a + t * (b + t * r t) - t ^ 2) 0 := by
    fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < a + t * (b + t * r t) - t ^ 2 :=
    (hc.tendsto.eventually (eventually_gt_nhds (by simpa using ha))).filter_mono
      nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
  apply clip_eq_one_of_one_le
  apply (le_div_iff₀ (sq_pos_of_pos htpos)).2
  nlinarith

theorem tendsto_clip_quadratic_of_constant_neg (a b : ℝ) (r : ℝ → ℝ)
    (hr : ContinuousAt r 0) (ha : a < 0) :
    Tendsto (fun t : ℝ => clip ((a + t * (b + t * r t)) / t ^ 2))
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hc : ContinuousAt (fun t : ℝ => a + t * (b + t * r t) + t ^ 2) 0 := by
    fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, a + t * (b + t * r t) + t ^ 2 < 0 :=
    (hc.tendsto.eventually (eventually_lt_nhds (by simpa using ha))).filter_mono
      nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
  apply clip_eq_neg_one_of_le
  apply (div_le_iff₀ (sq_pos_of_pos htpos)).2
  nlinarith

theorem tendsto_clip_quadratic_of_linear_pos (b : ℝ) (r : ℝ → ℝ)
    (hr : ContinuousAt r 0) (hb : 0 < b) :
    Tendsto (fun t : ℝ => clip ((t * (b + t * r t)) / t ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun t : ℝ => b + t * r t - t) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < b + t * r t - t :=
    (hc.tendsto.eventually (eventually_gt_nhds (by simpa using hb))).filter_mono
      nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
  apply clip_eq_one_of_one_le
  apply (le_div_iff₀ (sq_pos_of_pos htpos)).2
  have hp := mul_pos htpos ht
  nlinarith

theorem tendsto_clip_quadratic_of_linear_neg (b : ℝ) (r : ℝ → ℝ)
    (hr : ContinuousAt r 0) (hb : b < 0) :
    Tendsto (fun t : ℝ => clip ((t * (b + t * r t)) / t ^ 2))
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hc : ContinuousAt (fun t : ℝ => b + t * r t + t) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, b + t * r t + t < 0 :=
    (hc.tendsto.eventually (eventually_lt_nhds (by simpa using hb))).filter_mono
      nhdsWithin_le_nhds
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
  apply clip_eq_neg_one_of_le
  apply (div_le_iff₀ (sq_pos_of_pos htpos)).2
  have hp := mul_neg_of_pos_of_neg htpos ht
  nlinarith

theorem tendsto_clip_quadratic_of_low_coefficients_zero (r : ℝ → ℝ)
    (hr : ContinuousAt r 0) :
    Tendsto (fun t : ℝ => clip ((t * (t * r t)) / t ^ 2))
      (𝓝[>] 0) (𝓝 (clip (r 0))) := by
  have hc : ContinuousAt (fun t => clip (r t)) 0 := continuous_clip.continuousAt.comp hr
  apply (tendsto_congr' ?_).2 (hc.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t htpos
  congr 1
  have ht : t ≠ 0 := ne_of_gt htpos
  field_simp

end PBCounterexample.Radial
