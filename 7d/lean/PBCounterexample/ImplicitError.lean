import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Error estimates for approximate implicit solutions

A normalized strict derivative in the unknown variables gives a uniform
estimate of the solution error by the equation residual. The estimate
transfers any finite-order asymptotic residual bound to an actual solution.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology NNReal

namespace PBCounterexample

variable {E Y X : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup Y]

/-- A linear approximation with error at most one half of the displacement
controls the displacement by twice the residual. -/
theorem norm_le_twice_of_half_error (v w : Y)
    (h : ‖w - v‖ ≤ (1 / 2 : ℝ) * ‖v‖) : ‖v‖ ≤ 2 * ‖w‖ := by
  have ht : ‖v‖ ≤ ‖w‖ + ‖w - v‖ := by
    calc
      ‖v‖ = ‖w - (w - v)‖ := by congr 1; abel
      _ ≤ ‖w‖ + ‖w - v‖ := norm_sub_le _ _
  linarith

variable [NormedSpace ℝ E] [NormedSpace ℝ Y]

/-- If two families tend to the same base point, one solves the equation,
and the derivative in the unknown variables is the identity at that point,
then their difference is eventually bounded by twice the residual of the
other family. No analyticity assumption is required. -/
theorem eventually_implicit_error_le_twice_residual
    {F : E × Y → Y} {D : E × Y →L[ℝ] Y} {t₀ : E} {y₀ : Y}
    (hF : HasStrictFDerivAt F D (t₀, y₀))
    (hD : ∀ v : Y, D (0, v) = v)
    {l : Filter X} {t : X → E} {a e : X → Y}
    (ht : Tendsto t l (𝓝 t₀)) (ha : Tendsto a l (𝓝 y₀))
    (he : Tendsto e l (𝓝 y₀))
    (hzero : ∀ᶠ x in l, F (t x, e x) = 0) :
    ∀ᶠ x in l, ‖a x - e x‖ ≤ 2 * ‖F (t x, a x)‖ := by
  obtain ⟨s, hs, hbound⟩ := hF.approximates_deriv_on_nhds
    (c := (1 / 2 : ℝ≥0)) (Or.inr (by norm_num))
  have hsa : ∀ᶠ x in l, (t x, a x) ∈ s := (ht.prodMk_nhds ha).eventually hs
  have hse : ∀ᶠ x in l, (t x, e x) ∈ s := (ht.prodMk_nhds he).eventually hs
  filter_upwards [hsa, hse, hzero] with x hax hex hz
  have hb : ‖F (t x, a x) - (a x - e x)‖ ≤
      (1 / 2 : ℝ) * ‖a x - e x‖ := by
    simpa [hz, hD, Prod.norm_def] using hbound (t x, a x) hax (t x, e x) hex
  exact norm_le_twice_of_half_error _ _ hb

/-- An approximate solution with a prescribed asymptotic residual order
has that same error order relative to an exact solution. -/
theorem implicit_error_isBigO_residual
    {F : E × Y → Y} {D : E × Y →L[ℝ] Y} {t₀ : E} {y₀ : Y}
    (hF : HasStrictFDerivAt F D (t₀, y₀))
    (hD : ∀ v : Y, D (0, v) = v)
    {l : Filter X} {t : X → E} {a e : X → Y}
    (ht : Tendsto t l (𝓝 t₀)) (ha : Tendsto a l (𝓝 y₀))
    (he : Tendsto e l (𝓝 y₀))
    (hzero : ∀ᶠ x in l, F (t x, e x) = 0) :
    (fun x => a x - e x) =O[l] (fun x => F (t x, a x)) := by
  exact IsBigO.of_bound 2
    (eventually_implicit_error_le_twice_residual hF hD ht ha he hzero)

end PBCounterexample
