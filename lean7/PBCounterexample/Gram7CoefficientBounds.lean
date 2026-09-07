import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Polynomial

/-! Bounds at zero for polynomial residuals divisible by a power of the variable. -/

namespace PBCounterexample.Gram7Coefficient

open Polynomial Filter Asymptotics
open scoped Topology

theorem eval_isBigO_pow_of_dvd {p : ℝ[X]} {n : ℕ} (h : X^n ∣ p) :
    p.eval =O[𝓝 (0 : ℝ)] (fun t : ℝ => t^n) := by
  obtain ⟨q, rfl⟩ := h
  have hq := (q.continuous.tendsto 0).isBigO_one ℝ
  simpa using (isBigO_refl (fun t : ℝ => t^n) (𝓝 0)).mul hq

end PBCounterexample.Gram7Coefficient
