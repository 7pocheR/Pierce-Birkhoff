import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp

/-!
# Weighted scaling of arbitrary real polynomials

The weights are arbitrary natural numbers. The polynomial and its real
coefficients are unrestricted. A finite weighted decomposition controls
evaluation along a scaled base point that itself converges.
-/

namespace PBCounterexample.WeightedPolynomial

open Filter MvPolynomial
open scoped BigOperators Topology

noncomputable section

variable {σ : Type*}

def scale (w : σ → ℕ) (t : ℝ) (z : σ → ℝ) : σ → ℝ :=
  fun i => t ^ (w i) * z i

theorem eval_scale_of_weightedHomogeneous {w : σ → ℕ}
    {p : MvPolynomial σ ℝ} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (z : σ → ℝ) (t : ℝ) :
    eval (scale w t z) p = t ^ n * eval z p := by
  classical
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : (∑ i ∈ d.support, w i * d i) = n := by
    simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, nsmul_eq_mul, mul_comm] using
      hp (MvPolynomial.mem_support_iff.1 hd)
  simp only [scale, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd']
  ring

/-- A finite sum containing every occurring weight equals the original
polynomial, including when the polynomial is zero. -/
theorem sum_components_upto (w : σ → ℕ) (p : MvPolynomial σ ℝ)
    (N : ℕ) (hN : p.weightedTotalDegree w < N) :
    (∑ n ∈ Finset.range N, weightedHomogeneousComponent w n p) = p := by
  classical
  ext d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  by_cases hd : coeff d p = 0
  · simp [hd]
  · have hmem : Finsupp.weight w d < N :=
      lt_of_le_of_lt (le_weightedTotalDegree w (mem_support_iff.2 hd)) hN
    simp [Finset.mem_range, hmem]

theorem eval_scale_eq_sum (w : σ → ℕ) (p : MvPolynomial σ ℝ)
    (N : ℕ) (hN : p.weightedTotalDegree w < N) (z : σ → ℝ) (t : ℝ) :
    eval (scale w t z) p =
      ∑ n ∈ Finset.range N, t ^ n * eval z (weightedHomogeneousComponent w n p) := by
  calc
    eval (scale w t z) p =
        ∑ n ∈ Finset.range N, eval (scale w t z)
          (weightedHomogeneousComponent w n p) := by
      rw [← map_sum, sum_components_upto w p N hN]
    _ = _ := Finset.sum_congr rfl fun n _ =>
      eval_scale_of_weightedHomogeneous
        (weightedHomogeneousComponent_isWeightedHomogeneous n p) z t

/-- Vanishing lower components allow division by a power of the scaling
parameter without negative exponents in the resulting finite sum. -/
theorem eval_scale_div_eq_sum (w : σ → ℕ) (p : MvPolynomial σ ℝ)
    (m N : ℕ) (hN : p.weightedTotalDegree w < N)
    (hbelow : ∀ n < m, weightedHomogeneousComponent w n p = 0)
    (z : σ → ℝ) (t : ℝ) (ht : t ≠ 0) :
    eval (scale w t z) p / t ^ m =
      ∑ n ∈ Finset.range N,
        t ^ (n - m) * eval z (weightedHomogeneousComponent w n p) := by
  rw [eval_scale_eq_sum w p N hN, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hnm : n < m
  · simp [hbelow n hnm]
  · have hmn : m ≤ n := Nat.le_of_not_gt hnm
    have hp : t ^ n = t ^ (n - m) * t ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [hp]
    field_simp [ht]

/-- The first permitted weighted component is the normalized limit, even
when the base point varies with the positive scaling parameter. -/
theorem tendsto_eval_scale_div (w : σ → ℕ) (p : MvPolynomial σ ℝ)
    (m : ℕ) (hbelow : ∀ n < m, weightedHomogeneousComponent w n p = 0)
    {v : ℝ → σ → ℝ} {v₀ : σ → ℝ}
    (hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 v₀)) :
    Tendsto (fun t : ℝ => eval (scale w t (v t)) p / t ^ m)
      (𝓝[>] 0) (𝓝 (eval v₀ (weightedHomogeneousComponent w m p))) := by
  classical
  let N := p.weightedTotalDegree w + m + 1
  have hN : p.weightedTotalDegree w < N := by dsimp [N]; omega
  have hmN : m < N := by dsimp [N]; omega
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hvp (n : ℕ) :
      Tendsto (fun t => eval (v t) (weightedHomogeneousComponent w n p))
        (𝓝[>] (0 : ℝ)) (𝓝 (eval v₀ (weightedHomogeneousComponent w n p))) :=
    (MvPolynomial.continuous_eval _).continuousAt.tendsto.comp hv
  have hterm (n : ℕ) :
      Tendsto (fun t : ℝ => t ^ (n - m) *
        eval (v t) (weightedHomogeneousComponent w n p))
        (𝓝[>] 0)
        (𝓝 (if n = m then eval v₀ (weightedHomogeneousComponent w m p) else 0)) := by
    by_cases hnm : n < m
    · simpa [hbelow n hnm, ne_of_lt hnm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
          (𝓝[>] 0) (𝓝 0))
    · by_cases heq : n = m
      · subst n
        simpa using hvp m
      · have hpos : 0 < n - m := by omega
        have hpow : Tendsto (fun t : ℝ => t ^ (n - m))
            (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
          simpa [zero_pow (ne_of_gt hpos)] using ht.pow (n - m)
        simpa [heq] using hpow.mul (hvp n)
  have hsum := tendsto_finsetSum (Finset.range N) (fun n _ => hterm n)
  have hsum' :
      Tendsto (fun t : ℝ => ∑ n ∈ Finset.range N, t ^ (n - m) *
        eval (v t) (weightedHomogeneousComponent w n p))
        (𝓝[>] 0) (𝓝 (eval v₀ (weightedHomogeneousComponent w m p))) := by
    simpa [Finset.mem_range, hmN] using hsum
  apply (tendsto_congr' ?_).2 hsum'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  exact eval_scale_div_eq_sum w p m N hN hbelow (v t) t (ne_of_gt htpos)

/-- Every strictly higher weighted term is negligible after normalization;
there is no restriction on the polynomial's highest weight or degree. -/
theorem tendsto_eval_scale_div_zero (w : σ → ℕ) (p : MvPolynomial σ ℝ)
    (m : ℕ) (hthrough : ∀ n ≤ m, weightedHomogeneousComponent w n p = 0)
    {v : ℝ → σ → ℝ} {v₀ : σ → ℝ}
    (hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 v₀)) :
    Tendsto (fun t : ℝ => eval (scale w t (v t)) p / t ^ m)
      (𝓝[>] 0) (𝓝 0) := by
  simpa [hthrough m le_rfl] using
    tendsto_eval_scale_div w p m (fun n hn => hthrough n hn.le) hv

end

end PBCounterexample.WeightedPolynomial
