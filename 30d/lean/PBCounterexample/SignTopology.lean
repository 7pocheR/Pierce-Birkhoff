import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Real.Sign
import Mathlib.Order.Filter.Finite

/-!
# Stability of finitely many polynomial signs along two paths
-/

namespace PBCounterexample

open Filter Topology

theorem eventually_real_sign_eq_of_tendsto
    {α : Type*} {l : Filter α} {g : α → ℝ} {c : ℝ}
    (hg : Tendsto g l (𝓝 c)) (hc : c ≠ 0) :
    ∀ᶠ a in l, Real.sign (g a) = Real.sign c := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · have he : ∀ᶠ a in l, g a < 0 := hg.eventually (isOpen_Iio.mem_nhds hc)
    filter_upwards [he] with a ha
    rw [Real.sign_of_neg ha, Real.sign_of_neg hc]
  · have he : ∀ᶠ a in l, 0 < g a := hg.eventually (isOpen_Ioi.mem_nhds hc)
    filter_upwards [he] with a ha
    rw [Real.sign_of_pos ha, Real.sign_of_pos hc]

theorem exists_positive_time_same_polynomial_signs
    {σ : Type*} (S : Finset (MvPolynomial σ ℝ))
    (a b : ℝ → (σ → ℝ)) (o : σ → ℝ)
    (ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 o))
    (hb : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 o))
    (hS : ∀ p ∈ S,
      (∀ t, MvPolynomial.eval (a t) p = MvPolynomial.eval (b t) p) ∨
      MvPolynomial.eval o p ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ p ∈ S,
      Real.sign (MvPolynomial.eval (a t) p) = Real.sign (MvPolynomial.eval (b t) p) := by
  have heach : ∀ p ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Real.sign (MvPolynomial.eval (a t) p) = Real.sign (MvPolynomial.eval (b t) p) := by
    intro p hp
    rcases hS p hp with heq | hne
    · exact Filter.Eventually.of_forall fun t => congrArg Real.sign (heq t)
    · have hap := eventually_real_sign_eq_of_tendsto
        ((MvPolynomial.continuous_eval p).tendsto o |>.comp ha) hne
      have hbp := eventually_real_sign_eq_of_tendsto
        ((MvPolynomial.continuous_eval p).tendsto o |>.comp hb) hne
      filter_upwards [hap, hbp] with t hta htb
      exact hta.trans htb.symm
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ S,
      Real.sign (MvPolynomial.eval (a t) p) = Real.sign (MvPolynomial.eval (b t) p) :=
    (Filter.eventually_all_finset S).mpr heach
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact (hpositive.and hall).exists

end PBCounterexample
