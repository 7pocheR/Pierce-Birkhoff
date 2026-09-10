import PBCounterexample.RationalSubstitution
import PBCounterexample.PolynomialTopology

/-!
# Simultaneous nonvanishing under rational polynomial substitution

Nonzero rational functions with a common denominator have a common
nonvanishing point in every nonempty real open set on which the
denominator does not vanish.
-/

namespace PBCounterexample

open MvPolynomial

theorem exists_all_rational_evals_ne_zero_in_open
    {σ τ ι : Type*} [Finite τ]
    (S : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (d : MvPolynomial τ ℝ) (n : σ → MvPolynomial τ ℝ)
    (hp : ∀ i ∈ S, ∃ z : τ → ℝ,
      eval z d ≠ 0 ∧ eval (fun c => eval z (n c) / eval z d) (p i) ≠ 0)
    {s : Set (τ → ℝ)} (hs : IsOpen s) (hne : s.Nonempty)
    (hd : ∀ z ∈ s, eval z d ≠ 0) :
    ∃ z ∈ s, ∀ i ∈ S, eval (fun c => eval z (n c) / eval z d) (p i) ≠ 0 := by
  classical
  choose q k hq using fun i => polynomial_substitution_clear_denominator (p i) d n
  have hqn : ∀ i ∈ S, q i ≠ 0 := by
    intro i hi
    obtain ⟨z, hzd, hzp⟩ := hp i hi
    intro hzero
    have h := hq i z hzd
    rw [hzero, map_zero] at h
    exact (mul_ne_zero (pow_ne_zero _ hzd) hzp) h.symm
  obtain ⟨z, hz, hzq⟩ := exists_all_evals_ne_zero_in_open S q hqn hs hne
  refine ⟨z, hz, ?_⟩
  intro i hi hzero
  have h := hq i z (hd z hz)
  rw [hzero, mul_zero] at h
  exact hzq i hi h

end PBCounterexample
