import PBCounterexample.QuadraticForms
import Mathlib.Tactic

/-! Coefficient representations of homogeneous linear and quadratic polynomials. -/

noncomputable section

namespace PBCounterexample.LowDegreeCoordinates

open MvPolynomial
open scoped BigOperators

theorem homogeneous_eq_sum_monomials
    {σ ι : Type*} [Fintype ι] (d : ι → (σ →₀ ℕ))
    (hd : Function.Injective d) (n : ℕ)
    (hcomplete : ∀ m : σ →₀ ℕ, m.degree = n → ∃ i, d i = m)
    (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous n) :
    p = ∑ i, monomial (d i) (p.coeff (d i)) := by
  classical
  ext m
  by_cases hm : ∃ i, d i = m
  · obtain ⟨i, rfl⟩ := hm
    simp [coeff_sum, coeff_monomial, hd.eq_iff]
  · have hdegree : m.degree ≠ n := fun he => hm (hcomplete m he)
    rw [hp.coeff_eq_zero hdegree, coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_monomial, ite_eq_right (fun he => hm ⟨i, he⟩)]

theorem homogeneous_one_eq_sum
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous 1) :
    p = ∑ i, C (p.coeff (Finsupp.single i 1)) * X i := by
  have hcomplete : ∀ m : σ →₀ ℕ, m.degree = 1 →
      ∃ i, Finsupp.single i 1 = m := by
    intro m hm
    have hr : m ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hm
    exact hr
  simpa only [C_mul_X_eq_monomial] using
    homogeneous_eq_sum_monomials (fun i : σ => Finsupp.single i 1)
      (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)) 1 hcomplete p hp

theorem exponent_degree_two
    {σ : Type*} (m : σ →₀ ℕ) (hm : m.degree = 2) :
    ∃ i j, m = Finsupp.single i 1 + Finsupp.single j 1 := by
  rcases QuadraticDecomposition.exponent_degree_le_two m hm.le with
    hz | ⟨i, hi⟩ | htwo
  · simp [hz] at hm
  · simp [hi] at hm
  · exact htwo

theorem homogeneous_two_eq_sum
    {σ ι : Type*} [LinearOrder σ] [Fintype ι]
    (pairs : ι → σ × σ)
    (hinj : Function.Injective (fun i =>
      Finsupp.single (pairs i).1 1 + Finsupp.single (pairs i).2 1))
    (hcomplete : ∀ i j : σ, i ≤ j → ∃ k, pairs k = (i,j))
    (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous 2) :
    p = ∑ i, C (p.coeff
      (Finsupp.single (pairs i).1 1 + Finsupp.single (pairs i).2 1)) *
        (X (pairs i).1 * X (pairs i).2) := by
  have hdegrees : ∀ m : σ →₀ ℕ, m.degree = 2 →
      ∃ k, Finsupp.single (pairs k).1 1 + Finsupp.single (pairs k).2 1 = m := by
    intro m hm
    obtain ⟨i, j, rfl⟩ := exponent_degree_two m hm
    rcases le_total i j with hij | hji
    · obtain ⟨k, hk⟩ := hcomplete i j hij
      exact ⟨k, by simp [hk]⟩
    · obtain ⟨k, hk⟩ := hcomplete j i hji
      exact ⟨k, by simp [hk, add_comm]⟩
  have he := homogeneous_eq_sum_monomials
    (fun i => Finsupp.single (pairs i).1 1 + Finsupp.single (pairs i).2 1)
    hinj 2 hdegrees p hp
  calc
    p = ∑ i, monomial
        (Finsupp.single (pairs i).1 1 + Finsupp.single (pairs i).2 1)
        (p.coeff (Finsupp.single (pairs i).1 1 + Finsupp.single (pairs i).2 1)) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [X, X, monomial_mul_monomial, one_mul, C_mul_monomial, mul_one]

end PBCounterexample.LowDegreeCoordinates
