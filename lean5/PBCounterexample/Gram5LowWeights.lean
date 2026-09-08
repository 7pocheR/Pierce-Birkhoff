import PBCounterexample.Gram5Variations

/-! An exhaustive coefficient description of every weight through sixteen. -/

namespace PBCounterexample.Gram5

open MvPolynomial
open scoped BigOperators

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

private theorem low_coordinate_succ_two : (2 : Fin 4).succ = (3 : Fin 5) := rfl
private theorem low_coordinate_succ_succ_two : (2 : Fin 3).succ.succ = (4 : Fin 5) := rfl
attribute [local simp] low_coordinate_succ_two low_coordinate_succ_succ_two

def lowExponentTuple (i : Fin 21) : Fin 5 → ℕ :=
  match i.val with
  | 0 => ![0, 0, 0, 0, 0]
  | 1 => ![1, 0, 0, 0, 0]
  | 2 => ![0, 1, 0, 0, 0]
  | 3 => ![0, 0, 1, 0, 0]
  | 4 => ![0, 0, 0, 1, 0]
  | 5 => ![0, 0, 0, 0, 1]
  | 6 => ![2, 0, 0, 0, 0]
  | 7 => ![1, 1, 0, 0, 0]
  | 8 => ![1, 0, 1, 0, 0]
  | 9 => ![0, 2, 0, 0, 0]
  | 10 => ![1, 0, 0, 1, 0]
  | 11 => ![0, 1, 1, 0, 0]
  | 12 => ![1, 0, 0, 0, 1]
  | 13 => ![0, 1, 0, 1, 0]
  | 14 => ![0, 0, 2, 0, 0]
  | 15 => ![3, 0, 0, 0, 0]
  | 16 => ![0, 1, 0, 0, 1]
  | 17 => ![0, 0, 1, 1, 0]
  | 18 => ![2, 1, 0, 0, 0]
  | 19 => ![0, 0, 1, 0, 1]
  | _ => ![0, 0, 0, 2, 0]

def lowExponent (i : Fin 21) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (lowExponentTuple i)

def lowWeight (i : Fin 21) : ℕ :=
  match i.val with
  | 0 => 0
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 8
  | 5 => 9
  | 6 => 10
  | 7 => 11
  | 8 => 12
  | 9 => 12
  | 10 => 13
  | 11 => 13
  | 12 => 14
  | 13 => 14
  | 14 => 14
  | 15 => 15
  | 16 => 15
  | 17 => 15
  | 18 => 16
  | 19 => 16
  | _ => 16

def lowMonomial (i : Fin 21) : Poly :=
  match i.val with
  | 0 => 1
  | 1 => a
  | 2 => b
  | 3 => c
  | 4 => d
  | 5 => e
  | 6 => a^2
  | 7 => a*b
  | 8 => a*c
  | 9 => b^2
  | 10 => a*d
  | 11 => b*c
  | 12 => a*e
  | 13 => b*d
  | 14 => c^2
  | 15 => a^3
  | 16 => b*e
  | 17 => c*d
  | 18 => a^2*b
  | 19 => c*e
  | _ => d^2

theorem lowExponent_injective : Function.Injective lowExponent := by
  have h : Function.Injective lowExponentTuple := by decide
  exact Finsupp.equivFunOnFinite.symm.injective.comp h

theorem weight_eq_coordinates (u : Fin 5 →₀ ℕ) :
    Finsupp.weight weights u = 5*u 0+6*u 1+7*u 2+8*u 3+9*u 4 := by
  rw [Finsupp.weight_eq_sum]
  norm_num [weights, Fin.sum_univ_succ, nsmul_eq_mul]
  omega

theorem lowExponent_weight (i : Fin 21) :
    Finsupp.weight weights (lowExponent i) = lowWeight i := by
  rw [weight_eq_coordinates]
  fin_cases i <;> norm_num [lowExponent, lowExponentTuple, lowWeight]

theorem lowExponent_weight_le (i : Fin 21) :
    Finsupp.weight weights (lowExponent i) ≤ 16 := by
  rw [lowExponent_weight]
  fin_cases i <;> norm_num [lowWeight]

set_option maxHeartbeats 400000 in
private theorem low_coordinate_cases (ua ub uc ud ue : ℕ)
    (hw : 5*ua+6*ub+7*uc+8*ud+9*ue ≤ 16) :
    (ua = 0 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 1 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 1 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 1 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 0 ∧ ud = 1 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 1) ∨
    (ua = 2 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 1 ∧ ub = 1 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 1 ∧ ub = 0 ∧ uc = 1 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 2 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 1 ∧ ub = 0 ∧ uc = 0 ∧ ud = 1 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 1 ∧ uc = 1 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 1 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 1) ∨
    (ua = 0 ∧ ub = 1 ∧ uc = 0 ∧ ud = 1 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 2 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 3 ∧ ub = 0 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 1 ∧ uc = 0 ∧ ud = 0 ∧ ue = 1) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 1 ∧ ud = 1 ∧ ue = 0) ∨
    (ua = 2 ∧ ub = 1 ∧ uc = 0 ∧ ud = 0 ∧ ue = 0) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 1 ∧ ud = 0 ∧ ue = 1) ∨
    (ua = 0 ∧ ub = 0 ∧ uc = 0 ∧ ud = 2 ∧ ue = 0) := by
  have ha : ua ≤ 3 := by omega
  have hb : ub ≤ 2 := by omega
  have hc : uc ≤ 2 := by omega
  have hd : ud ≤ 2 := by omega
  have he : ue ≤ 1 := by omega
  interval_cases ua <;> interval_cases ub <;> interval_cases uc <;>
    interval_cases ud <;> interval_cases ue <;> norm_num at *

set_option maxHeartbeats 400000 in
/-- There are no other exponent vectors of weight at most sixteen. -/
theorem low_exponent_cases (u : Fin 5 →₀ ℕ)
    (hu : Finsupp.weight weights u ≤ 16) : ∃ i : Fin 21, u = lowExponent i := by
  have hw : 5*u 0+6*u 1+7*u 2+8*u 3+9*u 4 ≤ 16 := by
    rwa [weight_eq_coordinates] at hu
  have hc := low_coordinate_cases (u 0) (u 1) (u 2) (u 3) (u 4) hw
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨0, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨1, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨2, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨3, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨4, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨5, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨6, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨7, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨8, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨9, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨10, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨11, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨12, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨13, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨14, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨15, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨16, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨17, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨18, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨19, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  · refine ⟨20, ?_⟩
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    ext j
    fin_cases j <;> norm_num [lowExponent, lowExponentTuple, h0, h1, h2, h3, h4] <;>
      first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

theorem monomial_lowExponent (i : Fin 21) :
    (monomial (lowExponent i) (1 : ℝ) : Poly) = lowMonomial i := by
  apply MvPolynomial.funext
  intro z
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  fin_cases i <;>
    norm_num [lowExponent, lowExponentTuple, lowMonomial, a, b, c, d, e,
      Fin.prod_univ_succ]

/-- A polynomial supported in these weights is reconstructed from all its
actual coefficients, without any restriction on their real values. -/
theorem sum_low_coefficients (P : Poly)
    (hP : ∀ u ∈ P.support, Finsupp.weight weights u ≤ 16) :
    P = ∑ i : Fin 21, monomial (lowExponent i) (coeff (lowExponent i) P) := by
  classical
  ext u
  by_cases hu : Finsupp.weight weights u ≤ 16
  · obtain ⟨i, rfl⟩ := low_exponent_cases u hu
    simp [coeff_sum, coeff_monomial, lowExponent_injective.eq_iff]
  · have hc : coeff u P = 0 := by
      by_contra hc
      exact hu (hP u (mem_support_iff.2 hc))
    have hne (i : Fin 21) : lowExponent i ≠ u := by
      intro heq
      exact hu (heq ▸ lowExponent_weight_le i)
    simp [coeff_sum, coeff_monomial, hne, hc]

theorem weighted_polynomial_low_formula (P : Poly) (m : ℕ)
    (hP : P.IsWeightedHomogeneous weights m) (hm : m ≤ 16) :
    P = ∑ i : Fin 21,
      C (if lowWeight i = m then coeff (lowExponent i) P else 0) * lowMonomial i := by
  calc
    P = ∑ i : Fin 21, monomial (lowExponent i) (coeff (lowExponent i) P) :=
      sum_low_coefficients P (fun u hu => (hP (mem_support_iff.1 hu)).le.trans hm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hc : coeff (lowExponent i) P =
          if lowWeight i = m then coeff (lowExponent i) P else 0 := by
        split_ifs with hi
        · rfl
        · exact hP.coeff_eq_zero _ (by simpa only [lowExponent_weight] using hi)
      rw [← monomial_lowExponent, C_mul_monomial, mul_one, ← hc]

theorem low_weight_totalDegree (P : Poly)
    (hP : ∀ u ∈ P.support, Finsupp.weight weights u ≤ 16) :
    P.totalDegree ≤ 3 := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro u hu
  have hw := hP u hu
  rw [weight_eq_coordinates] at hw
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  norm_num [Fin.sum_univ_succ]
  omega

end

end PBCounterexample.Gram5
