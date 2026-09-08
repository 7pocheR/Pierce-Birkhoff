import PBCounterexample.Gram5LowWeights
import PBCounterexample.Gram5Differential

/-! The complete low-weight kernel over arbitrary real coefficients. -/

namespace PBCounterexample.Gram5

open MvPolynomial
open scoped BigOperators

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

theorem eval_lowMonomial (i : Fin 21) : eval basePoint (lowMonomial i) = 1 := by
  fin_cases i <;> norm_num [lowMonomial, a, b, c, d, e, basePoint]

private theorem single_monomial_zero (P : Poly) (i : Fin 21) (r : ℝ)
    (hP : P = C r*lowMonomial i) (hzero : eval basePoint P = 0) : P = 0 := by
  have hr : r = 0 := by
    simpa only [hP, map_mul, eval_C, eval_lowMonomial, mul_one] using hzero
  simp only [hP, hr, map_zero, zero_mul]

set_option maxHeartbeats 400000 in
private theorem low_weight_kernel_of_formula (P : Poly) (r : Fin 21 → ℝ) (m : ℕ)
    (hm : m ≤ 16)
    (hp : P = ∑ i : Fin 21, C (if lowWeight i = m then r i else 0)*lowMonomial i)
    (hvalue : eval basePoint P = 0) (hderiv : differential P normalDirection = 0) :
    P = C (if m = 14 then r 12 else 0)*invariantA +
    C (if m = 15 then r 15 else 0)*invariantB +
    C (if m = 16 then r 18 else 0)*invariantW := by
  norm_num [Fin.sum_univ_succ, lowWeight, lowMonomial] at hp
  interval_cases m
  all_goals norm_num at hp ⊢
  · exact single_monomial_zero P 0 (r 0) (by simpa [lowMonomial] using hp) hvalue
  · exact hp
  · exact hp
  · exact hp
  · exact hp
  · exact single_monomial_zero P 1 (r 1) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 2 (r 2) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 3 (r 3) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 4 (r 4) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 5 (r 5) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 6 (r 6) (by simpa [lowMonomial] using hp) hvalue
  · exact single_monomial_zero P 7 (r 7) (by simpa [lowMonomial] using hp) hvalue
  · change P = C (r 8)*(a*c) + C (r 9)*b^2 at hp
    have hv := congrArg (eval basePoint) hp
    have hn := congrArg (fun Q : Poly => differential Q normalDirection) hp
    rw [hvalue] at hv
    rw [hderiv] at hn
    norm_num [a, b, c, basePoint, normalDirection] at hv hn
    have h8 : r 8 = 0 := by linarith
    have h9 : r 9 = 0 := by linarith
    simpa [h8, h9] using hp
  · change P = C (r 10)*(a*d) + C (r 11)*(b*c) at hp
    have hv := congrArg (eval basePoint) hp
    have hn := congrArg (fun Q : Poly => differential Q normalDirection) hp
    rw [hvalue] at hv
    rw [hderiv] at hn
    norm_num [a, b, c, d, basePoint, normalDirection] at hv hn
    have h10 : r 10 = 0 := by linarith
    have h11 : r 11 = 0 := by linarith
    simpa [h10, h11] using hp
  · change P = C (r 12)*(a*e) + (C (r 13)*(b*d) + C (r 14)*c^2) at hp
    have hv := congrArg (eval basePoint) hp
    have hn := congrArg (fun Q : Poly => differential Q normalDirection) hp
    rw [hvalue] at hv
    rw [hderiv] at hn
    norm_num [a, b, c, d, e, basePoint, normalDirection] at hv hn
    have h13 : r 13 = -4*r 12 := by linarith
    have h14 : r 14 = 3*r 12 := by linarith
    rw [hp, h13, h14]
    simp only [invariantA, map_mul, map_neg, map_ofNat]
    ring
  · change P = C (r 15)*a^3 + (C (r 16)*(b*e) + C (r 17)*(c*d)) at hp
    have hv := congrArg (eval basePoint) hp
    have hn := congrArg (fun Q : Poly => differential Q normalDirection) hp
    rw [hvalue] at hv
    rw [hderiv] at hn
    norm_num [a, b, c, d, e, basePoint, normalDirection] at hv hn
    have h16 : r 16 = -3*r 15 := by linarith
    have h17 : r 17 = 2*r 15 := by linarith
    rw [hp, h16, h17]
    simp only [invariantB, map_mul, map_neg, map_ofNat]
    ring
  · change P = C (r 18)*(a^2*b) + (C (r 19)*(c*e) + C (r 20)*d^2) at hp
    have hv := congrArg (eval basePoint) hp
    have hn := congrArg (fun Q : Poly => differential Q normalDirection) hp
    rw [hvalue] at hv
    rw [hderiv] at hn
    norm_num [a, b, c, d, e, basePoint, normalDirection] at hv hn
    have h19 : r 19 = -4*r 18 := by linarith
    have h20 : r 20 = 3*r 18 := by linarith
    rw [hp, h19, h20]
    simp only [invariantW, map_mul, map_neg, map_ofNat]
    ring

/-- Simultaneous vanishing of value and normal derivative determines every
coefficient in weights at most sixteen. -/
theorem low_weight_kernel_formula (P : Poly) (m : ℕ)
    (hP : P.IsWeightedHomogeneous weights m) (hm : m ≤ 16)
    (hvalue : eval basePoint P = 0) (hderiv : differential P normalDirection = 0) :
    P = C (if m = 14 then coeff (lowExponent 12) P else 0)*invariantA +
      C (if m = 15 then coeff (lowExponent 15) P else 0)*invariantB +
      C (if m = 16 then coeff (lowExponent 18) P else 0)*invariantW :=
  low_weight_kernel_of_formula P (fun i => coeff (lowExponent i) P) m hm
    (weighted_polynomial_low_formula P m hP hm) hvalue hderiv

def IsExceptional (m : ℕ) (P : Poly) : Prop :=
  P = 0 ∨
    (m = 14 ∧ ∃ r : ℝ, P = C r*invariantA) ∨
    (m = 15 ∧ ∃ r : ℝ, P = C r*invariantB) ∨
    (m = 16 ∧ ∃ r : ℝ, P = C r*invariantW)

theorem isExceptional_of_value_derivative_zero (P : Poly) (m : ℕ)
    (hP : P.IsWeightedHomogeneous weights m) (hm : m ≤ 16)
    (hvalue : eval basePoint P = 0) (hderiv : differential P normalDirection = 0) :
    IsExceptional m P := by
  have hp := low_weight_kernel_formula P m hP hm hvalue hderiv
  by_cases h14 : m = 14
  · right; left
    refine ⟨h14, coeff (lowExponent 12) P, ?_⟩
    simpa [h14] using hp
  by_cases h15 : m = 15
  · right; right; left
    refine ⟨h15, coeff (lowExponent 15) P, ?_⟩
    simpa [h15] using hp
  by_cases h16 : m = 16
  · right; right; right
    refine ⟨h16, coeff (lowExponent 18) P, ?_⟩
    simpa [h16] using hp
  left
  simpa [h14, h15, h16] using hp

theorem value_or_derivative_ne_zero_of_notExceptional (P : Poly) (m : ℕ)
    (hP : P.IsWeightedHomogeneous weights m) (hm : m ≤ 16)
    (hne : ¬ IsExceptional m P) :
    eval basePoint P ≠ 0 ∨ differential P normalDirection ≠ 0 := by
  by_contra h
  push_neg at h
  exact hne (isExceptional_of_value_derivative_zero P m hP hm h.1 h.2)

end

end PBCounterexample.Gram5
