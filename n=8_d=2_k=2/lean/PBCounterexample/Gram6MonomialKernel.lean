import PBCounterexample.Gram6QuadraticCoordinates

/-! The complete quadratic kernel on the monomial curve and its tangent. -/

namespace PBCounterexample.Gram6

open MvPolynomial
open scoped BigOperators

noncomputable def tangentQuadratic : Fin 3 → MvPolynomial (Fin 6) ℝ := ![
  X 0 * X 4 - C 4 * (X 1 * X 3) + C 3 * (X 2 * X 2),
  X 0 * X 5 - C 3 * (X 1 * X 4) + C 2 * (X 2 * X 3),
  X 1 * X 5 - C 4 * (X 2 * X 4) + C 3 * (X 3 * X 3)]

private theorem kernel_sum_fin21 {α : Type*} [AddCommMonoid α] (f : Fin 21 → α) :
    ∑ i, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 := by
  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add] <;> rfl

private theorem kernel_monomial_coeff_0 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 0 = c 0 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change c 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 0
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_1 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 1 = c 1 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + c 1 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 1
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_2 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 2 = c 2 + c 6 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + c 2 + 0 + 0 + 0 + c 6 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 2 + c 6
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_3 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 3 = c 3 + c 7 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + c 3 + 0 + 0 + 0 + c 7 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 3 + c 7
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_4 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 4 = c 4 + c 8 + c 11 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + c 4 + 0 + 0 + 0 + c 8 + 0 + 0 + c 11 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 4 + c 8 + c 11
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_5 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 5 = c 5 + c 9 + c 12 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + c 5 + 0 + 0 + 0 + c 9 + 0 + 0 + c 12 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 5 + c 9 + c 12
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_6 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 6 = c 10 + c 13 + c 15 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 10 + 0 + 0 + c 13 + 0 + c 15 + 0 + 0 + 0 + 0 + 0 = c 10 + c 13 + c 15
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_7 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 7 = c 14 + c 16 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 14 + 0 + c 16 + 0 + 0 + 0 + 0 = c 14 + c 16
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_8 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 8 = c 17 + c 18 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 17 + c 18 + 0 + 0 = c 17 + c 18
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_9 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 9 = c 19 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 19 + 0 = c 19
  simp only [zero_add, add_zero]

private theorem kernel_monomial_coeff_10 (c : Fin 21 → ℝ) :
    (quadraticAlongMonomial c).coeff 10 = c 20 := by
  rw [quadraticAlongMonomial_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 20 = c 20
  simp only [zero_add, add_zero]

private theorem kernel_tangent_coeff_0 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 0 = c 6 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change c 0 * ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) + c 1 * ((0 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + c 6 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = c 6
  norm_num <;> ring

private theorem kernel_tangent_coeff_1 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 1 = 2 * c 7 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + c 2 * ((0 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + c 7 * ((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 2 * c 7
  norm_num <;> ring

private theorem kernel_tangent_coeff_2 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 2 = 3 * c 8 + 4 * c 11 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + c 3 * ((0 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + c 8 * ((1 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) + 0 + 0 + c 11 * ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 3 * c 8 + 4 * c 11
  norm_num <;> ring

private theorem kernel_tangent_coeff_3 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 3 = 4 * c 9 + 6 * c 12 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + c 4 * ((0 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + c 9 * ((1 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) + 0 + 0 + c 12 * ((2 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 4 * c 9 + 6 * c 12
  norm_num <;> ring

private theorem kernel_tangent_coeff_4 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 4 = 5 * c 10 + 8 * c 13 + 9 * c 15 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + c 5 * ((0 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + c 10 * ((1 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) + 0 + 0 + c 13 * ((2 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) + 0 + c 15 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) + 0 + 0 + 0 + 0 + 0 = 5 * c 10 + 8 * c 13 + 9 * c 15
  norm_num <;> ring

private theorem kernel_tangent_coeff_5 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 5 = 10 * c 14 + 12 * c 16 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 14 * ((2 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) + 0 + c 16 * ((3 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) + 0 + 0 + 0 + 0 = 10 * c 14 + 12 * c 16
  norm_num <;> ring

private theorem kernel_tangent_coeff_6 (c : Fin 21 → ℝ) :
    (quadraticAlongTangent c).coeff 6 = 15 * c 17 + 16 * c 18 := by
  rw [quadraticAlongTangent_coeff, kernel_sum_fin21]
  change 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + c 17 * ((3 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) + c 18 * ((4 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) + 0 + 0 = 15 * c 17 + 16 * c 18
  norm_num <;> ring

private theorem kernel_solve_weight4 (a x y : ℝ)
    (hs : a + x + y = 0) (ht : 3 * x + 4 * y = 0) :
    x = -4 * a ∧ y = 3 * a := by
  constructor <;> linarith only [hs, ht]

private theorem kernel_solve_weight5 (a x y : ℝ)
    (hs : a + x + y = 0) (ht : 4 * x + 6 * y = 0) :
    x = -3 * a ∧ y = 2 * a := by
  constructor <;> linarith only [hs, ht]

private theorem kernel_solve_weight6 (a x y : ℝ)
    (hs : a + x + y = 0) (ht : 5 * a + 8 * x + 9 * y = 0) :
    x = -4 * a ∧ y = 3 * a := by
  constructor <;> linarith only [hs, ht]

private theorem kernel_solve_weight7 (x y : ℝ)
    (hs : x + y = 0) (ht : 10 * x + 12 * y = 0) :
    x = 0 ∧ y = 0 := by
  constructor <;> linarith only [hs, ht]

private theorem kernel_solve_weight8 (x y : ℝ)
    (hs : x + y = 0) (ht : 15 * x + 16 * y = 0) :
    x = 0 ∧ y = 0 := by
  constructor <;> linarith only [hs, ht]

private theorem kernel_coefficients (c : Fin 21 → ℝ)
    (hs : quadraticAlongMonomial c = 0) (ht : quadraticAlongTangent c = 0) :
    c = ![0, 0, 0, 0, c 4, c 5, 0, 0, -4 * c 4, -3 * c 5, c 10,
      3 * c 4, 2 * c 5, -4 * c 10, 0, 3 * c 10, 0, 0, 0, 0, 0] := by
  have s0 : c 0 = 0 := by
    simpa only [kernel_monomial_coeff_0, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 0) hs
  have s1 : c 1 = 0 := by
    simpa only [kernel_monomial_coeff_1, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 1) hs
  have s2 : c 2 + c 6 = 0 := by
    simpa only [kernel_monomial_coeff_2, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 2) hs
  have s3 : c 3 + c 7 = 0 := by
    simpa only [kernel_monomial_coeff_3, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 3) hs
  have s4 : c 4 + c 8 + c 11 = 0 := by
    simpa only [kernel_monomial_coeff_4, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 4) hs
  have s5 : c 5 + c 9 + c 12 = 0 := by
    simpa only [kernel_monomial_coeff_5, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 5) hs
  have s6 : c 10 + c 13 + c 15 = 0 := by
    simpa only [kernel_monomial_coeff_6, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 6) hs
  have s7 : c 14 + c 16 = 0 := by
    simpa only [kernel_monomial_coeff_7, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 7) hs
  have s8 : c 17 + c 18 = 0 := by
    simpa only [kernel_monomial_coeff_8, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 8) hs
  have s9 : c 19 = 0 := by
    simpa only [kernel_monomial_coeff_9, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 9) hs
  have s10 : c 20 = 0 := by
    simpa only [kernel_monomial_coeff_10, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 10) hs
  have t0 : c 6 = 0 := by
    simpa only [kernel_tangent_coeff_0, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 0) ht
  have t1 : 2 * c 7 = 0 := by
    simpa only [kernel_tangent_coeff_1, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 1) ht
  have t2 : 3 * c 8 + 4 * c 11 = 0 := by
    simpa only [kernel_tangent_coeff_2, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 2) ht
  have t3 : 4 * c 9 + 6 * c 12 = 0 := by
    simpa only [kernel_tangent_coeff_3, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 3) ht
  have t4 : 5 * c 10 + 8 * c 13 + 9 * c 15 = 0 := by
    simpa only [kernel_tangent_coeff_4, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 4) ht
  have t5 : 10 * c 14 + 12 * c 16 = 0 := by
    simpa only [kernel_tangent_coeff_5, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 5) ht
  have t6 : 15 * c 17 + 16 * c 18 = 0 := by
    simpa only [kernel_tangent_coeff_6, Polynomial.coeff_zero] using
      congrArg (fun p : Polynomial ℝ => p.coeff 6) ht
  have h2 : c 2 = 0 := by simpa only [t0, add_zero] using s2
  have h7 : c 7 = 0 := by linarith only [t1]
  have h3 : c 3 = 0 := by simpa only [h7, add_zero] using s3
  obtain ⟨h8, h11⟩ := kernel_solve_weight4 (c 4) (c 8) (c 11) s4 t2
  obtain ⟨h9, h12⟩ := kernel_solve_weight5 (c 5) (c 9) (c 12) s5 t3
  obtain ⟨h13, h15⟩ := kernel_solve_weight6 (c 10) (c 13) (c 15) s6 t4
  obtain ⟨h14, h16⟩ := kernel_solve_weight7 (c 14) (c 16) s7 t5
  obtain ⟨h17, h18⟩ := kernel_solve_weight8 (c 17) (c 18) s8 t6
  funext i
  fin_cases i
  · change c 0 = 0
    exact s0
  · change c 1 = 0
    exact s1
  · change c 2 = 0
    exact h2
  · change c 3 = 0
    exact h3
  · change c 4 = c 4
    rfl
  · change c 5 = c 5
    rfl
  · change c 6 = 0
    exact t0
  · change c 7 = 0
    exact h7
  · change c 8 = -4 * c 4
    exact h8
  · change c 9 = -3 * c 5
    exact h9
  · change c 10 = c 10
    rfl
  · change c 11 = 3 * c 4
    exact h11
  · change c 12 = 2 * c 5
    exact h12
  · change c 13 = -4 * c 10
    exact h13
  · change c 14 = 0
    exact h14
  · change c 15 = 3 * c 10
    exact h15
  · change c 16 = 0
    exact h16
  · change c 17 = 0
    exact h17
  · change c 18 = 0
    exact h18
  · change c 19 = 0
    exact s9
  · change c 20 = 0
    exact s10

private theorem kernel_reconstruction (a b c : ℝ) :
    quadraticPolynomial ![0, 0, 0, 0, a, b, 0, 0, -4 * a, -3 * b, c, 3 * a, 2 * b, -4 * c, 0, 3 * c, 0, 0, 0, 0, 0] =
      C a * tangentQuadratic 0 + C b * tangentQuadratic 1 + C c * tangentQuadratic 2 := by
  rw [quadraticPolynomial, kernel_sum_fin21]
  change
    C (0) * (X 0 * X 0) +
      C (0) * (X 0 * X 1) +
      C (0) * (X 0 * X 2) +
      C (0) * (X 0 * X 3) +
      C (a) * (X 0 * X 4) +
      C (b) * (X 0 * X 5) +
      C (0) * (X 1 * X 1) +
      C (0) * (X 1 * X 2) +
      C (-4 * a) * (X 1 * X 3) +
      C (-3 * b) * (X 1 * X 4) +
      C (c) * (X 1 * X 5) +
      C (3 * a) * (X 2 * X 2) +
      C (2 * b) * (X 2 * X 3) +
      C (-4 * c) * (X 2 * X 4) +
      C (0) * (X 2 * X 5) +
      C (3 * c) * (X 3 * X 3) +
      C (0) * (X 3 * X 4) +
      C (0) * (X 3 * X 5) +
      C (0) * (X 4 * X 4) +
      C (0) * (X 4 * X 5) +
      C (0) * (X 5 * X 5) =
    C a * (X 0 * X 4 - C 4 * (X 1 * X 3) + C 3 * (X 2 * X 2)) +
      C b * (X 0 * X 5 - C 3 * (X 1 * X 4) + C 2 * (X 2 * X 3)) +
      C c * (X 1 * X 5 - C 4 * (X 2 * X 4) + C 3 * (X 3 * X 3))
  simp only [C_0, C_mul, C_neg, zero_mul, zero_add, add_zero]
  ring

theorem quadraticPolynomial_of_joint_vanishing (c : Fin 21 → ℝ)
    (hcurve : ∀ t : ℝ, eval (monomialCurve t) (quadraticPolynomial c) = 0)
    (htangent : ∀ t : ℝ, eval (monomialTangent t) (quadraticPolynomial c) = 0) :
    quadraticPolynomial c = C (c 4) * tangentQuadratic 0 +
      C (c 5) * tangentQuadratic 1 + C (c 10) * tangentQuadratic 2 := by
  have hs : quadraticAlongMonomial c = 0 := by
    apply Polynomial.funext
    intro t
    rw [eval_quadraticAlongMonomial, hcurve]
    simp
  have ht : quadraticAlongTangent c = 0 := by
    apply Polynomial.funext
    intro t
    rw [eval_quadraticAlongTangent, htangent]
    simp
  calc
    quadraticPolynomial c = quadraticPolynomial
        ![0, 0, 0, 0, c 4, c 5, 0, 0, -4 * c 4, -3 * c 5, c 10,
          3 * c 4, 2 * c 5, -4 * c 10, 0, 3 * c 10, 0, 0, 0, 0, 0] :=
      congrArg quadraticPolynomial (kernel_coefficients c hs ht)
    _ = _ := kernel_reconstruction (c 4) (c 5) (c 10)

theorem homogeneous_quadratic_monomial_kernel
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 2)
    (hcurve : ∀ t : ℝ, eval (monomialCurve t) p = 0)
    (htangent : ∀ t : ℝ, eval (monomialTangent t) p = 0) :
    ∃ a b c : ℝ, p = C a * tangentQuadratic 0 + C b * tangentQuadratic 1 +
      C c * tangentQuadratic 2 := by
  obtain ⟨v, rfl⟩ := homogeneous_two_representation p hp
  exact ⟨v 4, v 5, v 10, quadraticPolynomial_of_joint_vanishing v hcurve htangent⟩

end PBCounterexample.Gram6
