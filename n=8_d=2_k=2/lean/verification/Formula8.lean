import PBCounterexample.Quadratic8Main

/-! Literal coordinate formulas, independently stated for comparison with the
manuscript. These checks do not supply hypotheses to the counterexample. -/

namespace Quadratic8FormulaAudit

open PBCounterexample MvPolynomial

abbrev Space := Fin 8 → ℝ

noncomputable def a (z : Space) : ℝ :=
  (z 0)^2 + (z 1)^2 + 3 * (z 2)^2 - (z 3)^2 - (z 4)^2

noncomputable def b (z : Space) : ℝ :=
  z 0 * (-z 4 + z 5 / 2) + z 1 * (z 2 + z 3) + 3 * z 2 * (z 5 / 2) -
    (z 3 * (-z 4 / 2 + z 5) + z 4 * (2 * z 2 + z 3 / 2))

noncomputable def d (z : Space) : ℝ :=
  (z 0)^2 + (z 1)^2 - (z 4 / 2)^2 - (z 3 / 2)^2

noncomputable def e (z : Space) : ℝ :=
  (-z 4 + z 5 / 2) * (-z 1) + (z 2 + z 3) * z 0 -
    ((-z 4 / 2 + z 5) * (-z 4 / 2) + (2 * z 2 + z 3 / 2) * (z 3 / 2))

noncomputable def q (z : Space) : Fin 4 → ℝ := ![
  -10 * b z + 2 * d z + 2 * e z,
  4 * a z + 2 * b z - 2 * d z - 2 * e z,
  -4 * a z + 2 * b z + 6 * d z - 10 * e z,
  -4 * a z + 2 * b z + 2 * d z + 2 * e z]

noncomputable def c₁ (z : Space) : ℝ :=
  z 0 * (-z 4 + z 5 / 2) + z 1 * (z 2 + z 3)

noncomputable def c₂ (z : Space) : ℝ := -((z 0)^2 + (z 1)^2)

noncomputable def h (z : Space) : ℝ := min (min (q z 0) (q z 1)) (min (q z 2) (q z 3))

noncomputable def H (z : Space) : ℝ := h z - 8 * max |z 6 - c₁ z| |z 7 - c₂ z|

noncomputable def O (z : Space) : ℝ := z 2 * z 6 + (z 5 / 2) * z 7

noncomputable def F (z : Space) : ℝ := if 0 < H z ∧ 0 < O z then H z else 0

private theorem coordinate_zero (z : Space) : Quadratic8.baseProjection z 0 = z 0 := rfl
private theorem coordinate_one (z : Space) : Quadratic8.baseProjection z 1 = z 1 := rfl
private theorem coordinate_two (z : Space) : Quadratic8.baseProjection z 2 = z 2 := rfl
private theorem coordinate_three (z : Space) : Quadratic8.baseProjection z 3 = z 3 := rfl
private theorem coordinate_four (z : Space) : Quadratic8.baseProjection z 4 = z 4 := rfl
private theorem coordinate_five (z : Space) : Quadratic8.baseProjection z 5 = z 5 := rfl

theorem base_label_formula (z : Space) (j : Fin 4) :
    eval (Quadratic8.baseProjection z) (Gram6.labelPolynomial j) = q z j := by
  fin_cases j <;>
    norm_num [Gram6.labelPolynomial, Gram6.eval_gramPolynomial, Gram6.gramMatrix,
      Gram6.aMatrix, Gram6.bMatrix,
      coordinate_zero, coordinate_one, coordinate_two, coordinate_three,
      coordinate_four, coordinate_five,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons,
      q, a, b, d, e] <;> ring

theorem h_le (z : Space) (j : Fin 4) : h z ≤ q z j := by
  fin_cases j
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem base_minimum_formula (z : Space) : Gram6.minimum (Quadratic8.baseProjection z) = h z := by
  apply le_antisymm
  · dsimp only [h]
    simp only [le_min_iff]
    exact ⟨⟨by simpa only [base_label_formula] using
      Quadratic8.base_minimum_le_labelPolynomial (Quadratic8.baseProjection z) 0,
      by simpa only [base_label_formula] using
      Quadratic8.base_minimum_le_labelPolynomial (Quadratic8.baseProjection z) 1⟩,
      ⟨by simpa only [base_label_formula] using
      Quadratic8.base_minimum_le_labelPolynomial (Quadratic8.baseProjection z) 2,
      by simpa only [base_label_formula] using
      Quadratic8.base_minimum_le_labelPolynomial (Quadratic8.baseProjection z) 3⟩⟩
  · obtain ⟨j, hj⟩ := Quadratic8.exists_base_minimum_eq (Quadratic8.baseProjection z)
    rw [hj, base_label_formula]
    exact h_le z j

theorem minimum_formula (z : Space) : Quadratic8.minimum z = H z := by
  rw [Quadratic8.minimum_eq, base_minimum_formula]
  simp only [Quadratic8.eval_errorPolynomial_zero, Quadratic8.eval_errorPolynomial_one,
    Quadratic8.eval_cofactor1, Quadratic8.eval_cofactor2,
    coordinate_zero, coordinate_one, coordinate_two, coordinate_three,
    coordinate_four, coordinate_five, H, c₁, c₂]

theorem function_formula (z : Space) : Quadratic8.f z = F z := by
  change (if 0 < Quadratic8.minimum z ∧ 0 < eval z Quadratic8.orientationPolynomial
    then Quadratic8.minimum z else 0) = F z
  rw [minimum_formula, Quadratic8.eval_orientationPolynomial]
  rfl

theorem literal_function_continuous : Continuous F := by
  have hf : Quadratic8.f = F := funext function_formula
  rw [← hf]
  exact Quadratic8.continuous_f

theorem literal_function_not_polynomial_lattice : ¬ IsPolynomialLattice F := by
  have hf : Quadratic8.f = F := funext function_formula
  rw [← hf]
  exact Quadratic8.not_isPolynomialLattice

#print axioms function_formula
#print axioms literal_function_continuous
#print axioms literal_function_not_polynomial_lattice

end Quadratic8FormulaAudit
