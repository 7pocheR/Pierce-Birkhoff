import PBCounterexample.Quadratic8Data
import PBCounterexample.Quadratic8Geometry
import PBCounterexample.Quadratic8Partition

/-! Global continuity and polynomial covers for the eight-dimensional function. -/

namespace PBCounterexample.Quadratic8

open MvPolynomial

theorem orientation_ne_zero {z : Coord} (hz : 0 < minimum z) :
    eval z orientationPolynomial ≠ 0 := by
  have h1 := abs_error_lt_of_minimum_pos hz 0
  have h2 := abs_error_lt_of_minimum_pos hz 1
  simp only [eval_errorPolynomial_zero, eval_cofactor1] at h1
  simp only [eval_errorPolynomial_one, eval_cofactor2, sub_neg_eq_add] at h2
  have h := Quadratic8Geometry.orientation_ne_zero (baseProjection z) (z 6) (z 7)
    (base_minimum_pos hz) h1 h2
  rw [eval_orientationPolynomial]
  change z 2 * z 6 + (z 5 / 2) * z 7 ≠ 0 at h
  exact h

noncomputable def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover labelPolynomial orientationPolynomial
    (fun _ hz => orientation_ne_zero hz)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem polynomialCover_count : polynomialCover.count = 17 := by
  change Fintype.card (Option Label) = 17
  rw [Fintype.card_option, label_count]

theorem polynomialCover_degree (i : Fin polynomialCover.count) :
    (polynomialCover.label i).totalDegree ≤ 2 := by
  change (PolynomialSelection.label labelPolynomial _).totalDegree ≤ 2
  cases (Fintype.equivFin (Option Label)).symm i with
  | none => simp [PolynomialSelection.label]
  | some a => exact labelPolynomial_degree a

/-- The fixed function is continuous on the entire eight-coordinate space. It has
one quadratic label on each entire realization of 137 quadratic signs, a cover
by seventeen closed semialgebraic polynomial pieces, and no finite expression
formed from arbitrary real polynomials by maxima and minima. -/
theorem whole_space_counterexample :
    Continuous f ∧
      (∃ P : FinitePolynomialSignPartition f 2 2, P.count = 137) ∧
      (∃ C : FiniteClosedPolynomialCover f,
        C.count = 17 ∧ ∀ i, (C.label i).totalDegree ≤ 2) ∧
      ¬ IsPolynomialLattice f :=
  ⟨continuous_f, ⟨signPartition, signPartition_count⟩,
    ⟨polynomialCover, polynomialCover_count, polynomialCover_degree⟩,
    not_isPolynomialLattice⟩

/-- Existential statement on all of `Fin 8 → ℝ`, without a polynomial graph
constraint or any restriction on the degrees of a proposed representation. -/
theorem exists_whole_space_counterexample :
    ∃ g : (Fin 8 → ℝ) → ℝ,
      Continuous g ∧
      (∃ P : FinitePolynomialSignPartition g 2 2, P.count = 137) ∧
      (∃ C : FiniteClosedPolynomialCover g,
        C.count = 17 ∧ ∀ i, (C.label i).totalDegree ≤ 2) ∧
      ¬ IsPolynomialLattice g :=
  ⟨f, whole_space_counterexample⟩

end PBCounterexample.Quadratic8
