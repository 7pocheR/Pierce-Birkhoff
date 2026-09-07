import PBCounterexample.Gram7Main

open PBCounterexample
open scoped Topology

noncomputable section

-- These diagnostics check proposition types and the unrestricted domain.
example : ∃ g : (Fin 7 → ℝ) → ℝ, Continuous g ∧
    ∃ C : FiniteClosedPolynomialCover g,
      C.count = 6 ∧ (∀ i, (C.label i).IsHomogeneous 2) ∧
      ¬ ∃ e : LatticeExpr (Fin 7), ∀ z : Fin 7 → ℝ, e.eval z = g z :=
  Gram7.pierce_birkhoff_fails_in_dimension_seven

example : ∀ z : Fin 7 → ℝ, Gram7.coordinates (Gram7.ambient z) = z :=
  Gram7.coordinates_ambient

example (z : Fin 7 → ℝ) : Gram7.f z =
    if 0 < PolynomialSelection.minimum Gram7.qPolynomial z ∧
       0 < (Gram7.aMatrix z).det
    then PolynomialSelection.minimum Gram7.qPolynomial z else 0 := by
  change PolynomialSelection.f Gram7.qPolynomial Gram7.determinantPolynomial z = _
  simp only [PolynomialSelection.f, Gram7.determinantPolynomial,
    GramSelection.eval_determinantPolynomial, Gram7.eval_aPolynomial]

example (e : LatticeExpr (Fin 7)) :
    ¬ ∀ z : Fin 7 → ℝ, e.eval z = Gram7.f z := by
  intro h
  exact Gram7.not_isPolynomialLattice_f ⟨e, h⟩

#check @Gram7.counterexample
#check @Gram7.pierce_birkhoff_fails_in_dimension_seven
#check @Gram7.no_finite_max_min_representation
#check @Gram7.finite_homogeneous_tests_do_not_determine_sign
#check @homogeneous_lattice_finite_homogeneous_sign_condition
#check @Gram7.signed_path_pairs_eventually
#check @Gram7.unknownApproximation_error_isBigO
#check @Gram7.exists_positive_time_avoid_homogeneous_tests

-- Normal Lean dependency summaries; no raw closure traversal or kernel replay.
#print axioms Gram7.counterexample
#print axioms Gram7.no_finite_max_min_representation
#print axioms Gram7.pierce_birkhoff_fails_in_dimension_seven
#print axioms Gram7.finite_coefficient_certificate
