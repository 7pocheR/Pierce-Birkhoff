import PBCounterexample.Main
import Lean.Util.CollectAxioms

/-!
# Formalization checks

This module is a test, not a dependency of the mathematical proof. It fails
if a listed theorem is missing or transitively uses an axiom outside Lean's
standard classical foundations. The theorem statements are also printed for
independent comparison with the mathematical specification.
-/

#check PBCounterexample.pierce_birkhoff_counterexample
#check PBCounterexample.explicit_quadratic_counterexample72
#check PBCounterexample.no_finite_max_min_representation
#check PBCounterexample.finite_quadratic_sign_obstruction
#check PBCounterexample.OrbitVanishing.polynomial_vanishes_on_orbit_iff
#check PBCounterexample.homogeneous_lattice_finite_sign_condition

#print axioms PBCounterexample.pierce_birkhoff_counterexample
#print axioms PBCounterexample.explicit_quadratic_counterexample72

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``PBCounterexample.pierce_birkhoff_counterexample,
    ``PBCounterexample.explicit_quadratic_counterexample72,
    ``PBCounterexample.no_finite_max_min_representation,
    ``PBCounterexample.finite_sup_inf_polynomials_isPolynomialLattice,
    ``PBCounterexample.not_polynomial_lattice,
    ``PBCounterexample.finite_quadratic_sign_obstruction,
    ``PBCounterexample.Function.continuous_f,
    ``PBCounterexample.Function.polynomialCover_count,
    ``PBCounterexample.Function.polynomialCover_homogeneous,
    ``PBCounterexample.Function.f_positive_homogeneous,
    ``PBCounterexample.homogeneous_lattice_finite_sign_condition,
    ``PBCounterexample.OrbitVanishing.polynomial_vanishes_on_orbit_iff,
    ``PBCounterexample.OrbitVanishing.polynomial_orbit_classification,
    ``PBCounterexample.OrbitGeometry.rankOne_pair_mem_closure,
    ``PBCounterexample.OrbitGeometry.bilinear_orbit_classification,
    ``PBCounterexample.GenericOrbitPoint.exists_positive_units_all_nonzero,
    ``PBCounterexample.polynomial_substitution_clear_denominator,
    ``PBCounterexample.exists_all_evals_ne_zero_in_open,
    ``PBCounterexample.exists_positive_time_same_polynomial_signs,
    ``PBCounterexample.Perturbation.f_plus,
    ``PBCounterexample.Perturbation.f_minus,
    ``PBCounterexample.Perturbation.product_functionals_equal,
    ``PBCounterexample.polynomial_lattice_precomp_equiv_iff]
  for name in targets do
    let info ← Lean.getConstInfo name
    unless info.isTheorem do
      throwError "Expected a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom dependency in {name}: {axiomName}"
    Lean.logInfo m!"Axiom check passed: {name}: {axioms}"
