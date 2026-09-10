import PBCounterexample.SymmetricMain
import PBCounterexample.Collaborator30Main

/-!
Expanded whole-space statements for comparison with the mathematical
specification. This verification file is not imported by the proof modules.
-/

namespace Verification30

open PBCounterexample

theorem expanded_fifteen_label_statement :
    ∃ f : (Fin 30 → ℝ) → ℝ, Continuous f ∧
      ∃ m : ℕ, m = 16 ∧
      ∃ S : Fin m → Set (Fin 30 → ℝ),
      ∃ p : Fin m → MvPolynomial (Fin 30) ℝ,
        (∀ i, IsClosed (S i)) ∧
        (∀ i, IsSemialgebraic (S i)) ∧
        (∀ i, (p i).IsHomogeneous 2) ∧
        (∀ z : Fin 30 → ℝ, ∃ i, z ∈ S i) ∧
        (∀ i z, z ∈ S i → f z = MvPolynomial.eval z (p i)) ∧
        (∀ e : LatticeExpr (Fin 30), ∃ z : Fin 30 → ℝ, e.eval z ≠ f z) := by
  classical
  refine ⟨SymmetricMain.f30, SymmetricMain.continuous_f30,
    SymmetricMain.polynomialCover30.count, SymmetricMain.polynomialCover30_count,
    SymmetricMain.polynomialCover30.region, SymmetricMain.polynomialCover30.label,
    SymmetricMain.polynomialCover30.closed, SymmetricMain.polynomialCover30.semialgebraic,
    SymmetricMain.polynomialCover30_homogeneous, ?_,
    SymmetricMain.polynomialCover30.agrees, ?_⟩
  · intro z
    have hz : z ∈ ⋃ i, SymmetricMain.polynomialCover30.region i := by
      rw [SymmetricMain.polynomialCover30.covers]
      trivial
    exact Set.mem_iUnion.mp hz
  · intro e
    by_contra h
    push_neg at h
    exact SymmetricMain.not_polynomial_lattice_f30 ⟨e, h⟩

theorem expanded_forty_label_statement :
    ∃ f : (Fin 30 → ℝ) → ℝ, Continuous f ∧
      ∃ m : ℕ, m = 41 ∧
      ∃ S : Fin m → Set (Fin 30 → ℝ),
      ∃ p : Fin m → MvPolynomial (Fin 30) ℝ,
        (∀ i, IsClosed (S i)) ∧
        (∀ i, IsSemialgebraic (S i)) ∧
        (∀ i, (p i).IsHomogeneous 2) ∧
        (∀ z : Fin 30 → ℝ, ∃ i, z ∈ S i) ∧
        (∀ i z, z ∈ S i → f z = MvPolynomial.eval z (p i)) ∧
        (∀ e : LatticeExpr (Fin 30), ∃ z : Fin 30 → ℝ, e.eval z ≠ f z) := by
  classical
  refine ⟨Collaborator30Main.f30, Collaborator30Main.continuous_f30,
    Collaborator30Main.polynomialCover30.count, Collaborator30Main.polynomialCover30_count,
    Collaborator30Main.polynomialCover30.region, Collaborator30Main.polynomialCover30.label,
    Collaborator30Main.polynomialCover30.closed, Collaborator30Main.polynomialCover30.semialgebraic,
    Collaborator30Main.polynomialCover30_homogeneous, ?_,
    Collaborator30Main.polynomialCover30.agrees, ?_⟩
  · intro z
    have hz : z ∈ ⋃ i, Collaborator30Main.polynomialCover30.region i := by
      rw [Collaborator30Main.polynomialCover30.covers]
      trivial
    exact Set.mem_iUnion.mp hz
  · intro e
    by_contra h
    push_neg at h
    exact Collaborator30Main.not_polynomial_lattice_f30 ⟨e, h⟩

#print PBCounterexample.IsPolynomialLattice
#print PBCounterexample.LatticeExpr
#print PBCounterexample.LatticeExpr.eval
#print PBCounterexample.FiniteClosedPolynomialCover
#print PBCounterexample.SymmetricFunction.Coord
#print PBCounterexample.SymmetricFunction.X
#print PBCounterexample.SymmetricFunction.Y
#print PBCounterexample.PolynomialSelection.f
#print PBCounterexample.SymmetricMain.f30
#print PBCounterexample.SymmetricMain.coordinateEquiv
#print PBCounterexample.SymmetricFunction.f
#print PBCounterexample.Collaborator30Main.f30
#print PBCounterexample.Collaborator30Main.coordinateEquiv
#print PBCounterexample.Collaborator30Function.f
#check PBCounterexample.Collaborator30Function.q_eq
#check PBCounterexample.Collaborator30Function.f_eq
#check PBCounterexample.Collaborator30Function.label_count
#check PBCounterexample.SymmetricMain.explicit_quadratic_counterexample30
#check PBCounterexample.SymmetricMain.no_finite_max_min_representation
#check PBCounterexample.SymmetricMain.pierce_birkhoff_counterexample30
#check PBCounterexample.Collaborator30Main.explicit_quadratic_counterexample30
#check PBCounterexample.Collaborator30Main.no_finite_max_min_representation
#check PBCounterexample.Collaborator30Main.pierce_birkhoff_counterexample30
#print axioms expanded_fifteen_label_statement
#print axioms expanded_forty_label_statement

end Verification30
