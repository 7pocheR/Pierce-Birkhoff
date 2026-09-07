import PBCounterexample.SymmetricSignObstruction
import PBCounterexample.Reindexing
import PBCounterexample.FiniteExpressions

/-! The symmetric-matrix counterexample on thirty independent real coordinates. -/

namespace PBCounterexample.SymmetricMain

noncomputable def coordinateEquiv : SymmetricFunction.Coord ≃ Fin 30 :=
  Fintype.equivFinOfCardEq SymmetricFunction.coordinate_count

noncomputable def f30 (z : Fin 30 → ℝ) : ℝ :=
  SymmetricFunction.f (fun i => z (coordinateEquiv i))

noncomputable def polynomialCover30 : FiniteClosedPolynomialCover f30 :=
  SymmetricFunction.polynomialCover.precomp_coordinates coordinateEquiv

theorem continuous_f30 : Continuous f30 := polynomialCover30.continuous

theorem polynomialCover30_count : polynomialCover30.count = 16 :=
  SymmetricFunction.polynomialCover_count

theorem polynomialCover30_homogeneous (i : Fin polynomialCover30.count) :
    (polynomialCover30.label i).IsHomogeneous 2 :=
  (SymmetricFunction.polynomialCover_homogeneous i).rename_isHomogeneous

theorem not_polynomial_lattice_f30 : ¬ IsPolynomialLattice f30 := by
  intro h
  apply SymmetricSignObstruction.not_polynomial_lattice
  exact (polynomial_lattice_precomp_equiv_iff SymmetricFunction.f coordinateEquiv).mp h

theorem explicit_quadratic_counterexample30 :
    Continuous f30 ∧ polynomialCover30.count = 16 ∧
      (∀ i : Fin polynomialCover30.count, (polynomialCover30.label i).IsHomogeneous 2) ∧
      ¬ IsPolynomialLattice f30 :=
  ⟨continuous_f30, polynomialCover30_count, polynomialCover30_homogeneous,
    not_polynomial_lattice_f30⟩

theorem no_finite_max_min_representation
    {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 30) ℝ) :
    ¬ ∀ z : Fin 30 → ℝ, f30 z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j))) := by
  intro heq
  apply not_polynomial_lattice_f30
  rw [funext heq]
  exact finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p

theorem pierce_birkhoff_counterexample30 :
    ∃ f : (Fin 30 → ℝ) → ℝ, Continuous f ∧
      Nonempty (FiniteClosedPolynomialCover f) ∧ ¬ IsPolynomialLattice f :=
  ⟨f30, continuous_f30, ⟨polynomialCover30⟩, not_polynomial_lattice_f30⟩

end PBCounterexample.SymmetricMain
