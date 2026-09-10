import PBCounterexample.SignObstruction
import PBCounterexample.Reindexing
import PBCounterexample.FiniteExpressions

/-!
# The whole-space counterexample

The explicit function is defined on two independent six by six real matrices.
The final theorem also states the result on the standard 72-coordinate space.
-/

namespace PBCounterexample

theorem counterexample :
    Continuous Function.f ∧
    Nonempty (FiniteClosedPolynomialCover Function.f) ∧
    ¬ IsPolynomialLattice Function.f :=
  ⟨Function.continuous_f, ⟨Function.polynomialCover⟩, not_polynomial_lattice⟩

noncomputable def coordinateEquiv : Function.Coord ≃ Fin 72 :=
  Fintype.equivFinOfCardEq Function.coordinate_count

noncomputable def f72 (z : Fin 72 → ℝ) : ℝ :=
  Function.f (fun i => z (coordinateEquiv i))

noncomputable def polynomialCover72 : FiniteClosedPolynomialCover f72 :=
  Function.polynomialCover.precomp_coordinates coordinateEquiv

theorem continuous_f72 : Continuous f72 := polynomialCover72.continuous

theorem polynomialCover72_count : polynomialCover72.count = 193 :=
  Function.polynomialCover_count

theorem polynomialCover72_homogeneous (i : Fin polynomialCover72.count) :
    (polynomialCover72.label i).IsHomogeneous 2 :=
  (Function.polynomialCover_homogeneous i).rename_isHomogeneous

theorem not_polynomial_lattice_f72 : ¬ IsPolynomialLattice f72 := by
  intro h
  apply not_polynomial_lattice
  exact (polynomial_lattice_precomp_equiv_iff Function.f coordinateEquiv).mp h

theorem explicit_quadratic_counterexample72 :
    Continuous f72 ∧ polynomialCover72.count = 193 ∧
      (∀ i : Fin polynomialCover72.count, (polynomialCover72.label i).IsHomogeneous 2) ∧
      ¬ IsPolynomialLattice f72 :=
  ⟨continuous_f72, polynomialCover72_count, polynomialCover72_homogeneous,
    not_polynomial_lattice_f72⟩

theorem no_finite_max_min_representation
    {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 72) ℝ) :
    ¬ ∀ z : Fin 72 → ℝ, f72 z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j))) := by
  intro heq
  apply not_polynomial_lattice_f72
  rw [funext heq]
  exact finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p

/-- A continuous piecewise polynomial function on the whole space `ℝ⁷²`
that is not a finite lattice expression in arbitrary real polynomials. -/
theorem pierce_birkhoff_counterexample :
    ∃ f : (Fin 72 → ℝ) → ℝ, Continuous f ∧
      Nonempty (FiniteClosedPolynomialCover f) ∧ ¬ IsPolynomialLattice f :=
  ⟨f72, continuous_f72, ⟨polynomialCover72⟩, not_polynomial_lattice_f72⟩

end PBCounterexample
