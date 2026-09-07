import PBCounterexample.Gram7SignObstruction
import PBCounterexample.FiniteExpressions

/-! A whole-space seven-variable counterexample with six polynomial pieces. -/

namespace PBCounterexample.Gram7

theorem counterexample :
    Continuous f ∧
    polynomialCover.count = 6 ∧
    (∀ i : Fin polynomialCover.count, (polynomialCover.label i).IsHomogeneous 2) ∧
    (∀ (t : ℝ), 0 < t → ∀ z : Coord, f (t • z) = t^2 * f z) ∧
    ¬ IsPolynomialLattice f :=
  ⟨continuous_f, polynomialCover_count, polynomialCover_homogeneous,
    f_positive_homogeneous, not_isPolynomialLattice_f⟩

theorem no_finite_max_min_representation
    {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 7) ℝ) :
    ¬ ∀ z : Coord, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j))) := by
  intro heq
  apply not_isPolynomialLattice_f
  have h := finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p
  have hf := funext heq
  rwa [← hf] at h

theorem pierce_birkhoff_fails_in_dimension_seven :
    ∃ g : (Fin 7 → ℝ) → ℝ, Continuous g ∧
      ∃ C : FiniteClosedPolynomialCover g,
        C.count = 6 ∧ (∀ i, (C.label i).IsHomogeneous 2) ∧
        ¬ IsPolynomialLattice g :=
  ⟨f, continuous_f, polynomialCover, polynomialCover_count,
    polynomialCover_homogeneous, not_isPolynomialLattice_f⟩

end PBCounterexample.Gram7
