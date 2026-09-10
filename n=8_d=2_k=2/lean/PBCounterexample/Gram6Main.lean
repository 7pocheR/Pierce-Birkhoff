import PBCounterexample.Gram6SignObstruction
import PBCounterexample.FiniteExpressions

/-! The six-dimensional whole-space counterexample with quadratic labels. -/

namespace PBCounterexample.Gram6

/-- The fixed function on all six real coordinates has five closed semialgebraic polynomial pieces
and no finite lattice expression in real polynomials of arbitrary degrees. -/
theorem whole_space_counterexample :
    Continuous f ∧
      (∃ C : FiniteClosedPolynomialCover f,
        C.count = 5 ∧ ∀ i, (C.label i).IsHomogeneous 2) ∧
      ¬ IsPolynomialLattice f :=
  ⟨continuous_f, ⟨polynomialCover, polynomialCover_count, polynomialCover_homogeneous⟩,
    not_isPolynomialLattice⟩

/-- An existential form whose ambient domain is the entire space `Fin 6 → ℝ`. -/
theorem exists_whole_space_counterexample :
    ∃ g : (Fin 6 → ℝ) → ℝ,
      Continuous g ∧
      (∃ C : FiniteClosedPolynomialCover g,
        C.count = 5 ∧ ∀ i, (C.label i).IsHomogeneous 2) ∧
      ¬ IsPolynomialLattice g :=
  ⟨f, whole_space_counterexample⟩

/-- No ordinary finite maximum of nonempty finite minima of arbitrary real polynomials equals
the fixed six-dimensional function everywhere. -/
theorem not_finite_sup_inf_polynomials {ι κ : Type*}
    (S : Finset ι) (hS : S.Nonempty) (T : ι → Finset κ)
    (hT : ∀ i, (T i).Nonempty) (p : ι → κ → MvPolynomial (Fin 6) ℝ) :
    ¬ (∀ z : Fin 6 → ℝ, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j)))) := by
  intro heq
  apply not_isPolynomialLattice
  have hfun : f = (fun z =>
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j)))) :=
    funext heq
  rw [hfun]
  exact finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p

end PBCounterexample.Gram6
