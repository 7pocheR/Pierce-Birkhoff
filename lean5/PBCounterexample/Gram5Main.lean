import PBCounterexample.Gram5FiniteFamily
import PBCounterexample.Gram5Degree
import PBCounterexample.FiniteExpressions

/-! A whole-space five-dimensional piecewise polynomial function with no
finite polynomial lattice representation, allowing arbitrary real leaves. -/

namespace PBCounterexample.Gram5

noncomputable section

theorem whole_space_counterexample :
    Continuous f ∧ polynomialCover.count = 5 ∧
      (∀ i, (polynomialCover.label i).totalDegree ≤ 3) ∧
      ¬ IsPolynomialLattice f :=
  ⟨continuous_f, polynomialCover_count, polynomialCover_totalDegree,
    not_isPolynomialLattice⟩

theorem exists_whole_space_counterexample :
    ∃ g : (Fin 5 → ℝ) → ℝ, Continuous g ∧
      ∃ C : FiniteClosedPolynomialCover g, C.count = 5 ∧
        (∀ i, (C.label i).totalDegree ≤ 3) ∧ ¬ IsPolynomialLattice g :=
  ⟨f, continuous_f, polynomialCover, polynomialCover_count,
    polynomialCover_totalDegree, not_isPolynomialLattice⟩

theorem not_finite_sup_inf_polynomials {ι κ : Type*}
    (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 5) ℝ) :
    ¬ ∀ z : Fin 5 → ℝ, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j))) := by
  intro heq
  obtain ⟨e, he⟩ := finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p
  exact not_isPolynomialLattice ⟨e, fun z => (he z).trans (heq z).symm⟩

end

end PBCounterexample.Gram5
