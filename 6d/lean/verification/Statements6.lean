import PBCounterexample.Gram6Main

open PBCounterexample PBCounterexample.Gram6 MvPolynomial

example : Continuous (f : (Fin 6 → ℝ) → ℝ) := continuous_f

example : ∃ (m : ℕ) (S : Fin m → Set (Fin 6 → ℝ))
    (p : Fin m → MvPolynomial (Fin 6) ℝ),
    m = 5 ∧ (∀ i, IsClosed (S i)) ∧
      (∀ i, IsSemialgebraic (S i)) ∧ (⋃ i, S i) = Set.univ ∧
      (∀ i z, z ∈ S i → f z = eval z (p i)) ∧
      (∀ i, (p i).IsHomogeneous 2) :=
  ⟨polynomialCover.count, polynomialCover.region, polynomialCover.label,
    polynomialCover_count, polynomialCover.closed, polynomialCover.semialgebraic,
    polynomialCover.covers, polynomialCover.agrees, polynomialCover_homogeneous⟩

example (e : LatticeExpr (Fin 6)) :
    ¬ (∀ z : Fin 6 → ℝ, e.eval z = f z) := by
  intro he
  exact not_isPolynomialLattice ⟨e, he⟩

example {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 6) ℝ) :
    ¬ (∀ z : Fin 6 → ℝ, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => eval z (p i j)))) :=
  not_finite_sup_inf_polynomials S hS T hT p

#check PBCounterexample.Gram6.exists_same_homogeneous_signs_different_f
#check PBCounterexample.Gram6.whole_space_counterexample
#check PBCounterexample.Gram6.exists_whole_space_counterexample
#check PBCounterexample.Gram6.not_finite_sup_inf_polynomials
#print axioms PBCounterexample.Gram6.exists_same_homogeneous_signs_different_f
#print axioms PBCounterexample.Gram6.not_isPolynomialLattice
#print axioms PBCounterexample.Gram6.whole_space_counterexample
#print axioms PBCounterexample.Gram6.exists_whole_space_counterexample
#print axioms PBCounterexample.Gram6.not_finite_sup_inf_polynomials
