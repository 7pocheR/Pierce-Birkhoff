import PBCounterexample.Quadratic8Main

/-! Independent interface checks for the full real-coordinate statement. -/

open PBCounterexample PBCounterexample.Quadratic8 MvPolynomial

example : Continuous (f : (Fin 8 → ℝ) → ℝ) := continuous_f

example : ∃ (p : Fin 137 → MvPolynomial (Fin 8) ℝ)
    (q : (Fin 137 → SignType) → MvPolynomial (Fin 8) ℝ),
    (∀ i, (p i).totalDegree ≤ 2) ∧
    (∀ s, (q s).totalDegree ≤ 2) ∧
    (∀ s (z : Fin 8 → ℝ),
      (∀ i, SignType.sign (eval z (p i)) = s i) → f z = eval z (q s)) := by
  have hc := signPartition_count
  generalize hP : signPartition = P at hc
  rcases P with ⟨count, test, test_degree, label, label_degree, agrees⟩
  dsimp only at hc
  subst count
  exact ⟨test, label, test_degree, label_degree, agrees⟩

example : ∃ (m : ℕ) (S : Fin m → Set (Fin 8 → ℝ))
    (p : Fin m → MvPolynomial (Fin 8) ℝ),
    m = 17 ∧ (∀ i, IsClosed (S i)) ∧
      (∀ i, IsSemialgebraic (S i)) ∧ (⋃ i, S i) = Set.univ ∧
      (∀ i z, z ∈ S i → f z = eval z (p i)) ∧
      (∀ i, (p i).totalDegree ≤ 2) :=
  ⟨polynomialCover.count, polynomialCover.region, polynomialCover.label,
    polynomialCover_count, polynomialCover.closed, polynomialCover.semialgebraic,
    polynomialCover.covers, polynomialCover.agrees, polynomialCover_degree⟩

example (e : LatticeExpr (Fin 8)) :
    ¬ (∀ z : Fin 8 → ℝ, e.eval z = f z) := by
  intro he
  exact not_isPolynomialLattice ⟨e, he⟩

example {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 8) ℝ) :
    ¬ (∀ z : Fin 8 → ℝ, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => eval z (p i j)))) :=
  not_finite_sup_inf_polynomials S hS T hT p

#check PBCounterexample.Quadratic8.whole_space_counterexample
#check PBCounterexample.Quadratic8.exists_whole_space_counterexample
#print axioms PBCounterexample.Quadratic8.whole_space_counterexample
#print axioms PBCounterexample.Quadratic8.exists_whole_space_counterexample
#print axioms PBCounterexample.Quadratic8.not_finite_sup_inf_polynomials
#print axioms PBCounterexample.Quadratic8Geometry.determinant_bound
#print axioms PBCounterexample.Quadratic8.agrees_on_entire_sign_realization
