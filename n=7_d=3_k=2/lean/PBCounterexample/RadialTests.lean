import PBCounterexample.Radial

/-! Homogeneous test polynomials suffice for the quadratic radial sign condition. -/

namespace PBCounterexample

namespace LatticeExpr

theorem lowDegreeTests_homogeneous {σ : Type*} (e : LatticeExpr σ) :
    ∀ p ∈ e.lowDegreeTests, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2 := by
  classical
  intro p hp
  obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.1 hp
  rcases Finset.mem_insert.1 hp with rfl | hp
  · exact Or.inl (MvPolynomial.homogeneousComponent_isHomogeneous 1 q)
  · have he : p = MvPolynomial.homogeneousComponent 2 q := Finset.mem_singleton.1 hp
    rw [he]
    exact Or.inr (MvPolynomial.homogeneousComponent_isHomogeneous 2 q)

end LatticeExpr

theorem homogeneous_lattice_finite_homogeneous_sign_condition
    {σ : Type*} (g : (σ → ℝ) → ℝ)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (fun i => t * z i) = t ^ 2 * g z)
    (hrep : IsPolynomialLattice g) :
    ∃ S : Finset (MvPolynomial σ ℝ),
      (∀ p ∈ S, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2) ∧
      ∀ z w, (∀ p ∈ S,
        Real.sign (MvPolynomial.eval z p) = Real.sign (MvPolynomial.eval w p)) →
        Real.sign (g z) = Real.sign (g w) := by
  obtain ⟨e, he⟩ := hrep
  exact ⟨e.lowDegreeTests, e.lowDegreeTests_homogeneous,
    e.sign_eq_of_lowDegreeTests g hg he⟩

end PBCounterexample
