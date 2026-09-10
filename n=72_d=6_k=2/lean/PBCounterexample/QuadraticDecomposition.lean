import PBCounterexample.Function
import PBCounterexample.QuadraticForms

/-! Decomposing degree-at-most-two polynomials on the two matrix coordinate spaces. -/

namespace PBCounterexample.QuadraticDecomposition

open PBCounterexample.Function

noncomputable section

def leftEmbedding : Mat →ₗ[ℝ] Point where
  toFun A := ofMatrices A 0
  map_add' := by
    intro A B
    ext ⟨b, i, j⟩
    cases b <;> simp [ofMatrices]
  map_smul' := by
    intro r A
    ext ⟨b, i, j⟩
    cases b <;> simp [ofMatrices]

def rightEmbedding : Mat →ₗ[ℝ] Point where
  toFun B := ofMatrices 0 B
  map_add' := by
    intro A B
    ext ⟨b, i, j⟩
    cases b <;> simp [ofMatrices]
  map_smul' := by
    intro r A
    ext ⟨b, i, j⟩
    cases b <;> simp [ofMatrices]

theorem ofMatrices_eq_sum (A B : Mat) :
    ofMatrices A B = leftEmbedding A + rightEmbedding B := by
  ext ⟨b, i, j⟩
  cases b <;> simp [ofMatrices, leftEmbedding, rightEmbedding]

/-- The pure quadratic forms can be chosen symmetric. The mixed term is a
bilinear form on the two independent matrix spaces. -/
theorem matrix_polynomial_decomposition (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2) :
    ∃ (c : ℝ) (Lx Ly : Mat →ₗ[ℝ] ℝ)
      (Qx Qy B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ),
      (∀ A C, Qx A C = Qx C A) ∧
      (∀ A C, Qy A C = Qy C A) ∧
      ∀ A C, MvPolynomial.eval (ofMatrices A C) p =
        c + Lx A + Ly C + Qx A A + Qy C C + B A C := by
  obtain ⟨c, L, Q, hsym, hrep⟩ := polynomial_representation p hp
  refine ⟨c, L.comp leftEmbedding, L.comp rightEmbedding,
    Q.compl₁₂ leftEmbedding leftEmbedding,
    Q.compl₁₂ rightEmbedding rightEmbedding,
    (2 : ℝ) • Q.compl₁₂ leftEmbedding rightEmbedding, ?_, ?_, ?_⟩
  · intro A C
    exact hsym _ _
  · intro A C
    exact hsym _ _
  · intro A C
    rw [hrep, ofMatrices_eq_sum]
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsym (rightEmbedding C) (leftEmbedding A)]
    ring

theorem point_polynomial_decomposition (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2) :
    ∃ (c : ℝ) (Lx Ly : Mat →ₗ[ℝ] ℝ)
      (Qx Qy B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ),
      (∀ A C, Qx A C = Qx C A) ∧
      (∀ A C, Qy A C = Qy C A) ∧
      ∀ z : Point, MvPolynomial.eval z p =
        c + Lx (X z) + Ly (Y z) + Qx (X z) (X z) + Qy (Y z) (Y z) + B (X z) (Y z) := by
  obtain ⟨c, Lx, Ly, Qx, Qy, B, hsx, hsy, hrep⟩ := matrix_polynomial_decomposition p hp
  exact ⟨c, Lx, Ly, Qx, Qy, B, hsx, hsy, fun z => by simpa using hrep (X z) (Y z)⟩

end

end PBCounterexample.QuadraticDecomposition
