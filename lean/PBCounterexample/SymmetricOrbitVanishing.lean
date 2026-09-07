import PBCounterexample.SymmetricDecomposition
import PBCounterexample.SymmetricGeometry

/-! Low-degree polynomial equations of the symmetric rank-two congruence orbit. -/

namespace PBCounterexample.SymmetricOrbitVanishing

open SymmetricFunction (Coord Point X Y ofMatrices)
open SymmetricGeometry (Mat orbit)

theorem polynomial_orbit_classification (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2)
    (hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0) :
    ∃ L : Mat →ₗ[ℝ] ℝ, ∀ A B : Mat, A.IsSymm → B.IsSymm →
      MvPolynomial.eval (ofMatrices A B) p = L (A * B) := by
  obtain ⟨c, Lx, Ly, Qx, Qy, B, hsx, hsy, hrep⟩ :=
    SymmetricDecomposition.matrix_polynomial_decomposition p hp
  obtain ⟨L, hL⟩ := SymmetricGeometry.decomposed_orbit_classification
    c Lx Ly Qx Qy B hsx hsy
    (fun z hz => (hrep z.1 z.2).symm.trans (hvan z hz))
  exact ⟨L, fun A C hA hC => (hrep A C).trans (hL A C hA hC)⟩

theorem point_polynomial_orbit_classification (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2)
    (hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0) :
    ∃ L : Mat →ₗ[ℝ] ℝ, ∀ z : Point,
      MvPolynomial.eval z p = L (X z * Y z) := by
  obtain ⟨L, hL⟩ := polynomial_orbit_classification p hp hvan
  refine ⟨L, fun z => ?_⟩
  simpa only [SymmetricFunction.ofMatrices_X_Y] using
    hL (X z) (Y z) (SymmetricFunction.X_symm z) (SymmetricFunction.Y_symm z)

end PBCounterexample.SymmetricOrbitVanishing
