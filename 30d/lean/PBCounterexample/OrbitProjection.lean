import PBCounterexample.MatrixProjection
import PBCounterexample.OrbitGeometry

/-! Vanishing linear and pure quadratic terms on the two matrix orbit projections. -/

namespace PBCounterexample.OrbitProjection

open PBCounterexample.OrbitGeometry

theorem linear_D_eq_zero (L : Mat →ₗ[ℝ] ℝ)
    (hL : ∀ U V : Matˣ, L ((U : Mat) * D * ↑(V⁻¹)) = 0) : L = 0 := by
  exact MatrixProjection.linear_eq_zero_of_projection_vanish D 0
    (by norm_num [D, Matrix.diagonal]) L hL

theorem linear_E_eq_zero (L : Mat →ₗ[ℝ] ℝ)
    (hL : ∀ U V : Matˣ, L ((U : Mat) * E * ↑(V⁻¹)) = 0) : L = 0 := by
  exact MatrixProjection.linear_eq_zero_of_projection_vanish E 2
    (by rfl) L hL

theorem quadratic_D_eq_zero (Q : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hsym : ∀ A C, Q A C = Q C A)
    (hQ : ∀ U V : Matˣ, Q ((U : Mat) * D * ↑(V⁻¹)) ((U : Mat) * D * ↑(V⁻¹)) = 0) :
    Q = 0 := by
  exact MatrixProjection.quadratic_eq_zero_of_projection_vanish D 0 1
    (by norm_num [D, Matrix.diagonal]) (by norm_num [D, Matrix.diagonal])
    (by norm_num [D, Matrix.diagonal]) (by norm_num [D, Matrix.diagonal]) Q hsym hQ

theorem quadratic_E_eq_zero (Q : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hsym : ∀ A C, Q A C = Q C A)
    (hQ : ∀ U V : Matˣ, Q ((U : Mat) * E * ↑(V⁻¹)) ((U : Mat) * E * ↑(V⁻¹)) = 0) :
    Q = 0 := by
  exact MatrixProjection.quadratic_eq_zero_of_projection_vanish E 2 3
    (by rfl) (by rfl) (by rfl) (by rfl) Q hsym hQ

end PBCounterexample.OrbitProjection
