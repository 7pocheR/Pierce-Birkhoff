import PBCounterexample.QuadraticDecomposition
import PBCounterexample.OrbitGeometry
import PBCounterexample.OrbitProjection

/-! The degree-at-most-two equations of the rank-(2,2) zero-product orbit. -/

namespace PBCounterexample.OrbitVanishing

open PBCounterexample.Function PBCounterexample.OrbitGeometry

theorem polynomial_orbit_classification (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2)
    (hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0) :
    ∃ L M : OrbitGeometry.Mat →ₗ[ℝ] ℝ, ∀ A C : OrbitGeometry.Mat,
      MvPolynomial.eval (ofMatrices A C) p = L (C * A) + M (A * C) := by
  obtain ⟨c, Lx, Ly, Qx, Qy, B, hsx, hsy, hrep⟩ :=
    QuadraticDecomposition.matrix_polynomial_decomposition p hp
  have hcomponents (z : Pair) (hz : z ∈ orbit) :=
    bihomogeneous_components_vanish c Lx Ly Qx Qy B
      (fun w hw => (hrep w.1 w.2).symm.trans (hvan w hw)) z hz
  have hbase : (D, E) ∈ orbit := ⟨1, 1, (action_one (D, E)).symm⟩
  have hc := (hcomponents (D, E) hbase).1
  have hLx : Lx = 0 := by
    apply OrbitProjection.linear_D_eq_zero
    intro U V
    exact (hcomponents (action U V (D, E)) ⟨U, V, rfl⟩).2.1
  have hLy : Ly = 0 := by
    apply OrbitProjection.linear_E_eq_zero
    intro U V
    exact (hcomponents (action V U (D, E)) ⟨V, U, rfl⟩).2.2.1
  have hQx : Qx = 0 := by
    apply OrbitProjection.quadratic_D_eq_zero Qx hsx
    intro U V
    exact (hcomponents (action U V (D, E)) ⟨U, V, rfl⟩).2.2.2.1
  have hQy : Qy = 0 := by
    apply OrbitProjection.quadratic_E_eq_zero Qy hsy
    intro U V
    exact (hcomponents (action V U (D, E)) ⟨V, U, rfl⟩).2.2.2.2.1
  obtain ⟨L, M, hLM⟩ := bilinear_orbit_classification B
    (fun z hz => (hcomponents z hz).2.2.2.2.2)
  refine ⟨L, M, ?_⟩
  intro A C
  simpa only [hrep, hc, hLx, hLy, hQx, hQy, LinearMap.zero_apply, zero_add] using hLM A C

theorem polynomial_orbit_entry_classification (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2)
    (hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0) :
    ∃ a b : OrbitGeometry.I → OrbitGeometry.I → ℝ, ∀ A C : OrbitGeometry.Mat,
      MvPolynomial.eval (ofMatrices A C) p =
        (∑ i, ∑ j, a i j * (A * C) i j) + (∑ i, ∑ j, b i j * (C * A) i j) := by
  obtain ⟨L, M, hLM⟩ := polynomial_orbit_classification p hp hvan
  refine ⟨fun i j => M (OrbitAlgebra.unit i j), fun i j => L (OrbitAlgebra.unit i j), ?_⟩
  intro A C
  rw [hLM, OrbitAlgebra.linear_eval_expansion L, OrbitAlgebra.linear_eval_expansion M]
  simp only [mul_comm]
  exact add_comm _ _

noncomputable def reverseProductPolynomial (i j : OrbitGeometry.I) : MvPolynomial Coord ℝ :=
  ∑ k : OrbitGeometry.I,
    MvPolynomial.X (true, i, k) * MvPolynomial.X (false, k, j)

@[simp] theorem eval_reverseProductPolynomial (z : Point) (i j : OrbitGeometry.I) :
    MvPolynomial.eval z (reverseProductPolynomial i j) = (Y z * X z) i j := by
  simp [reverseProductPolynomial, Matrix.mul_apply, X, Y]

noncomputable def productEntryCombination
    (a b : OrbitGeometry.I → OrbitGeometry.I → ℝ) : MvPolynomial Coord ℝ :=
  (∑ i, ∑ j, MvPolynomial.C (a i j) * productPolynomial i j) +
    (∑ i, ∑ j, MvPolynomial.C (b i j) * reverseProductPolynomial i j)

@[simp] theorem eval_productEntryCombination
    (a b : OrbitGeometry.I → OrbitGeometry.I → ℝ) (z : Point) :
    MvPolynomial.eval z (productEntryCombination a b) =
      (∑ i, ∑ j, a i j * (X z * Y z) i j) +
        (∑ i, ∑ j, b i j * (Y z * X z) i j) := by
  simp [productEntryCombination]

/-- Among polynomials of total degree at most two, the equations of the
rank-(2,2) orbit are exactly constant linear combinations of the entries of
the two matrix products. -/
theorem polynomial_vanishes_on_orbit_iff (p : MvPolynomial Coord ℝ)
    (hp : p.totalDegree ≤ 2) :
    (∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0) ↔
      ∃ a b : OrbitGeometry.I → OrbitGeometry.I → ℝ, p = productEntryCombination a b := by
  constructor
  · intro hvan
    obtain ⟨a, b, hab⟩ := polynomial_orbit_entry_classification p hp hvan
    refine ⟨a, b, MvPolynomial.funext ?_⟩
    intro z
    simpa only [ofMatrices_X_Y, eval_productEntryCombination] using hab (X z) (Y z)
  · rintro ⟨a, b, rfl⟩ z hz
    obtain ⟨hxy, hyx⟩ := orbit_products_zero z hz
    simp only [eval_productEntryCombination, X_ofMatrices, Y_ofMatrices, hxy, hyx]
    simp

end PBCounterexample.OrbitVanishing
