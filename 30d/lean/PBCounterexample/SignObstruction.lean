import PBCounterexample.GenericOrbitPoint
import PBCounterexample.OrbitVanishing
import PBCounterexample.Perturbation
import PBCounterexample.SignTopology
import PBCounterexample.Radial

/-!
# Failure of every finite quadratic sign test
-/

namespace PBCounterexample

open Filter Topology
open PBCounterexample.Function (Coord Point X Y ofMatrices)
open OrbitGeometry (D E Mat orbit action)

theorem finite_quadratic_sign_obstruction
    (S : Finset (MvPolynomial Coord ℝ)) (hdegree : ∀ p ∈ S, p.totalDegree ≤ 2) :
    ∃ z w : Point, 0 < Function.f z ∧ Function.f w = 0 ∧
      ∀ p ∈ S, Real.sign (MvPolynomial.eval z p) = Real.sign (MvPolynomial.eval w p) := by
  classical
  let T := S.filter (fun p => ∃ z ∈ orbit,
    MvPolynomial.eval (ofMatrices z.1 z.2) p ≠ 0)
  have hT : ∀ p ∈ T, ∃ U V : Matˣ,
      MvPolynomial.eval (GenericOrbitPoint.point D E U V) p ≠ 0 := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨U, V, rfl⟩ := hz
    exact ⟨U, V, hpz⟩
  obtain ⟨U, V, hU, hV, hnonzero⟩ :=
    GenericOrbitPoint.exists_positive_units_all_nonzero D E T hT
  let o := GenericOrbitPoint.point D E U V
  have hlim (η : ℝ) : Tendsto (Perturbation.pointPath U V η) (𝓝[>] (0 : ℝ)) (𝓝 o) :=
    Perturbation.pointPath_tendsto_zero_right U V η
  have hdichotomy : ∀ p ∈ S,
      (∀ t, MvPolynomial.eval (Perturbation.pointPath U V 1 t) p =
        MvPolynomial.eval (Perturbation.pointPath U V (-1) t) p) ∨
      MvPolynomial.eval o p ≠ 0 := by
    intro p hp
    by_cases hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0
    · left
      obtain ⟨L, M, hrep⟩ :=
        OrbitVanishing.polynomial_orbit_classification p (hdegree p hp) hvan
      have hrepPoint (z : Point) :
          MvPolynomial.eval z p = L (Y z * X z) + M (X z * Y z) := by
        simpa only [Function.ofMatrices_X_Y] using hrep (X z) (Y z)
      intro t
      rw [hrepPoint, hrepPoint]
      exact Perturbation.product_functionals_equal U V t L M
    · right
      apply hnonzero p
      apply Finset.mem_filter.mpr
      refine ⟨hp, ?_⟩
      push_neg at hvan
      exact hvan
  obtain ⟨t, ht, hsign⟩ := exists_positive_time_same_polynomial_signs S
    (Perturbation.pointPath U V 1) (Perturbation.pointPath U V (-1)) o
    (hlim 1) (hlim (-1)) hdichotomy
  exact ⟨Perturbation.pointPath U V 1 t, Perturbation.pointPath U V (-1) t,
    Perturbation.f_plus_pos U V hU hV t ht, Perturbation.f_minus U V hU hV t ht, hsign⟩

theorem not_polynomial_lattice : ¬ IsPolynomialLattice Function.f := by
  intro hrep
  have hhom (t : ℝ) (ht : 0 < t) (z : Point) :
      Function.f (fun i => t * z i) = t ^ 2 * Function.f z :=
    Function.f_positive_homogeneous t ht z
  obtain ⟨S, hdegree, hsign⟩ := homogeneous_lattice_finite_sign_condition Function.f hhom hrep
  obtain ⟨z, w, hz, hw, hzw⟩ := finite_quadratic_sign_obstruction S hdegree
  have h := hsign z w hzw
  rw [Real.sign_of_pos hz, hw, Real.sign_zero] at h
  exact one_ne_zero h

end PBCounterexample
