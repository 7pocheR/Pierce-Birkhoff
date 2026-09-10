import PBCounterexample.Collaborator30Function
import PBCounterexample.SymmetricGenericPoint
import PBCounterexample.SymmetricOrbitVanishing
import PBCounterexample.SignTopology
import PBCounterexample.Radial

/-!
# The obstruction to finite polynomial lattice representations

The two congruence paths have equal products and opposite determinant signs.
They give different function signs while preserving any specified finite
family of polynomial signs of total degree at most two.
-/

namespace PBCounterexample.Collaborator30SignObstruction

open Filter Topology
open SymmetricFunction (Coord Point ofMatrices)
open SymmetricGeometry (Mat D E orbit)

theorem finite_quadratic_sign_obstruction
    (S : Finset (MvPolynomial Coord ℝ)) (hdegree : ∀ p ∈ S, p.totalDegree ≤ 2) :
    ∃ z w : Point, 0 < Collaborator30Function.f z ∧ Collaborator30Function.f w = 0 ∧
      ∀ p ∈ S, Real.sign (MvPolynomial.eval z p) = Real.sign (MvPolynomial.eval w p) := by
  classical
  let T := S.filter (fun p => ∃ z ∈ orbit,
    MvPolynomial.eval (ofMatrices z.1 z.2) p ≠ 0)
  have hT : ∀ p ∈ T, ∃ U : Matˣ,
      MvPolynomial.eval (SymmetricGenericPoint.point D E U) p ≠ 0 := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨U, rfl⟩ := hz
    exact ⟨U, hpz⟩
  obtain ⟨U, _, hnonzero⟩ :=
    SymmetricGenericPoint.exists_positive_unit_all_nonzero D E T hT
  let o := SymmetricGenericPoint.point D E U
  have hlim (η : ℝ) : Tendsto (SymmetricPerturbation.pointPath U η)
      (𝓝[>] (0 : ℝ)) (𝓝 o) :=
    SymmetricPerturbation.pointPath_tendsto_zero_right U η
  have hdichotomy : ∀ p ∈ S,
      (∀ t, MvPolynomial.eval (SymmetricPerturbation.pointPath U 1 t) p =
        MvPolynomial.eval (SymmetricPerturbation.pointPath U (-1) t) p) ∨
      MvPolynomial.eval o p ≠ 0 := by
    intro p hp
    by_cases hvan : ∀ z ∈ orbit, MvPolynomial.eval (ofMatrices z.1 z.2) p = 0
    · left
      obtain ⟨L, hrep⟩ := SymmetricOrbitVanishing.point_polynomial_orbit_classification
        p (hdegree p hp) hvan
      intro t
      rw [hrep, hrep, SymmetricPerturbation.pointPath_XY U 1 t (by norm_num),
        SymmetricPerturbation.pointPath_XY U (-1) t (by norm_num)]
    · right
      apply hnonzero p
      apply Finset.mem_filter.mpr
      refine ⟨hp, ?_⟩
      push_neg at hvan
      exact hvan
  obtain ⟨t, ht, hsign⟩ := exists_positive_time_same_polynomial_signs S
    (SymmetricPerturbation.pointPath U 1) (SymmetricPerturbation.pointPath U (-1)) o
    (hlim 1) (hlim (-1)) hdichotomy
  exact ⟨SymmetricPerturbation.pointPath U 1 t, SymmetricPerturbation.pointPath U (-1) t,
    Collaborator30Function.f_plus_pos U t ht, Collaborator30Function.f_minus U t ht, hsign⟩

theorem not_polynomial_lattice : ¬ IsPolynomialLattice Collaborator30Function.f := by
  intro hrep
  have hhom (t : ℝ) (ht : 0 < t) (z : Point) :
      Collaborator30Function.f (fun i => t * z i) = t ^ 2 * Collaborator30Function.f z :=
    Collaborator30Function.f_positive_homogeneous t ht z
  obtain ⟨S, hdegree, hsign⟩ :=
    homogeneous_lattice_finite_sign_condition Collaborator30Function.f hhom hrep
  obtain ⟨z, w, hz, hw, hzw⟩ := finite_quadratic_sign_obstruction S hdegree
  have h := hsign z w hzw
  rw [Real.sign_of_pos hz, hw, Real.sign_zero] at h
  exact one_ne_zero h

end PBCounterexample.Collaborator30SignObstruction
