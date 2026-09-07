import PBCounterexample.Gram7Certificate
import PBCounterexample.Gram7AvoidanceAnalytic
import PBCounterexample.LowDegreeCoordinates
import PBCounterexample.MatrixKernel

/-! Simultaneous avoidance of homogeneous linear and quadratic tests on the fixed base curve. -/

noncomputable section

namespace PBCounterexample.Gram7

open Filter Asymptotics Matrix
open scoped Topology BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def gramQuadraticSpan : Submodule ℝ (MvPolynomial (Fin 7) ℝ) :=
  Submodule.span ℝ (Set.range gramPolynomials)

def linearPolynomial (v : Fin 7 → ℝ) : MvPolynomial (Fin 7) ℝ :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i

def quadraticPolynomial (v : Fin 28 → ℝ) : MvPolynomial (Fin 7) ℝ :=
  ∑ i, MvPolynomial.C (v i) * quadraticMonomial i

theorem homogeneous_one_representation
    (p : MvPolynomial (Fin 7) ℝ) (hp : p.IsHomogeneous 1) :
    ∃ v : Fin 7 → ℝ, p = linearPolynomial v :=
  ⟨fun i => p.coeff (Finsupp.single i 1), LowDegreeCoordinates.homogeneous_one_eq_sum p hp⟩

theorem homogeneous_two_representation
    (p : MvPolynomial (Fin 7) ℝ) (hp : p.IsHomogeneous 2) :
    ∃ v : Fin 28 → ℝ, p = quadraticPolynomial v := by
  refine ⟨fun i => p.coeff (quadraticExponent i), ?_⟩
  exact LowDegreeCoordinates.homogeneous_two_eq_sum quadraticPairs
    quadraticExponent_injective quadraticPairs_complete p hp

theorem quadraticCoefficientMatrixOver_kernel_eq_gram_range :
    LinearMap.ker (quadraticCoefficientMatrixOver ℝ).mulVecLin =
      LinearMap.range gramCoefficientMatrixᵀ.mulVecLin := by
  apply matrix_kernel_eq_range_of_rank_sum
  · rw [quadraticCoefficientMatrixOver_eq]
    exact quadraticCoefficientMatrix_gram_annihilation
  · rw [quadraticCoefficientMatrixOver_rank, Matrix.rank_transpose,
      gramCoefficientMatrix_rank]

theorem gramPolynomials_eq_quadraticPolynomial (i : Fin 6) :
    gramPolynomials i = quadraticPolynomial (gramCoefficientMatrix i) := by
  rw [gramCoefficientMatrix_eq_data]
  exact gramPolynomials_eq_coefficients i

theorem quadraticPolynomial_gram_mulVec (c : Fin 6 → ℝ) :
    quadraticPolynomial (gramCoefficientMatrixᵀ *ᵥ c) =
      ∑ i, c i • gramPolynomials i := by
  simp only [quadraticPolynomial, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    map_sum, Finset.sum_mul, gramPolynomials_eq_quadraticPolynomial,
    MvPolynomial.smul_eq_C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  ring

theorem quadraticPolynomial_mem_gramQuadraticSpan_of_range
    (v : Fin 28 → ℝ)
    (hv : v ∈ LinearMap.range gramCoefficientMatrixᵀ.mulVecLin) :
    quadraticPolynomial v ∈ gramQuadraticSpan := by
  obtain ⟨c, hc⟩ := hv
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨c, ?_⟩
  rw [← quadraticPolynomial_gram_mulVec]
  exact congrArg quadraticPolynomial hc

theorem eval_eq_of_mem_gramQuadraticSpan_of_gram_eq
    {p : MvPolynomial (Fin 7) ℝ} (hp : p ∈ gramQuadraticSpan)
    {x y : Coord} (hxy : gramMatrix x = gramMatrix y) :
    MvPolynomial.eval x p = MvPolynomial.eval y p := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    eval_gramPolynomials, hxy]

theorem eval_zero_of_mem_gramQuadraticSpan_of_gram_zero
    {p : MvPolynomial (Fin 7) ℝ} (hp : p ∈ gramQuadraticSpan)
    {x : Coord} (hx : gramMatrix x = 0) : MvPolynomial.eval x p = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    eval_gramPolynomials, hx, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem eventually_zero_of_mem_gramQuadraticSpan
    {p : MvPolynomial (Fin 7) ℝ} (hp : p ∈ gramQuadraticSpan) :
    ∀ᶠ t in 𝓝 (0 : ℝ), MvPolynomial.eval (baseCurve t) p = 0 := by
  filter_upwards [baseCurve_gram_zero] with t ht
  exact eval_zero_of_mem_gramQuadraticSpan_of_gram_zero hp ht

theorem polynomial_baseCurve_approximation_error_isBigO
    (p : MvPolynomial (Fin 7) ℝ) :
    (fun t => MvPolynomial.eval (baseCurve t) p -
      (polynomialAlongApproximation chartApproximation p).eval t)
      =O[𝓝 0] (fun t : ℝ => t^23) := by
  have he := polynomial_chart_approximation_error_isBigO
    unknownApproximation unknownApproximation_zero 23
    chartSystem_unknownApproximation_isBigO p
  simpa only [polynomialAlongApproximation_eval, chartApproximation_eval_eq_chart] using he

theorem linearPolynomial_approximation_coeff (v : Fin 7 → ℝ) (k : Fin 23) :
    (polynomialAlongApproximation chartApproximation (linearPolynomial v)).coeff k =
      (linearCoefficientMatrixOver ℝ *ᵥ v) k := by
  simp only [polynomialAlongApproximation, linearPolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Matrix.mulVec, dotProduct,
    linearCoefficientMatrixOver, chartApproximation]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem quadraticPolynomial_approximation_coeff (v : Fin 28 → ℝ) (k : Fin 23) :
    (polynomialAlongApproximation chartApproximation (quadraticPolynomial v)).coeff k =
      (quadraticCoefficientMatrixOver ℝ *ᵥ v) k := by
  simp only [polynomialAlongApproximation, quadraticPolynomial, quadraticMonomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Matrix.mulVec, dotProduct, quadraticCoefficientMatrixOver, chartApproximation]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem exists_nonzero_coefficient_of_homogeneous_not_mem_gramQuadraticSpan
    {p : MvPolynomial (Fin 7) ℝ}
    (hp : p.IsHomogeneous 1 ∨ p.IsHomogeneous 2)
    (hnot : p ∉ gramQuadraticSpan) :
    ∃ k < 23, (polynomialAlongApproximation chartApproximation p).coeff k ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  rcases hp with hlin | hquad
  · obtain ⟨v, rfl⟩ := homogeneous_one_representation p hlin
    have hv : linearCoefficientMatrixOver ℝ *ᵥ v = 0 := by
      ext k
      rw [← linearPolynomial_approximation_coeff]
      exact hn k k.isLt
    have hz := (matrix_mulVec_eq_zero_iff_of_full_column_rank
      (linearCoefficientMatrixOver ℝ) (linearCoefficientMatrixOver_rank ℝ) v).mp hv
    apply hnot
    simp [hz, linearPolynomial]
  · obtain ⟨v, rfl⟩ := homogeneous_two_representation p hquad
    have hv : v ∈ LinearMap.ker (quadraticCoefficientMatrixOver ℝ).mulVecLin := by
      change quadraticCoefficientMatrixOver ℝ *ᵥ v = 0
      ext k
      rw [← quadraticPolynomial_approximation_coeff]
      exact hn k k.isLt
    rw [quadraticCoefficientMatrixOver_kernel_eq_gram_range] at hv
    exact hnot (quadraticPolynomial_mem_gramQuadraticSpan_of_range v hv)

theorem eventually_nonzero_of_homogeneous_not_mem_gramQuadraticSpan
    {p : MvPolynomial (Fin 7) ℝ}
    (hp : p.IsHomogeneous 1 ∨ p.IsHomogeneous 2)
    (hnot : p ∉ gramQuadraticSpan) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), MvPolynomial.eval (baseCurve t) p ≠ 0 :=
  eventually_ne_zero_of_polynomial_approximation
    (polynomial_baseCurve_approximation_error_isBigO p)
    (exists_nonzero_coefficient_of_homogeneous_not_mem_gramQuadraticSpan hp hnot)

theorem homogeneous_approximation_coefficients_zero_iff
    {p : MvPolynomial (Fin 7) ℝ}
    (hp : p.IsHomogeneous 1 ∨ p.IsHomogeneous 2) :
    (∀ k < 23, (polynomialAlongApproximation chartApproximation p).coeff k = 0) ↔
      p ∈ gramQuadraticSpan := by
  constructor
  · intro hz
    by_contra hnot
    obtain ⟨k, hk, hne⟩ :=
      exists_nonzero_coefficient_of_homogeneous_not_mem_gramQuadraticSpan hp hnot
    exact hne (hz k hk)
  · intro hmem
    exact coefficients_eq_zero_of_eventually_zero_approximation
      (polynomial_baseCurve_approximation_error_isBigO p)
      ((eventually_zero_of_mem_gramQuadraticSpan hmem).filter_mono nhdsWithin_le_nhds)

theorem exists_positive_time_avoid_homogeneous_tests
    (s : Finset (MvPolynomial (Fin 7) ℝ))
    (hs : ∀ p ∈ s, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧ ∀ p ∈ s,
      p ∈ gramQuadraticSpan ∨ MvPolynomial.eval (baseCurve t) p ≠ 0 := by
  classical
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ s,
      p ∈ gramQuadraticSpan ∨ MvPolynomial.eval (baseCurve t) p ≠ 0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro p hp
    by_cases hmem : p ∈ gramQuadraticSpan
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hmem)
    · exact (eventually_nonzero_of_homogeneous_not_mem_gramQuadraticSpan
        (hs p hp) hmem).mono (fun _ ht => Or.inr ht)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ U := nhdsWithin_le_nhds hU
  exact (hu.and (hpos.and hall)).exists

theorem exists_positive_time_homogeneous_evaluation_zero_iff
    (s : Finset (MvPolynomial (Fin 7) ℝ))
    (hs : ∀ p ∈ s, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧ ∀ p ∈ s,
      MvPolynomial.eval (baseCurve t) p = 0 ↔ p ∈ gramQuadraticSpan := by
  have hz : {t : ℝ | gramMatrix (baseCurve t) = 0} ∈ 𝓝 (0 : ℝ) :=
    baseCurve_gram_zero
  obtain ⟨t, htU, hpos, ht⟩ := exists_positive_time_avoid_homogeneous_tests
    s hs (U ∩ {t : ℝ | gramMatrix (baseCurve t) = 0}) (Filter.inter_mem hU hz)
  refine ⟨t, htU.1, hpos, ?_⟩
  intro p hp
  constructor
  · intro hzero
    rcases ht p hp with hmem | hne
    · exact hmem
    · exact (hne hzero).elim
  · intro hmem
    exact eval_zero_of_mem_gramQuadraticSpan_of_gram_zero hmem htU.2

end PBCounterexample.Gram7
