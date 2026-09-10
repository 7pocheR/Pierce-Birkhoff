import PBCounterexample.LowDegreeCoordinates
import PBCounterexample.Gram6Curve

/-! All homogeneous quadratic polynomials in six real variables. -/

namespace PBCounterexample.Gram6

open MvPolynomial
open scoped BigOperators

def quadraticPairs : Fin 21 → Fin 6 × Fin 6 := ![
  (0,0), (0,1), (0,2), (0,3), (0,4), (0,5),
  (1,1), (1,2), (1,3), (1,4), (1,5),
  (2,2), (2,3), (2,4), (2,5),
  (3,3), (3,4), (3,5), (4,4), (4,5), (5,5)]

noncomputable def quadraticExponent (i : Fin 21) : Fin 6 →₀ ℕ :=
  Finsupp.single (quadraticPairs i).1 1 + Finsupp.single (quadraticPairs i).2 1

theorem quadraticPairs_complete : ∀ i j : Fin 6, i ≤ j →
    ∃ k : Fin 21, quadraticPairs k = (i,j) := by decide

theorem quadraticExponent_injective : Function.Injective quadraticExponent := by
  have key : ∀ i j : Fin 21,
      (∀ k : Fin 6,
        ((if k = (quadraticPairs i).1 then 1 else 0) +
          (if k = (quadraticPairs i).2 then 1 else 0) : ℕ) =
        ((if k = (quadraticPairs j).1 then 1 else 0) +
          (if k = (quadraticPairs j).2 then 1 else 0) : ℕ)) → i = j := by
    decide +kernel
  intro i j h
  apply key i j
  intro k
  simpa [quadraticExponent, Finsupp.single_apply, eq_comm] using DFunLike.congr_fun h k

noncomputable def quadraticPolynomial (c : Fin 21 → ℝ) : MvPolynomial (Fin 6) ℝ :=
  ∑ i, C (c i) * (X (quadraticPairs i).1 * X (quadraticPairs i).2)

theorem homogeneous_two_representation
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 2) :
    ∃ c : Fin 21 → ℝ, p = quadraticPolynomial c := by
  refine ⟨fun i => p.coeff (quadraticExponent i), ?_⟩
  exact LowDegreeCoordinates.homogeneous_two_eq_sum quadraticPairs
    quadraticExponent_injective quadraticPairs_complete p hp

theorem quadraticPolynomial_homogeneous (c : Fin 21 → ℝ) :
    (quadraticPolynomial c).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact ((MvPolynomial.isHomogeneous_X ℝ (quadraticPairs i).1).mul
    (MvPolynomial.isHomogeneous_X ℝ (quadraticPairs i).2)).C_mul (c i)

noncomputable def monomialCurve (t : ℝ) : Coord := fun i => t ^ i.val

noncomputable def monomialTangent (t : ℝ) : Coord :=
  fun i => (i.val : ℝ) * t ^ (i.val - 1)

noncomputable def quadraticAlongMonomial (c : Fin 21 → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (c i) * Polynomial.X ^ ((quadraticPairs i).1.val + (quadraticPairs i).2.val)

noncomputable def quadraticAlongTangent (c : Fin 21 → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (c i * (quadraticPairs i).1.val * (quadraticPairs i).2.val) *
    Polynomial.X ^ (((quadraticPairs i).1.val - 1) + ((quadraticPairs i).2.val - 1))

theorem eval_quadraticAlongMonomial (c : Fin 21 → ℝ) (t : ℝ) :
    (quadraticAlongMonomial c).eval t = eval (monomialCurve t) (quadraticPolynomial c) := by
  simp [quadraticAlongMonomial, quadraticPolynomial, monomialCurve, pow_add,
    Polynomial.eval_finsetSum]

theorem eval_quadraticAlongTangent (c : Fin 21 → ℝ) (t : ℝ) :
    (quadraticAlongTangent c).eval t = eval (monomialTangent t) (quadraticPolynomial c) := by
  simp only [quadraticAlongTangent, quadraticPolynomial, Polynomial.eval_finsetSum,
    map_sum, map_mul, eval_C, eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, monomialTangent, pow_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticAlongMonomial_coeff (c : Fin 21 → ℝ) (k : ℕ) :
    (quadraticAlongMonomial c).coeff k =
      ∑ i, if (quadraticPairs i).1.val + (quadraticPairs i).2.val = k then c i else 0 := by
  simp only [quadraticAlongMonomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, eq_comm]

theorem quadraticAlongTangent_coeff (c : Fin 21 → ℝ) (k : ℕ) :
    (quadraticAlongTangent c).coeff k =
      ∑ i, if ((quadraticPairs i).1.val - 1) + ((quadraticPairs i).2.val - 1) = k
        then c i * (quadraticPairs i).1.val * (quadraticPairs i).2.val else 0 := by
  simp only [quadraticAlongTangent, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, eq_comm]

end PBCounterexample.Gram6
