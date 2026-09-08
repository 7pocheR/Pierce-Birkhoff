import PBCounterexample.Gram6MonomialKernel
import PBCounterexample.PolynomialSubstitution
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The joint quadratic kernel in the original six coordinates

The explicit inverse linear coordinate changes induce inverse algebra
homomorphisms on the entire polynomial ring over `ℝ`. Transport of the
monomial-curve kernel identifies the actual three Gram polynomials.
-/

noncomputable section

namespace PBCounterexample.Gram6

open MvPolynomial Matrix
open scoped BigOperators

private theorem kernel_sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

def fromMonomialPolynomial : Fin 6 → MvPolynomial (Fin 6) ℝ := ![
  X 0 - C 6 * X 2 + X 4,
  -(C 4 * X 1) + C 4 * X 3,
  X 0 + C 2 * X 2 + X 4,
  -(C 2 * X 0) + C 2 * X 4,
  C 4 * X 1 + C 4 * X 3,
  C 2 * X 1 + C 4 * X 3 + C 2 * X 5]

def monomialCoordinatesPolynomial : Fin 6 → MvPolynomial (Fin 6) ℝ := ![
  C (1/8) * (X 0 + C 3 * X 2 - C 2 * X 3),
  C (1/8) * (X 4 - X 1),
  C (1/8) * (X 2 - X 0),
  C (1/8) * (X 4 + X 1),
  C (1/8) * (X 0 + C 3 * X 2 + C 2 * X 3),
  C (1/8) * (C 4 * X 5 - C 3 * X 4 - X 1)]

@[simp] theorem eval_fromMonomialPolynomial (v : Coord) (i : Fin 6) :
    eval v (fromMonomialPolynomial i) = fromMonomial v i := by
  fin_cases i <;>
    norm_num [fromMonomialPolynomial, fromMonomial, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

@[simp] theorem eval_monomialCoordinatesPolynomial (w : Coord) (i : Fin 6) :
    eval w (monomialCoordinatesPolynomial i) = monomialCoordinates w i := by
  fin_cases i <;>
    norm_num [monomialCoordinatesPolynomial, monomialCoordinates, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

theorem fromMonomialPolynomial_homogeneous (i : Fin 6) :
    (fromMonomialPolynomial i).IsHomogeneous 1 := by
  have hX (k : Fin 6) := MvPolynomial.isHomogeneous_X ℝ k
  fin_cases i
  · exact ((hX 0).sub ((hX 2).C_mul 6)).add (hX 4)
  · exact (((hX 1).C_mul 4).neg).add ((hX 3).C_mul 4)
  · exact ((hX 0).add ((hX 2).C_mul 2)).add (hX 4)
  · exact (((hX 0).C_mul 2).neg).add ((hX 4).C_mul 2)
  · exact ((hX 1).C_mul 4).add ((hX 3).C_mul 4)
  · exact (((hX 1).C_mul 2).add ((hX 3).C_mul 4)).add ((hX 5).C_mul 2)

theorem monomialCoordinatesPolynomial_homogeneous (i : Fin 6) :
    (monomialCoordinatesPolynomial i).IsHomogeneous 1 := by
  have hX (k : Fin 6) := MvPolynomial.isHomogeneous_X ℝ k
  fin_cases i
  · exact (((hX 0).add ((hX 2).C_mul 3)).sub ((hX 3).C_mul 2)).C_mul (1/8 : ℝ)
  · exact ((hX 4).sub (hX 1)).C_mul (1/8 : ℝ)
  · exact ((hX 2).sub (hX 0)).C_mul (1/8 : ℝ)
  · exact ((hX 4).add (hX 1)).C_mul (1/8 : ℝ)
  · exact (((hX 0).add ((hX 2).C_mul 3)).add ((hX 3).C_mul 2)).C_mul (1/8 : ℝ)
  · exact ((((hX 5).C_mul 4).sub ((hX 4).C_mul 3)).sub (hX 1)).C_mul (1/8 : ℝ)

/-- Substitute the original coordinates as linear polynomials in monomial coordinates. -/
def pullToMonomial :
    MvPolynomial (Fin 6) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ :=
  bind₁ fromMonomialPolynomial

/-- Substitute the monomial coordinates as linear polynomials in the original coordinates. -/
def pullFromMonomial :
    MvPolynomial (Fin 6) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ :=
  bind₁ monomialCoordinatesPolynomial

@[simp] theorem pullToMonomial_C (r : ℝ) : pullToMonomial (C r) = C r :=
  bind₁_C_right fromMonomialPolynomial r

@[simp] theorem pullFromMonomial_C (r : ℝ) : pullFromMonomial (C r) = C r :=
  bind₁_C_right monomialCoordinatesPolynomial r

@[simp] theorem eval_pullToMonomial (p : MvPolynomial (Fin 6) ℝ) (v : Coord) :
    eval v (pullToMonomial p) = eval (fromMonomial v) p := by
  rw [pullToMonomial, PBCounterexample.eval_polynomial_substitution]
  simp only [eval_fromMonomialPolynomial]

@[simp] theorem eval_pullFromMonomial (p : MvPolynomial (Fin 6) ℝ) (w : Coord) :
    eval w (pullFromMonomial p) = eval (monomialCoordinates w) p := by
  rw [pullFromMonomial, PBCounterexample.eval_polynomial_substitution]
  simp only [eval_monomialCoordinatesPolynomial]

@[simp] theorem pullFromMonomial_pullToMonomial (p : MvPolynomial (Fin 6) ℝ) :
    pullFromMonomial (pullToMonomial p) = p := by
  apply MvPolynomial.funext
  intro w
  simp only [eval_pullFromMonomial, eval_pullToMonomial,
    fromMonomial_monomialCoordinates]

@[simp] theorem pullToMonomial_pullFromMonomial (p : MvPolynomial (Fin 6) ℝ) :
    pullToMonomial (pullFromMonomial p) = p := by
  apply MvPolynomial.funext
  intro v
  simp only [eval_pullToMonomial, eval_pullFromMonomial,
    monomialCoordinates_fromMonomial]

def polynomialCoordinateEquiv :
    MvPolynomial (Fin 6) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 6) ℝ :=
  AlgEquiv.ofAlgHom pullToMonomial pullFromMonomial
    (DFunLike.ext _ _ fun p => pullToMonomial_pullFromMonomial p)
    (DFunLike.ext _ _ fun p => pullFromMonomial_pullToMonomial p)

theorem pullToMonomial_injective : Function.Injective pullToMonomial :=
  polynomialCoordinateEquiv.injective

theorem pullFromMonomial_injective : Function.Injective pullFromMonomial :=
  polynomialCoordinateEquiv.symm.injective

theorem pullToMonomial_homogeneous {p : MvPolynomial (Fin 6) ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) : (pullToMonomial p).IsHomogeneous d :=
  PBCounterexample.homogeneous_polynomial_substitution fromMonomialPolynomial hp
    fromMonomialPolynomial_homogeneous

theorem pullFromMonomial_homogeneous {p : MvPolynomial (Fin 6) ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) : (pullFromMonomial p).IsHomogeneous d :=
  PBCounterexample.homogeneous_polynomial_substitution monomialCoordinatesPolynomial hp
    monomialCoordinatesPolynomial_homogeneous

theorem fromMonomial_monomialCurve (t : ℝ) :
    fromMonomial (monomialCurve t) = curve t := by
  have h : monomialCurve t = ![1, t, t^2, t^3, t^4, t^5] := by
    ext i
    fin_cases i <;>
      norm_num [monomialCurve, Matrix.cons_val, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry]
  rw [h]
  exact fromMonomial_curve t

theorem fromMonomial_monomialTangent (t : ℝ) :
    fromMonomial (monomialTangent t) = curveTangent t := by
  ext i
  fin_cases i <;>
    norm_num [monomialTangent, fromMonomial, curveTangent, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

theorem pullToMonomial_gramPolynomial00 :
    pullToMonomial (gramPolynomial 0 0) = C 16 * tangentQuadratic 0 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_pullToMonomial, eval_gramPolynomial]
  norm_num [gramMatrix, aMatrix, bMatrix, fromMonomial, tangentQuadratic,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

theorem pullToMonomial_gramPolynomial01 :
    pullToMonomial (gramPolynomial 0 1) = C 8 * tangentQuadratic 1 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_pullToMonomial, eval_gramPolynomial]
  norm_num [gramMatrix, aMatrix, bMatrix, fromMonomial, tangentQuadratic,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

theorem pullToMonomial_gramPolynomial12_add22 :
    pullToMonomial (gramPolynomial 1 2 + gramPolynomial 2 2) =
      C 8 * (tangentQuadratic 0 + tangentQuadratic 2) := by
  apply MvPolynomial.funext
  intro v
  rw [eval_pullToMonomial]
  simp only [map_add, eval_gramPolynomial]
  norm_num [gramMatrix, aMatrix, bMatrix, fromMonomial, tangentQuadratic,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, kernel_sixth_entry] <;> ring

/-- The complete real homogeneous quadratic kernel in the original coordinates. -/
theorem homogeneous_quadratic_original_kernel
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 2)
    (hcurve : ∀ t : ℝ, eval (curve t) p = 0)
    (htangent : ∀ t : ℝ, eval (curveTangent t) p = 0) :
    ∃ a b c : ℝ, p = C a * gramPolynomial 0 0 + C b * gramPolynomial 0 1 +
      C c * (gramPolynomial 1 2 + gramPolynomial 2 2) := by
  have hc : ∀ t : ℝ, eval (monomialCurve t) (pullToMonomial p) = 0 := by
    intro t
    rw [eval_pullToMonomial, fromMonomial_monomialCurve]
    exact hcurve t
  have ht : ∀ t : ℝ, eval (monomialTangent t) (pullToMonomial p) = 0 := by
    intro t
    rw [eval_pullToMonomial, fromMonomial_monomialTangent]
    exact htangent t
  obtain ⟨a, b, c, hk⟩ := homogeneous_quadratic_monomial_kernel
    (pullToMonomial p) (pullToMonomial_homogeneous hp) hc ht
  refine ⟨(a-c)/16, b/8, c/8, ?_⟩
  apply pullToMonomial_injective
  rw [hk, map_add pullToMonomial, map_add pullToMonomial,
    map_mul pullToMonomial, map_mul pullToMonomial, map_mul pullToMonomial,
    pullToMonomial_C, pullToMonomial_C, pullToMonomial_C,
    pullToMonomial_gramPolynomial00, pullToMonomial_gramPolynomial01,
    pullToMonomial_gramPolynomial12_add22]
  apply MvPolynomial.funext
  intro v
  simp only [map_add, map_mul, eval_C]
  ring

private theorem gram00_joint_vanishing (t : ℝ) :
    eval (curve t) (gramPolynomial 0 0) = 0 ∧
      eval (curveTangent t) (gramPolynomial 0 0) = 0 := by
  constructor
  · rw [eval_gramPolynomial, gramMatrix_curve]
    rfl
  · rw [eval_gramPolynomial, gramMatrix_curveTangent]
    change (12 * (1 + t^2)^2) * 0 = 0
    exact mul_zero _

private theorem gram01_joint_vanishing (t : ℝ) :
    eval (curve t) (gramPolynomial 0 1) = 0 ∧
      eval (curveTangent t) (gramPolynomial 0 1) = 0 := by
  constructor
  · rw [eval_gramPolynomial, gramMatrix_curve]
    rfl
  · rw [eval_gramPolynomial, gramMatrix_curveTangent]
    change (12 * (1 + t^2)^2) * 0 = 0
    exact mul_zero _

private theorem gram12_add22_joint_vanishing (t : ℝ) :
    eval (curve t) (gramPolynomial 1 2 + gramPolynomial 2 2) = 0 ∧
      eval (curveTangent t) (gramPolynomial 1 2 + gramPolynomial 2 2) = 0 := by
  constructor
  · simp only [map_add, eval_gramPolynomial, gramMatrix_curve, Matrix.zero_apply,
      zero_add]
  · simp only [map_add, eval_gramPolynomial, gramMatrix_curveTangent]
    change (12 * (1 + t^2)^2) * (-1) + (12 * (1 + t^2)^2) * 1 = 0
    ring

theorem homogeneous_quadratic_original_kernel_iff (p : MvPolynomial (Fin 6) ℝ) :
    (p.IsHomogeneous 2 ∧ (∀ t : ℝ, eval (curve t) p = 0) ∧
      (∀ t : ℝ, eval (curveTangent t) p = 0)) ↔
    ∃ a b c : ℝ, p = C a * gramPolynomial 0 0 + C b * gramPolynomial 0 1 +
      C c * (gramPolynomial 1 2 + gramPolynomial 2 2) := by
  constructor
  · rintro ⟨hp, hc, ht⟩
    exact homogeneous_quadratic_original_kernel p hp hc ht
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (((gramPolynomial_homogeneous 0 0).C_mul a).add
        ((gramPolynomial_homogeneous 0 1).C_mul b)).add
        (((gramPolynomial_homogeneous 1 2).add
          (gramPolynomial_homogeneous 2 2)).C_mul c)
    · intro t
      have h0 := (gram00_joint_vanishing t).1
      have h1 := (gram01_joint_vanishing t).1
      have h2 := (gram12_add22_joint_vanishing t).1
      rw [map_add, map_add, map_mul, map_mul, map_mul, h0, h1, h2]
      simp only [mul_zero, zero_add]
    · intro t
      have h0 := (gram00_joint_vanishing t).2
      have h1 := (gram01_joint_vanishing t).2
      have h2 := (gram12_add22_joint_vanishing t).2
      rw [map_add, map_add, map_mul, map_mul, map_mul, h0, h1, h2]
      simp only [mul_zero, zero_add]

private theorem linear_monomial_coeff (c : Fin 6 → ℝ) (i : Fin 6) :
    (∑ j : Fin 6, Polynomial.C (c j) * Polynomial.X ^ j.val).coeff i.val = c i := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Fin.val_inj]
  simp

theorem homogeneous_linear_monomial_kernel
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 1)
    (hcurve : ∀ t : ℝ, eval (monomialCurve t) p = 0) : p = 0 := by
  classical
  let c : Fin 6 → ℝ := fun i => p.coeff (Finsupp.single i 1)
  have hp' : p = ∑ i : Fin 6, C (c i) * X i :=
    LowDegreeCoordinates.homogeneous_one_eq_sum p hp
  have hs : (∑ i : Fin 6, Polynomial.C (c i) * Polynomial.X ^ i.val) = 0 := by
    apply Polynomial.funext
    intro t
    have ht := hcurve t
    rw [hp'] at ht
    simpa [Polynomial.eval_finsetSum, monomialCurve] using ht
  have hc (i : Fin 6) : c i = 0 := by
    simpa only [linear_monomial_coeff, Polynomial.coeff_zero] using
      congrArg (fun q : Polynomial ℝ => q.coeff i.val) hs
  rw [hp']
  simp only [hc, C_0, zero_mul, Finset.sum_const_zero]

/-- No nonzero homogeneous linear polynomial vanishes on the entire original curve. -/
theorem homogeneous_linear_original_kernel
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 1)
    (hcurve : ∀ t : ℝ, eval (curve t) p = 0) : p = 0 := by
  have hc : ∀ t : ℝ, eval (monomialCurve t) (pullToMonomial p) = 0 := by
    intro t
    rw [eval_pullToMonomial, fromMonomial_monomialCurve]
    exact hcurve t
  have hz := homogeneous_linear_monomial_kernel (pullToMonomial p)
    (pullToMonomial_homogeneous hp) hc
  apply pullToMonomial_injective
  rw [map_zero]
  exact hz

theorem exists_curve_eval_ne_zero_of_homogeneous_one
    (p : MvPolynomial (Fin 6) ℝ) (hp : p.IsHomogeneous 1) (hne : p ≠ 0) :
    ∃ t : ℝ, eval (curve t) p ≠ 0 := by
  classical
  by_contra h
  apply hne
  apply homogeneous_linear_original_kernel p hp
  intro t
  by_contra ht
  exact h ⟨t, ht⟩

end PBCounterexample.Gram6
