import PBCounterexample.PolynomialTopology
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.DenseEmbedding
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Linear and quadratic forms determined by the two-dimensional matrix projection. -/

namespace PBCounterexample.MatrixProjection

open Matrix
open scoped BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n ℝ

def flatDeterminantPolynomial (n : Type*) [Fintype n] [DecidableEq n] :
    MvPolynomial (n × n) ℝ :=
  Matrix.det (fun i j : n => MvPolynomial.X (i, j))

theorem eval_flatDeterminantPolynomial (z : n × n → ℝ) :
    MvPolynomial.eval z (flatDeterminantPolynomial n) = Matrix.det (Function.curry z : Mat n) := by
  calc
    _ = ((MvPolynomial.eval z).mapMatrix
        (fun i j : n => MvPolynomial.X (i, j))).det := (MvPolynomial.eval z).map_det _
    _ = _ := by
      congr 1
      ext i j
      change MvPolynomial.eval z (MvPolynomial.X (i, j)) = z (i, j)
      exact MvPolynomial.eval_X _

theorem flatDeterminantPolynomial_ne_zero : flatDeterminantPolynomial n ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun ij : n × n => (1 : Mat n) ij.1 ij.2)) h
  rw [eval_flatDeterminantPolynomial] at he
  have hc : (Function.curry (fun ij : n × n => (1 : Mat n) ij.1 ij.2) : Mat n) =
      (1 : Mat n) := rfl
  simp [hc] at he

theorem denseRange_units : DenseRange (fun U : (Mat n)ˣ => (U : Mat n)) := by
  change Dense (Set.range (fun U : (Mat n)ˣ => (U : Mat n)))
  apply dense_iff_inter_open.2
  intro s hs hne
  let e : (n × n → ℝ) ≃ₜ Mat n := Homeomorph.piCurry
  have hpre : IsOpen (e ⁻¹' s) := hs.preimage e.continuous
  have hprenonempty : (e ⁻¹' s).Nonempty := by
    obtain ⟨A, hA⟩ := hne
    exact ⟨e.symm A, by simpa using hA⟩
  obtain ⟨z, hz, hdet⟩ := exists_eval_ne_zero_in_open
    (flatDeterminantPolynomial_ne_zero (n := n)) hpre hprenonempty
  have hunit : IsUnit (e z) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    apply isUnit_iff_ne_zero.2
    exact (eval_flatDeterminantPolynomial z) ▸ hdet
  obtain ⟨U, hU⟩ := hunit
  exact ⟨e z, hz, ⟨U, hU⟩⟩

theorem continuous_vanish_on_all_products (P : Mat n) (F : Mat n → ℝ)
    (hF : Continuous F)
    (hvan : ∀ U V : (Mat n)ˣ, F ((U : Mat n) * P * ↑(V⁻¹)) = 0) :
    ∀ A C : Mat n, F (A * P * C) = 0 := by
  intro A C
  have hclosed : IsClosed {q : Mat n × Mat n | F (q.1 * P * q.2) = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  exact (denseRange_units (n := n)).induction_on₂ hclosed
    (fun U V => by simpa using hvan U (V⁻¹)) A C

theorem unit_as_product (P : Mat n) (a : n) (ha : P a a = 1) (i j : n) :
    (single i a 1 : Mat n) * P * single a j 1 = single i j 1 := by
  simp [ha]

theorem two_units_as_product (P : Mat n) (a b : n)
    (haa : P a a = 1) (hbb : P b b = 1) (hab : P a b = 0) (hba : P b a = 0)
    (i j k l : n) :
    ((single i a 1 + single k b 1 : Mat n) * P * (single a j 1 + single b l 1)) =
      single i j 1 + single k l 1 := by
  simp [Matrix.add_mul, Matrix.mul_add, haa, hbb, hab, hba]

theorem matrix_expansion (A : Mat n) :
    A = ∑ i, ∑ j, A i j • (single i j 1 : Mat n) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp

theorem linear_expansion (L : Mat n →ₗ[ℝ] ℝ) (A : Mat n) :
    L A = ∑ i, ∑ j, A i j * L (single i j 1) := by
  conv_lhs => rw [matrix_expansion A]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem bilinear_expansion (Q : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) (A C : Mat n) :
    Q A C = ∑ i, ∑ j, ∑ k, ∑ l,
      A i j * C k l * Q (single i j 1) (single k l 1) := by
  calc
    Q A C = ∑ i, ∑ j, A i j * Q (single i j 1) C := linear_expansion (Q.flip C) A
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [linear_expansion (Q (single i j 1)) C]
      simp only [Finset.mul_sum, mul_assoc]

theorem continuous_quadratic (Q : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) :
    Continuous (fun A : Mat n => Q A A) := by
  have heq : (fun A : Mat n => Q A A) =
      (fun A : Mat n => ∑ i, ∑ j, ∑ k, ∑ l,
        A i j * A k l * Q (single i j 1) (single k l 1)) :=
    funext (fun A => bilinear_expansion Q A A)
  rw [heq]
  fun_prop

theorem linear_eq_zero_of_projection_vanish (P : Mat n) (a : n) (ha : P a a = 1)
    (L : Mat n →ₗ[ℝ] ℝ)
    (hL : ∀ U V : (Mat n)ˣ, L ((U : Mat n) * P * ↑(V⁻¹)) = 0) : L = 0 := by
  have hall := continuous_vanish_on_all_products P L L.continuous_of_finiteDimensional hL
  have hunit : ∀ i j : n, L (single i j 1) = 0 := by
    intro i j
    simpa [unit_as_product P a ha] using hall (single i a 1) (single a j 1)
  ext A
  rw [linear_expansion]
  simp [hunit]

theorem quadratic_eq_zero_of_projection_vanish (P : Mat n) (a b : n)
    (haa : P a a = 1) (hbb : P b b = 1) (hab : P a b = 0) (hba : P b a = 0)
    (Q : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ)
    (hsym : ∀ A C, Q A C = Q C A)
    (hQ : ∀ U V : (Mat n)ˣ,
      Q ((U : Mat n) * P * ↑(V⁻¹)) ((U : Mat n) * P * ↑(V⁻¹)) = 0) : Q = 0 := by
  have hall := continuous_vanish_on_all_products P (fun A => Q A A) (continuous_quadratic Q) hQ
  have hdiag : ∀ i j : n, Q (single i j 1) (single i j 1) = 0 := by
    intro i j
    simpa [unit_as_product P a haa] using hall (single i a 1) (single a j 1)
  have hunit : ∀ i j k l : n, Q (single i j 1) (single k l 1) = 0 := by
    intro i j k l
    have h := hall (single i a 1 + single k b 1) (single a j 1 + single b l 1)
    rw [two_units_as_product P a b haa hbb hab hba] at h
    simp only [map_add, LinearMap.add_apply, hdiag] at h
    rw [hsym (single k l 1) (single i j 1)] at h
    linarith
  ext A C
  rw [bilinear_expansion]
  simp [hunit]

end

end PBCounterexample.MatrixProjection
