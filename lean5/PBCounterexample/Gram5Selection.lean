import PBCounterexample.Gram5Data
import PBCounterexample.PolynomialSelection

/-! The actual four-label selection and its five closed polynomial pieces. -/

namespace PBCounterexample.Gram5

open Matrix MvPolynomial
open scoped BigOperators

noncomputable section

def minimum : Coord → ℝ := PolynomialSelection.minimum qPolynomial
def f : Coord → ℝ := PolynomialSelection.f qPolynomial determinantPolynomial

theorem minimum_le (z : Coord) (i : Label) : minimum z ≤ q i z :=
  PolynomialSelection.minimum_le qPolynomial z i

theorem le_minimum_iff (z : Coord) (r : ℝ) :
    r ≤ minimum z ↔ ∀ i : Label, r ≤ q i z :=
  PolynomialSelection.le_minimum_iff qPolynomial z r

theorem gram_kernel_zero_of_nonpos (z : Coord)
    (hq : ∀ i : Label, 0 < q i z) (v : Index → ℝ)
    (hv : v ⬝ᵥ (gramMatrix z *ᵥ v) ≤ 0) : v = 0 := by
  have h02 : 0 < 2*q 0 z+6*q 1 z+5*q 3 z := by
    have := hq 0
    have := hq 1
    have := hq 3
    positivity
  have h23 : 0 < q 0 z+2*q 1 z+2*q 3 z := by
    have := hq 0
    have := hq 1
    have := hq 3
    positivity
  have h0 := mul_nonneg (hq 0).le (sq_nonneg (v 0-v 1))
  have h1 := mul_nonneg h02.le (sq_nonneg (v 0-v 2))
  have h2 := mul_nonneg (hq 1).le (sq_nonneg (2*v 0+v 1+v 2))
  have h3 := mul_nonneg (hq 2).le (sq_nonneg (v 1-v 2))
  have h4 := mul_nonneg (hq 3).le (sq_nonneg (v 0+2*v 1+v 2))
  have h5 := mul_nonneg h23.le (sq_nonneg (v 0+v 1+2*v 2))
  have hid := quadratic_simplex_identity z v
  have hs0 : (v 0-v 1)^2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right (by linarith : q 0 z * (v 0-v 1)^2 ≤ 0) (hq 0)
  have hs2 : (2*v 0+v 1+v 2)^2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right
      (by linarith : q 1 z * (2*v 0+v 1+v 2)^2 ≤ 0) (hq 1)
  have hs3 : (v 1-v 2)^2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right (by linarith : q 2 z * (v 1-v 2)^2 ≤ 0) (hq 2)
  have he01 : v 0 = v 1 := by nlinarith [sq_nonneg (v 0-v 1)]
  have he12 : v 1 = v 2 := by nlinarith [sq_nonneg (v 1-v 2)]
  have he0 : v 0 = 0 := by nlinarith [sq_nonneg (2*v 0+v 1+v 2)]
  ext i
  fin_cases i
  · exact he0
  · change v 1 = 0
    exact he01.symm.trans he0
  · change v 2 = 0
    exact he12.symm.trans (he01.symm.trans he0)

theorem positiveMatrix_kernel_zero {z : Coord} (hz : 0 < minimum z)
    (v : Index → ℝ) (hv : positiveMatrix z *ᵥ v = 0) : v = 0 := by
  apply gram_kernel_zero_of_nonpos z
    (fun i => lt_of_lt_of_le hz (minimum_le z i)) v
  rw [quadratic_gram_identity, hv]
  simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, zero_sub]
  have h0 := sq_nonneg ((negativeMatrix z *ᵥ v) 0)
  have h1 := sq_nonneg ((negativeMatrix z *ᵥ v) 1)
  linarith

theorem determinant_ne_zero {z : Coord} (hz : 0 < minimum z) :
    eval z determinantPolynomial ≠ 0 := by
  rw [eval_determinantPolynomial]
  have hi : Function.Injective (positiveMatrix z).mulVec := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply positiveMatrix_kernel_zero hz
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover qPolynomial determinantPolynomial
    (fun _ hz => determinant_ne_zero hz)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem polynomialCover_count : polynomialCover.count = 5 := by
  change Fintype.card (Option (Fin 4)) = 5
  simp

theorem polynomialCover_label (i : Fin polynomialCover.count) :
    polynomialCover.label i = 0 ∨
      ∃ j : Label, polynomialCover.label i = qPolynomial j := by
  change PolynomialSelection.label qPolynomial _ = 0 ∨
    ∃ j : Label, PolynomialSelection.label qPolynomial _ = qPolynomial j
  cases (Fintype.equivFin (Option Label)).symm i with
  | none => exact Or.inl rfl
  | some j => exact Or.inr ⟨j, rfl⟩

theorem f_of_positive {z : Coord} (hh : 0 < minimum z)
    (hd : 0 < determinant z) : f z = minimum z := by
  exact if_pos ⟨hh, hd⟩

theorem f_of_determinant_nonpos {z : Coord} (hd : determinant z ≤ 0) :
    f z = 0 := by
  simp only [f, PolynomialSelection.f]
  exact if_neg (fun h => (not_lt_of_ge hd) h.2)

end

end PBCounterexample.Gram5
