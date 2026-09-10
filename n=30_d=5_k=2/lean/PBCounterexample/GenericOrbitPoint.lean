import PBCounterexample.Function
import PBCounterexample.PolynomialTopology
import PBCounterexample.RationalSubstitution
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Simultaneous nonvanishing on matrix orbits

The common point can be chosen using two matrices with positive determinant.
The proof clears inverse determinants and uses polynomial nonvanishing on open
sets. No connectedness assumption on the real matrix group is needed.
-/

namespace PBCounterexample.GenericOrbitPoint

open MvPolynomial (eval C)
open Matrix
open PBCounterexample.Function (I Coord Point Mat X Y ofMatrices)

noncomputable section

def point (D E : Mat) (U V : Matˣ) : Point :=
  ofMatrices ((U : Mat) * D * ↑(V⁻¹)) ((V : Mat) * E * ↑(U⁻¹))

def firstMatrix : Matrix I I (MvPolynomial Coord ℝ) :=
  fun i j => MvPolynomial.X (false, i, j)

def secondMatrix : Matrix I I (MvPolynomial Coord ℝ) :=
  fun i j => MvPolynomial.X (true, i, j)

@[simp] theorem eval_firstMatrix (z : Point) :
    (eval z).mapMatrix firstMatrix = X z := by
  ext i j
  exact MvPolynomial.eval_X _

@[simp] theorem eval_secondMatrix (z : Point) :
    (eval z).mapMatrix secondMatrix = Y z := by
  ext i j
  exact MvPolynomial.eval_X _

def constantMatrix (A : Mat) : Matrix I I (MvPolynomial Coord ℝ) := C.mapMatrix A

@[simp] theorem eval_constantMatrix (z : Point) (A : Mat) :
    (eval z).mapMatrix (constantMatrix A) = A := by
  ext i j
  exact MvPolynomial.eval_C _

def denominator : MvPolynomial Coord ℝ := firstMatrix.det * secondMatrix.det

@[simp] theorem eval_denominator (z : Point) :
    eval z denominator = (X z).det * (Y z).det := by
  simp only [denominator, map_mul, RingHom.map_det, eval_firstMatrix, eval_secondMatrix]

def numerator (D E : Mat) (c : Coord) : MvPolynomial Coord ℝ :=
  if c.1 then
    secondMatrix.det * (secondMatrix * constantMatrix E * firstMatrix.adjugate) c.2.1 c.2.2
  else
    firstMatrix.det * (firstMatrix * constantMatrix D * secondMatrix.adjugate) c.2.1 c.2.2

theorem eval_numerator_first (D E : Mat) (z : Point) (i j : I) :
    eval z (numerator D E (false, i, j)) =
      (X z).det * (X z * D * (Y z).adjugate) i j := by
  change eval z (firstMatrix.det * _) = _
  rw [map_mul, RingHom.map_det, eval_firstMatrix]
  congr 1
  change ((eval z).mapMatrix
    (firstMatrix * constantMatrix D * secondMatrix.adjugate)) i j = _
  rw [map_mul, map_mul, RingHom.map_adjugate, eval_firstMatrix,
    eval_secondMatrix, eval_constantMatrix]

theorem eval_numerator_second (D E : Mat) (z : Point) (i j : I) :
    eval z (numerator D E (true, i, j)) =
      (Y z).det * (Y z * E * (X z).adjugate) i j := by
  change eval z (secondMatrix.det * _) = _
  rw [map_mul, RingHom.map_det, eval_secondMatrix]
  congr 1
  change ((eval z).mapMatrix
    (secondMatrix * constantMatrix E * firstMatrix.adjugate)) i j = _
  rw [map_mul, map_mul, RingHom.map_adjugate, eval_firstMatrix,
    eval_secondMatrix, eval_constantMatrix]

theorem denominator_units_ne_zero (U V : Matˣ) :
    eval (ofMatrices U V) denominator ≠ 0 := by
  simp only [eval_denominator, Function.X_ofMatrices, Function.Y_ofMatrices]
  exact mul_ne_zero (Matrix.isUnits_det_units U).ne_zero
    (Matrix.isUnits_det_units V).ne_zero

theorem inverse_unit_adjugate (U : Matˣ) :
    (↑(U⁻¹) : Mat) = (U : Mat).det⁻¹ • (U : Mat).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]

theorem numerator_div_denominator (D E : Mat) (U V : Matˣ) :
    (fun c => eval (ofMatrices U V) (numerator D E c) /
      eval (ofMatrices U V) denominator) = point D E U V := by
  have hu := (Matrix.isUnits_det_units U).ne_zero
  have hv := (Matrix.isUnits_det_units V).ne_zero
  funext c
  rcases c with ⟨b, i, j⟩
  cases b
  · rw [eval_numerator_first, eval_denominator]
    simp only [Function.X_ofMatrices, Function.Y_ofMatrices, point, ofMatrices,
      Bool.false_eq_true, ↓reduceIte, inverse_unit_adjugate, Matrix.mul_smul,
      Matrix.smul_apply, smul_eq_mul]
    field_simp
  · rw [eval_numerator_second, eval_denominator]
    simp only [Function.X_ofMatrices, Function.Y_ofMatrices, point, ofMatrices,
      ↓reduceIte, inverse_unit_adjugate, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    field_simp

theorem exists_cleared_polynomial (D E : Mat) (p : MvPolynomial Coord ℝ) :
    ∃ q : MvPolynomial Coord ℝ, ∃ k : ℕ, ∀ U V : Matˣ,
      eval (ofMatrices U V) q =
        ((U : Mat).det * (V : Mat).det) ^ k * eval (point D E U V) p := by
  obtain ⟨q, k, hq⟩ := polynomial_substitution_clear_denominator p denominator (numerator D E)
  refine ⟨q, k, ?_⟩
  intro U V
  have hh := hq (ofMatrices U V) (denominator_units_ne_zero U V)
  rw [numerator_div_denominator] at hh
  simpa only [eval_denominator, Function.X_ofMatrices, Function.Y_ofMatrices] using hh

theorem exists_positive_units_all_nonzero
    (D E : Mat) (S : Finset (MvPolynomial Coord ℝ))
    (hS : ∀ p ∈ S, ∃ U V : Matˣ, eval (point D E U V) p ≠ 0) :
    ∃ U V : Matˣ, 0 < (U : Mat).det ∧ 0 < (V : Mat).det ∧
      ∀ p ∈ S, eval (point D E U V) p ≠ 0 := by
  classical
  choose q k hq using exists_cleared_polynomial D E
  have hqnonzero : ∀ p ∈ S, q p ≠ 0 := by
    intro p hp
    obtain ⟨U, V, huv⟩ := hS p hp
    intro hzero
    have heq := hq p U V
    rw [hzero, map_zero] at heq
    exact (mul_ne_zero
      (pow_ne_zero _ (mul_ne_zero (Matrix.isUnits_det_units U).ne_zero
        (Matrix.isUnits_det_units V).ne_zero)) huv) heq.symm
  have hx : Continuous (fun z : Point => (X z).det) := by
    unfold X
    fun_prop
  have hy : Continuous (fun z : Point => (Y z).det) := by
    unfold Y
    fun_prop
  have hopen : IsOpen {z : Point | 0 < (X z).det ∧ 0 < (Y z).det} :=
    (isOpen_lt continuous_const hx).inter (isOpen_lt continuous_const hy)
  have hnonempty : Set.Nonempty {z : Point | 0 < (X z).det ∧ 0 < (Y z).det} :=
    ⟨ofMatrices 1 1, by simp⟩
  obtain ⟨z, hz, hzq⟩ := exists_all_evals_ne_zero_in_open S q hqnonzero hopen hnonempty
  have hu : IsUnit (X z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hz.1))
  have hv : IsUnit (Y z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hz.2))
  let U : Matˣ := hu.unit
  let V : Matˣ := hv.unit
  have hU : (U : Mat) = X z := hu.unit_spec
  have hV : (V : Mat) = Y z := hv.unit_spec
  have hpoint : ofMatrices U V = z := by
    rw [hU, hV, Function.ofMatrices_X_Y]
  refine ⟨U, V, ?_, ?_, ?_⟩
  · simpa only [hU] using hz.1
  · simpa only [hV] using hz.2
  · intro p hp hzero
    have heq := hq p U V
    rw [hpoint, hzero, mul_zero] at heq
    exact hzq p hp heq

end

end PBCounterexample.GenericOrbitPoint
