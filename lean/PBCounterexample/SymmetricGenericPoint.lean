import PBCounterexample.SymmetricFunction
import PBCounterexample.RationalGenericPoint

/-!
# Simultaneous nonvanishing on a symmetric congruence orbit

The orbit coordinates are rational functions of the 25 entries of the
congruence matrix. Their common denominator is the square of its
determinant. Nonzero polynomial restrictions have a common nonvanishing
point with positive congruence determinant.
-/

namespace PBCounterexample.SymmetricGenericPoint

open Matrix MvPolynomial
open PBCounterexample.SymmetricFunction (I Coord Point Mat ofMatrices)

abbrev Param := I × I

def matrix (z : Param → ℝ) : Mat := Matrix.of fun i j => z (i, j)

def matrixCoordinates (U : Mat) : Param → ℝ := fun ij => U ij.1 ij.2

@[simp] theorem matrix_coordinates (U : Mat) : matrix (matrixCoordinates U) = U := rfl

def point (D E : Mat) (U : Matˣ) : Point :=
  ofMatrices ((U : Mat) * D * (U : Mat)ᵀ)
    ((↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat))

theorem X_point (D E : Mat) (U : Matˣ) (hD : D.IsSymm) :
    SymmetricFunction.X (point D E U) = (U : Mat) * D * (U : Mat)ᵀ := by
  apply SymmetricFunction.X_ofMatrices
  change ((U : Mat) * D * (U : Mat)ᵀ)ᵀ = (U : Mat) * D * (U : Mat)ᵀ
  simp only [transpose_mul, transpose_transpose, hD.eq, Matrix.mul_assoc]

theorem Y_point (D E : Mat) (U : Matˣ) (hE : E.IsSymm) :
    SymmetricFunction.Y (point D E U) =
      (↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat) := by
  apply SymmetricFunction.Y_ofMatrices
  change ((↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat))ᵀ =
    (↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat)
  simp only [transpose_mul, transpose_transpose, hE.eq, Matrix.mul_assoc]

noncomputable section

def matrixPolynomial : Matrix I I (MvPolynomial Param ℝ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

def constantMatrix (D : Mat) : Matrix I I (MvPolynomial Param ℝ) := C.mapMatrix D

@[simp] theorem eval_matrixPolynomial (z : Param → ℝ) :
    (eval z).mapMatrix matrixPolynomial = matrix z := by
  ext i j
  exact MvPolynomial.eval_X _

@[simp] theorem eval_constantMatrix (z : Param → ℝ) (D : Mat) :
    (eval z).mapMatrix (constantMatrix D) = D := by
  ext i j
  exact MvPolynomial.eval_C _

theorem eval_transpose (z : Param → ℝ) (M : Matrix I I (MvPolynomial Param ℝ)) :
    (eval z).mapMatrix Mᵀ = ((eval z).mapMatrix M)ᵀ := rfl

def denominator : MvPolynomial Param ℝ := matrixPolynomial.det ^ 2

@[simp] theorem eval_denominator (z : Param → ℝ) :
    eval z denominator = (matrix z).det ^ 2 := by
  simp only [denominator, map_pow, RingHom.map_det, eval_matrixPolynomial]

def numerator (D E : Mat) (c : Coord) : MvPolynomial Param ℝ :=
  if c.1 then
    (matrixPolynomial.adjugateᵀ * constantMatrix E * matrixPolynomial.adjugate)
      c.2.val.1 c.2.val.2
  else
    denominator * (matrixPolynomial * constantMatrix D * matrixPolynomialᵀ)
      c.2.val.1 c.2.val.2

theorem eval_numerator_first (D E : Mat) (z : Param → ℝ)
    (c : SymmetricFunction.Upper) :
    eval z (numerator D E (false, c)) =
      (matrix z).det ^ 2 * (matrix z * D * (matrix z)ᵀ) c.val.1 c.val.2 := by
  change eval z (denominator * _) = _
  rw [map_mul, eval_denominator]
  congr 1
  change ((eval z).mapMatrix
    (matrixPolynomial * constantMatrix D * matrixPolynomialᵀ)) c.val.1 c.val.2 = _
  rw [map_mul, map_mul, eval_transpose, eval_matrixPolynomial, eval_constantMatrix]

theorem eval_numerator_second (D E : Mat) (z : Param → ℝ)
    (c : SymmetricFunction.Upper) :
    eval z (numerator D E (true, c)) =
      ((matrix z).adjugateᵀ * E * (matrix z).adjugate) c.val.1 c.val.2 := by
  change ((eval z).mapMatrix
    (matrixPolynomial.adjugateᵀ * constantMatrix E * matrixPolynomial.adjugate))
      c.val.1 c.val.2 = _
  rw [map_mul, map_mul, eval_transpose, RingHom.map_adjugate,
    eval_matrixPolynomial, eval_constantMatrix]

theorem denominator_unit_ne_zero (U : Matˣ) :
    eval (matrixCoordinates U) denominator ≠ 0 := by
  rw [eval_denominator, matrix_coordinates]
  exact pow_ne_zero _ (Matrix.isUnits_det_units U).ne_zero

theorem inverse_unit_adjugate (U : Matˣ) :
    (↑(U⁻¹) : Mat) = (U : Mat).det⁻¹ • (U : Mat).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]

theorem numerator_div_denominator (D E : Mat) (U : Matˣ) :
    (fun c => eval (matrixCoordinates U) (numerator D E c) /
      eval (matrixCoordinates U) denominator) = point D E U := by
  have hdet := (Matrix.isUnits_det_units U).ne_zero
  funext c
  rcases c with ⟨b, ij⟩
  cases b
  · rw [eval_numerator_first, eval_denominator, matrix_coordinates]
    simp only [point, ofMatrices, Bool.false_eq_true, ↓reduceIte]
    field_simp
  · rw [eval_numerator_second, eval_denominator, matrix_coordinates]
    simp only [point, ofMatrices, ↓reduceIte, inverse_unit_adjugate,
      transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_apply, smul_eq_mul]
    field_simp

theorem exists_positive_unit_all_nonzero
    (D E : Mat) (S : Finset (MvPolynomial Coord ℝ))
    (hS : ∀ p ∈ S, ∃ U : Matˣ, eval (point D E U) p ≠ 0) :
    ∃ U : Matˣ, 0 < (U : Mat).det ∧ ∀ p ∈ S, eval (point D E U) p ≠ 0 := by
  have hopen : IsOpen {z : Param → ℝ | 0 < (matrix z).det} := by
    apply isOpen_lt continuous_const
    unfold matrix
    fun_prop
  have hnonempty : Set.Nonempty {z : Param → ℝ | 0 < (matrix z).det} := by
    refine ⟨matrixCoordinates 1, ?_⟩
    simp
  have hd : ∀ z ∈ {z : Param → ℝ | 0 < (matrix z).det}, eval z denominator ≠ 0 := by
    intro z hz
    rw [eval_denominator]
    exact pow_ne_zero _ (ne_of_gt hz)
  have hp : ∀ p ∈ S, ∃ z : Param → ℝ, eval z denominator ≠ 0 ∧
      eval (fun c => eval z (numerator D E c) / eval z denominator) p ≠ 0 := by
    intro p hp
    obtain ⟨U, hU⟩ := hS p hp
    refine ⟨matrixCoordinates U, denominator_unit_ne_zero U, ?_⟩
    simpa only [numerator_div_denominator] using hU
  obtain ⟨z, hz, hnonzero⟩ := exists_all_rational_evals_ne_zero_in_open
    S id denominator (numerator D E) hp hopen hnonempty hd
  have hu : IsUnit (matrix z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hz))
  let U : Matˣ := hu.unit
  have hU : (U : Mat) = matrix z := hu.unit_spec
  have hcoord : matrixCoordinates U = z := by
    rw [hU]
    rfl
  refine ⟨U, ?_, ?_⟩
  · simpa only [hU, Set.mem_setOf_eq] using hz
  · intro p hp
    have h := hnonzero p hp
    rw [← hcoord, numerator_div_denominator] at h
    exact h

end

end PBCounterexample.SymmetricGenericPoint
