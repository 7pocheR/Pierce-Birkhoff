import PBCounterexample.Gram7CoefficientAlgebra
import Mathlib.LinearAlgebra.Matrix.Block

/-! Transfer of a nonzero integer minor to characteristic zero after clearing row denominators. -/

namespace PBCounterexample.Gram7Coefficient

open Matrix

theorem rational_det_ne_zero_of_modular_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h : (A.map (Int.castRingHom (ZMod 1009))).det ≠ 0) :
    (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
  have hi : A.det ≠ 0 := by
    intro he
    apply h
    change ((Int.castRingHom (ZMod 1009)).mapMatrix A).det = 0
    rw [← RingHom.map_det, he, map_zero]
  change ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0
  rw [← RingHom.map_det]
  change (A.det : ℚ) ≠ 0
  exact_mod_cast hi

theorem rational_det_ne_zero_of_row_clear {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (hclear : ∀ i j, (A i j : ℚ) = (d i : ℚ) * M i j)
    (hmod : (A.map (Int.castRingHom (ZMod 1009))).det ≠ 0) :
    M.det ≠ 0 := by
  have hA : A.map (Int.castRingHom ℚ) = diagonal (fun i => (d i : ℚ)) * M := by
    ext i j
    simpa using hclear i j
  have h := rational_det_ne_zero_of_modular_det A hmod
  rw [hA, det_mul] at h
  exact (mul_ne_zero_iff.mp h).2

theorem cast_det_ne_zero {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (h : M.det ≠ 0) :
    (M.map (algebraMap ℚ K)).det ≠ 0 := by
  change ((algebraMap ℚ K).mapMatrix M).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ K)).mpr h

end PBCounterexample.Gram7Coefficient
