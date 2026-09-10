import PBCounterexample.Gram6Variations

/-! Three coordinates on the image of the Gram variation. -/

namespace PBCounterexample.Gram6

open Matrix

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

noncomputable def coordinateCorrection (z : Index → ℝ) : Coord :=
  ![z 0, z 1, z 2, 0, 0, 0]

noncomputable def correctionMatrix (t ρ : ℝ) : Matrix Index Index ℝ :=
  let d₀ := gramPolar (ρ • curve t) ![1,0,0,0,0,0]
  let d₁ := gramPolar (ρ • curve t) ![0,1,0,0,0,0]
  let d₂ := gramPolar (ρ • curve t) ![0,0,1,0,0,0]
  !![d₀ 0 0, d₁ 0 0, d₂ 0 0;
     d₀ 0 1, d₁ 0 1, d₂ 0 1;
     d₀ 2 2, d₁ 2 2, d₂ 2 2]

theorem correctionMatrix_mulVec (t ρ : ℝ) (z : Index → ℝ) :
    correctionMatrix t ρ *ᵥ z =
      gramCoordinates (gramPolar (ρ • curve t) (coordinateCorrection z)) := by
  ext i
  fin_cases i <;>
    norm_num [correctionMatrix, coordinateCorrection, gramCoordinates,
      gramPolar, aMatrix, bMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, sixth_entry, Pi.smul_apply, smul_eq_mul] <;> ring

theorem correctionMatrix_det (t ρ : ℝ) :
    (correctionMatrix t ρ).det = 12*ρ^3*(1+t^2)^6 := by
  norm_num [correctionMatrix, gramPolar, aMatrix, bMatrix, curve,
    Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, sixth_entry, Pi.smul_apply, smul_eq_mul]
  ring

theorem correctionMatrix_det_ne_zero (t ρ : ℝ) (hρ : ρ ≠ 0) :
    (correctionMatrix t ρ).det ≠ 0 := by
  rw [correctionMatrix_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hρ))
    (pow_ne_zero 6 (ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)))

theorem gramCoordinates_functional_injective (t : ℝ)
    (R : Matrix Index Index ℝ) (hSymm : R.IsSymm)
    (hRel : R 0 0 + R 1 1 - R 2 2 = 0) (h02 : R 0 2 = 0)
    (hπ : gramCoordinates R = 0) (hℓ : gramFunctional t R = 0) : R = 0 := by
  have h00 := congrFun hπ (0 : Index)
  have h01 := congrFun hπ (1 : Index)
  have h22 := congrFun hπ (2 : Index)
  norm_num [gramCoordinates, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h00 h01 h22
  have h11 : R 1 1 = 0 := by linarith only [hRel, h00, h22]
  have h12 : R 1 2 = 0 := by
    simp only [gramFunctional, h00, h01, h22, mul_zero, sub_self, zero_add] at hℓ
    linarith only [hℓ]
  have h10 : R 1 0 = 0 := by rw [hSymm.apply 0 1, h01]
  have h20 : R 2 0 = 0 := by rw [hSymm.apply 0 2, h02]
  have h21 : R 2 1 = 0 := by rw [hSymm.apply 1 2, h12]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> assumption

end PBCounterexample.Gram6
