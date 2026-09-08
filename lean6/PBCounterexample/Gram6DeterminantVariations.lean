import PBCounterexample.Gram6Variations

/-! The cubic determinant and its exact directional coefficient. -/

namespace PBCounterexample.Gram6

open Matrix

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

theorem determinant_explicit (v : Coord) :
    (aMatrix v).det = -v 0^2*v 5/2 + (-v 4+v 5/2)*v 0*v 2 -
      v 1^2*v 5/2 + v 1*(v 2+v 3)*v 2 := by
  norm_num [aMatrix, Matrix.det_fin_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

noncomputable def determinantLinearTerm (v w : Coord) : ℝ :=
  -(2*v 0*w 0*v 5 + v 0^2*w 5)/2 +
    (-w 4+w 5/2)*v 0*v 2 + (-v 4+v 5/2)*(w 0*v 2+v 0*w 2) -
    (2*v 1*w 1*v 5 + v 1^2*w 5)/2 +
    w 1*(v 2+v 3)*v 2 + v 1*(w 2+w 3)*v 2 + v 1*(v 2+v 3)*w 2

theorem determinant_add_smul (v w : Coord) (ε : ℝ) :
    (aMatrix (v + ε • w)).det = (aMatrix v).det + ε*determinantLinearTerm v w +
      ε^2*determinantLinearTerm w v + ε^3*(aMatrix w).det := by
  simp only [determinant_explicit, determinantLinearTerm, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_determinant_line (v w : Coord) :
    HasDerivAt (fun ε : ℝ => (aMatrix (v + ε • w)).det)
      (determinantLinearTerm v w) 0 := by
  have hf : (fun ε : ℝ => (aMatrix (v + ε • w)).det) =
      (fun ε : ℝ => (aMatrix v).det + ε*determinantLinearTerm v w +
        ε^2*determinantLinearTerm w v + ε^3*(aMatrix w).det) := by
    funext ε
    exact determinant_add_smul v w ε
  rw [hf]
  convert! ((((hasDerivAt_const (0 : ℝ) (aMatrix v).det).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (determinantLinearTerm v w))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (determinantLinearTerm w v))).add
    (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (aMatrix w).det)) using 1 <;> norm_num

theorem determinantLinearTerm_smul_left (v w : Coord) (c : ℝ) :
    determinantLinearTerm (c • v) w = c^2 * determinantLinearTerm v w := by
  simp only [determinantLinearTerm, Pi.smul_apply, smul_eq_mul]
  ring

theorem determinantLinearTerm_smul_right (v w : Coord) (c : ℝ) :
    determinantLinearTerm v (c • w) = c * determinantLinearTerm v w := by
  simp only [determinantLinearTerm, Pi.smul_apply, smul_eq_mul]
  ring

theorem determinantLinearTerm_sub_right (v w z : Coord) :
    determinantLinearTerm v (w-z) =
      determinantLinearTerm v w - determinantLinearTerm v z := by
  simp only [determinantLinearTerm, Pi.sub_apply]
  ring

theorem determinantLinearTerm_curve_acceleration (t : ℝ) :
    determinantLinearTerm (curve t) (curveAcceleration t) = 0 := by
  norm_num [determinantLinearTerm, curve, curveAcceleration,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem determinantLinearTerm_curve_third (t : ℝ) :
    determinantLinearTerm (curve t) (curveThird t) = -48*(1+t^2)^4 := by
  norm_num [determinantLinearTerm, curve, curveThird,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem determinantLinearTerm_base_normal (t ρ : ℝ) :
    determinantLinearTerm (ρ • curve t) (normalDirection t ρ) = 0 := by
  rw [normalDirection, determinantLinearTerm_smul_left,
    determinantLinearTerm_smul_right, determinantLinearTerm_curve_acceleration,
    mul_zero, mul_zero]

theorem determinantLinearTerm_base_kernelDirection0 (t ρ : ℝ) :
    determinantLinearTerm (ρ • curve t) (kernelDirection0 t) =
      -48*ρ^2*(1+t^2)^4 := by
  rw [kernelDirection0, determinantLinearTerm_smul_left,
    determinantLinearTerm_sub_right, determinantLinearTerm_smul_right,
    determinantLinearTerm_curve_acceleration, determinantLinearTerm_curve_third]
  ring

theorem determinantLinearTerm_base_kernelDirection_pos (t ρ : ℝ) (hρ : ρ ≠ 0) :
    0 < determinantLinearTerm (ρ • curve t) (kernelDirection t) := by
  rw [kernelDirection, determinantLinearTerm_smul_right,
    determinantLinearTerm_base_kernelDirection0]
  have hs : 0 < Real.sqrt (interiorScale t / 1728) :=
    Real.sqrt_pos.2 (div_pos (interiorScale_pos t) (by norm_num))
  have hρ2 : 0 < ρ^2 := sq_pos_of_ne_zero hρ
  have ht : 0 < (1+t^2)^4 := by positivity
  nlinarith only [mul_pos hs (mul_pos hρ2 ht)]

end PBCounterexample.Gram6
