import PBCounterexample.Gram6Curve
import PBCounterexample.Gram6Polarization

/-! Exact first and second variations at the six-coordinate base curve. -/

namespace PBCounterexample.Gram6

open Matrix

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

noncomputable def curveAcceleration (t : ℝ) : Coord := ![
  12*t^2 - 12, 24*t, 12*t^2 + 4, 24*t^2, 24*t, 40*t^3 + 24*t]

noncomputable def curveThird (t : ℝ) : Coord := ![
  24*t, 24, 24*t, 48*t, 24, 120*t^2 + 24]

noncomputable def tangentScale (t : ℝ) : ℝ := 12*(1+t^2)^2

theorem tangentScale_pos (t : ℝ) : 0 < tangentScale t := by
  unfold tangentScale
  positivity

noncomputable def normalDirection (t ρ : ℝ) : Coord :=
  (-(2*ρ*tangentScale t)⁻¹) • curveAcceleration t

noncomputable def kernelDirection0 (t : ℝ) : Coord :=
  curveThird t - (6*t/(1+t^2)) • curveAcceleration t

noncomputable def gramFunctional (t : ℝ) (R : Matrix Index Index ℝ) : ℝ :=
  (t^2-1)*R 0 0 - 2*t*R 0 1 + 2*R 2 2 + 2*R 1 2

noncomputable def gramCoordinates (R : Matrix Index Index ℝ) : Index → ℝ :=
  ![R 0 0, R 0 1, R 2 2]

noncomputable def interiorTarget : Matrix Index Index ℝ := !![
  1, 1/4, 0;
  1/4, 1, 0;
  0, 0, 2]

noncomputable def interiorScale (t : ℝ) : ℝ := t^2 - t/2 + 3

theorem interiorScale_pos (t : ℝ) : 0 < interiorScale t := by
  unfold interiorScale
  nlinarith only [sq_nonneg (t - 1/4)]

theorem gramFunctional_add (t : ℝ) (R S : Matrix Index Index ℝ) :
    gramFunctional t (R + S) = gramFunctional t R + gramFunctional t S := by
  simp only [gramFunctional, Matrix.add_apply]
  ring

theorem gramFunctional_smul (t c : ℝ) (R : Matrix Index Index ℝ) :
    gramFunctional t (c • R) = c * gramFunctional t R := by
  simp only [gramFunctional, Matrix.smul_apply, smul_eq_mul]
  ring

theorem gramFunctional_sub (t : ℝ) (R S : Matrix Index Index ℝ) :
    gramFunctional t (R-S) = gramFunctional t R - gramFunctional t S := by
  simp only [gramFunctional, Matrix.sub_apply]
  ring

theorem gramFunctional_interiorTarget (t : ℝ) :
    gramFunctional t interiorTarget = interiorScale t := by
  norm_num [gramFunctional, interiorTarget, interiorScale,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem gramFunctional_rankOneTarget (t : ℝ) :
    gramFunctional t rankOneTarget = 0 := by
  norm_num [gramFunctional, rankOneTarget,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem gramPolar_curve_acceleration (t : ℝ) :
    gramPolar (curve t) (curveAcceleration t) =
      (-2*tangentScale t) • rankOneTarget := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramPolar, aMatrix, bMatrix, curve, curveAcceleration,
      tangentScale, rankOneTarget, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, sixth_entry] <;> ring

theorem gramPolar_curve_third (t : ℝ) :
    gramPolar (curve t) (curveThird t) =
      (-144*t*(1+t^2)) • rankOneTarget := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramPolar, aMatrix, bMatrix, curve, curveThird,
      rankOneTarget, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, sixth_entry] <;> ring

theorem gramPolar_sub_right (v w z : Coord) :
    gramPolar v (w - z) = gramPolar v w - gramPolar v z := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ z, gramPolar_add_right,
    gramPolar_smul_right]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem gramPolar_base_normal (t ρ : ℝ) (hρ : ρ ≠ 0) :
    gramPolar (ρ • curve t) (normalDirection t ρ) = rankOneTarget := by
  have hd : tangentScale t ≠ 0 := ne_of_gt (tangentScale_pos t)
  rw [normalDirection, gramPolar_smul_left, gramPolar_smul_right,
    gramPolar_curve_acceleration, smul_smul, smul_smul]
  have h : (ρ * (-(2*ρ*tangentScale t)⁻¹)) * (-2*tangentScale t) = 1 := by
    field_simp [hρ, hd]
    <;> ring
  rw [h, one_smul]

theorem gramPolar_base_kernelDirection0 (t ρ : ℝ) :
    gramPolar (ρ • curve t) (kernelDirection0 t) = 0 := by
  have ht : 1+t^2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)
  rw [kernelDirection0, gramPolar_smul_left, gramPolar_sub_right,
    gramPolar_curve_third, gramPolar_smul_right, gramPolar_curve_acceleration]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul,
    tangentScale]
  field_simp
  <;> ring

theorem gramFunctional_gramPolar_base (t ρ : ℝ) (w : Coord) :
    gramFunctional t (gramPolar (ρ • curve t) w) = 0 := by
  rw [gramPolar_smul_left, gramFunctional_smul]
  suffices gramFunctional t (gramPolar (curve t) w) = 0 by rw [this, mul_zero]
  norm_num [gramFunctional, gramPolar, aMatrix, bMatrix, curve,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem gramFunctional_gramMatrix_acceleration (t : ℝ) :
    gramFunctional t (gramMatrix (curveAcceleration t)) = 0 := by
  norm_num [gramFunctional, gramMatrix, aMatrix, bMatrix, curveAcceleration,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem gramFunctional_acceleration_third (t : ℝ) :
    gramFunctional t (gramPolar (curveAcceleration t) (curveThird t)) = 0 := by
  norm_num [gramFunctional, gramPolar, aMatrix, bMatrix, curveAcceleration,
    curveThird, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sixth_entry]
  ring

theorem gramFunctional_gramMatrix_third (t : ℝ) :
    gramFunctional t (gramMatrix (curveThird t)) = 1728 := by
  norm_num [gramFunctional, gramMatrix, aMatrix, bMatrix,
    curveThird, Matrix.cons_val, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, sixth_entry]
  ring

theorem gramFunctional_acceleration_kernelDirection0 (t : ℝ) :
    gramFunctional t (gramPolar (curveAcceleration t) (kernelDirection0 t)) = 0 := by
  rw [kernelDirection0, gramPolar_sub_right, gramPolar_smul_right,
    gramFunctional_sub, gramFunctional_smul, gramFunctional_acceleration_third,
    gramPolar_self, gramFunctional_smul, gramFunctional_gramMatrix_acceleration]
  ring

theorem gramFunctional_gramMatrix_kernelDirection0 (t : ℝ) :
    gramFunctional t (gramMatrix (kernelDirection0 t)) = 1728 := by
  have hdir : kernelDirection0 t =
      curveThird t + (-(6*t/(1+t^2))) • curveAcceleration t := by
    simp only [kernelDirection0, sub_eq_add_neg, neg_smul]
  rw [hdir, gramMatrix_add_smul, gramFunctional_add, gramFunctional_add,
    gramFunctional_smul, gramFunctional_smul, gramFunctional_gramMatrix_third,
    gramPolar_comm (curveThird t), gramFunctional_acceleration_third,
    gramFunctional_gramMatrix_acceleration]
  ring

noncomputable def kernelDirection (t : ℝ) : Coord :=
  (-Real.sqrt (interiorScale t / 1728)) • kernelDirection0 t

theorem gramPolar_base_kernelDirection (t ρ : ℝ) :
    gramPolar (ρ • curve t) (kernelDirection t) = 0 := by
  rw [kernelDirection, gramPolar_smul_right, gramPolar_base_kernelDirection0, smul_zero]

theorem gramFunctional_gramMatrix_normal (t ρ : ℝ) :
    gramFunctional t (gramMatrix (normalDirection t ρ)) = 0 := by
  rw [normalDirection, gramMatrix_smul, gramFunctional_smul,
    gramFunctional_gramMatrix_acceleration, mul_zero]

theorem gramFunctional_normal_kernelDirection (t ρ : ℝ) :
    gramFunctional t (gramPolar (normalDirection t ρ) (kernelDirection t)) = 0 := by
  rw [normalDirection, kernelDirection, gramPolar_smul_left,
    gramPolar_smul_right, gramFunctional_smul, gramFunctional_smul,
    gramFunctional_acceleration_kernelDirection0, mul_zero, mul_zero]

theorem gramFunctional_gramMatrix_kernelDirection (t : ℝ) :
    gramFunctional t (gramMatrix (kernelDirection t)) = interiorScale t := by
  rw [kernelDirection, gramMatrix_smul, gramFunctional_smul,
    gramFunctional_gramMatrix_kernelDirection0, neg_sq,
    Real.sq_sqrt (le_of_lt (div_pos (interiorScale_pos t) (by norm_num)))]
  ring

theorem gramFunctional_normal_add_kernel (t ρ δ : ℝ) :
    gramFunctional t (gramMatrix (normalDirection t ρ + δ • kernelDirection t)) =
      δ^2 * interiorScale t := by
  rw [gramMatrix_add_smul, gramFunctional_add, gramFunctional_add,
    gramFunctional_smul, gramFunctional_smul, gramFunctional_gramMatrix_normal,
    gramFunctional_normal_kernelDirection, gramFunctional_gramMatrix_kernelDirection]
  ring

end PBCounterexample.Gram6
