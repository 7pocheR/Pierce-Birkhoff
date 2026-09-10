import PBCounterexample.Gram6Function

/-!
The quantitative Gram estimate and stability of the determinant orientation
under independent errors in its two cofactors.
-/

namespace PBCounterexample.Quadratic8Geometry

open Matrix MvPolynomial
open scoped BigOperators

theorem minimum_le_label (w : Gram6.Coord) (i : Fin 4) :
    Gram6.minimum w ≤ eval w (Gram6.labelPolynomial i) := by
  let a : Gram6.Label := ⟨Gram6.fourEdges i, by fin_cases i <;> decide⟩
  have ha := PolynomialSelection.minimum_le Gram6.qPolynomial w a
  change Gram6.minimum w ≤ eval w (Gram6.allQuadratics (Gram6.fourEdges i)) at ha
  simpa only [Gram6.allQuadratics_fourEdges] using ha

private theorem four_label_margin (a b d e h X Y Z : ℝ) (hh : 0 ≤ h)
    (h1 : h ≤ -10*b+2*d+2*e) (h2 : h ≤ 4*a+2*b-2*d-2*e)
    (h3 : h ≤ -4*a+2*b+6*d-10*e) (h4 : h ≤ -4*a+2*b+2*d+2*e) :
    h/4*(X^2+Y^2+Z^2) ≤ a*X^2+2*b*X*Y+(d-a)*Y^2+2*e*Y*Z+d*Z^2 := by
  let q1 := -10*b+2*d+2*e
  let q2 := 4*a+2*b-2*d-2*e
  let q3 := -4*a+2*b+6*d-10*e
  let q4 := -4*a+2*b+2*d+2*e
  have p1 : 0 ≤ q1-h := sub_nonneg.mpr h1
  have p2 : 0 ≤ q2-h := sub_nonneg.mpr h2
  have p3 : 0 ≤ q3-h := sub_nonneg.mpr h3
  have p4 : 0 ≤ q4-h := sub_nonneg.mpr h4
  have p02 : 0 ≤ 2*q1+6*q2+5*q4-h := by dsimp [q1,q2,q4] at *; linarith
  have p23 : 0 ≤ q1+2*q2+2*q4-h := by dsimp [q1,q2,q4] at *; linarith
  have hsum : 0 ≤
      (q1-h)*(X-Y)^2 + (2*q1+6*q2+5*q4-h)*(X-Z)^2 +
      (q2-h)*(2*X+Y+Z)^2 + (q3-h)*(Y-Z)^2 +
      (q4-h)*(X+2*Y+Z)^2 + (q1+2*q2+2*q4-h)*(X+Y+2*Z)^2 +
      4*h*(X+Y+Z)^2 := by
    positivity
  have hid :
      (q1-h)*(X-Y)^2 + (2*q1+6*q2+5*q4-h)*(X-Z)^2 +
      (q2-h)*(2*X+Y+Z)^2 + (q3-h)*(Y-Z)^2 +
      (q4-h)*(X+2*Y+Z)^2 + (q1+2*q2+2*q4-h)*(X+Y+2*Z)^2 +
      4*h*(X+Y+Z)^2 =
      16*(a*X^2+2*b*X*Y+(d-a)*Y^2+2*e*Y*Z+d*Z^2 -
        h/4*(X^2+Y^2+Z^2)) := by
    dsimp [q1,q2,q3,q4]
    ring
  rw [hid] at hsum
  linarith

theorem gram_margin (w : Gram6.Coord) (hw : 0 < Gram6.minimum w)
    (v : Fin 3 → ℝ) :
    Gram6.minimum w/4*((v 0)^2+(v 1)^2+(v 2)^2) ≤
      v ⬝ᵥ (Gram6.gramMatrix w *ᵥ v) := by
  have h1 := minimum_le_label w 0
  have h2 := minimum_le_label w 1
  have h3 := minimum_le_label w 2
  have h4 := minimum_le_label w 3
  norm_num [Gram6.labelPolynomial, Matrix.cons_val, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3 h4
  have hm := four_label_margin (Gram6.gramMatrix w 0 0)
    (Gram6.gramMatrix w 0 1) (Gram6.gramMatrix w 2 2)
    (Gram6.gramMatrix w 1 2) (Gram6.minimum w) (v 0) (v 1) (v 2)
    hw.le (by nlinarith only [h1]) (by nlinarith only [h2])
    (by nlinarith only [h3]) (by nlinarith only [h4])
  have he : v ⬝ᵥ (Gram6.gramMatrix w *ᵥ v) =
      Gram6.gramMatrix w 0 0*(v 0)^2 + 2*Gram6.gramMatrix w 0 1*v 0*v 1 +
      (Gram6.gramMatrix w 2 2-Gram6.gramMatrix w 0 0)*(v 1)^2 +
      2*Gram6.gramMatrix w 1 2*v 1*v 2 + Gram6.gramMatrix w 2 2*(v 2)^2 := by
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
      Gram6.gramMatrix, Gram6.aMatrix, Gram6.bMatrix, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rwa [he]

theorem gram_le_weighted_squares (w : Gram6.Coord) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (Gram6.gramMatrix w *ᵥ v) ≤
      ((Gram6.aMatrix w *ᵥ v) 0)^2 + ((Gram6.aMatrix w *ᵥ v) 1)^2 +
      3*((Gram6.aMatrix w *ᵥ v) 2)^2 := by
  have he : v ⬝ᵥ (Gram6.gramMatrix w *ᵥ v) =
      ((Gram6.aMatrix w *ᵥ v) 0)^2 + ((Gram6.aMatrix w *ᵥ v) 1)^2 +
      3*((Gram6.aMatrix w *ᵥ v) 2)^2 -
      (((Gram6.bMatrix w *ᵥ v) 0)^2 + ((Gram6.bMatrix w *ᵥ v) 1)^2) := by
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Gram6.gramMatrix]
    ring
  rw [he]
  nlinarith only [sq_nonneg ((Gram6.bMatrix w *ᵥ v) 0),
    sq_nonneg ((Gram6.bMatrix w *ᵥ v) 1)]

theorem determinant_formula (w : Gram6.Coord) :
    (Gram6.aMatrix w).det =
      w 2*(w 0*(-w 4+w 5/2)+w 1*(w 2+w 3)) -
      (w 5/2)*((w 0)^2+(w 1)^2) := by
  norm_num [Gram6.aMatrix, Matrix.det_fin_three, Matrix.cons_val,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem determinant_sq_bound (w : Gram6.Coord) (hw : 0 < Gram6.minimum w) :
    (Gram6.minimum w/4)^2*((w 2)^2+(w 5/2)^2) ≤ (Gram6.aMatrix w).det^2 := by
  let α := Gram6.minimum w/4
  let ρ := (w 0)^2+(w 1)^2
  let N := (w 2)^2+(w 5/2)^2
  let D := (Gram6.aMatrix w).det
  let W := -(w 1)*(w 0*(w 5/2)-(-w 4+w 5/2)*w 2) +
    w 0*(w 1*(w 5/2)-(w 2+w 3)*w 2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hρ : α ≤ ρ := by
    have hm := le_trans (gram_margin w hw ![0,0,1])
      (gram_le_weighted_squares w ![0,0,1])
    norm_num [Gram6.aMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hm
    dsimp [α,ρ]
    nlinarith only [hm]
  have hρpos : 0 < ρ := lt_of_lt_of_le hα hρ
  let v : Fin 3 → ℝ := ![ρ*(w 5/2), -ρ*w 2, -W]
  have hv0 : (Gram6.aMatrix w *ᵥ v) 0 = -w 0*D := by
    dsimp [v,ρ,W,D]
    rw [determinant_formula]
    norm_num [Gram6.aMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hv1 : (Gram6.aMatrix w *ᵥ v) 1 = -w 1*D := by
    dsimp [v,ρ,W,D]
    rw [determinant_formula]
    norm_num [Gram6.aMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hv2 : (Gram6.aMatrix w *ᵥ v) 2 = 0 := by
    norm_num [v, Gram6.aMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hm := le_trans (gram_margin w hw v) (gram_le_weighted_squares w v)
  rw [hv0,hv1,hv2] at hm
  have he : α*(ρ^2*N+W^2) ≤ ρ*D^2 := by
    calc
      α*(ρ^2*N+W^2) =
          Gram6.minimum w/4*((v 0)^2+(v 1)^2+(v 2)^2) := by
        simp only [α,N,v,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
        ring
      _ ≤ (-w 0*D)^2+(-w 1*D)^2+3*0^2 := hm
      _ = ρ*D^2 := by dsimp [ρ]; ring
  have hc : α*ρ*N ≤ D^2 := by
    apply (mul_le_mul_iff_right₀ hρpos).mp
    nlinarith only [he, mul_nonneg hα.le (sq_nonneg W)]
  have hαN : 0 ≤ α*N := mul_nonneg hα.le hN
  have hmul := mul_le_mul_of_nonneg_right hρ hαN
  change α^2*N ≤ D^2
  nlinarith only [hc,hmul]

theorem third_row_sq_pos (w : Gram6.Coord) (hw : 0 < Gram6.minimum w) :
    0 < (w 2)^2+(w 5/2)^2 := by
  have hd := Gram6.determinant_ne_zero hw
  rw [Gram6.eval_determinantPolynomial] at hd
  by_contra hn
  have hz : w 2 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 5/2)]
  have hr : w 5/2 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 5/2)]
  apply hd
  rw [determinant_formula,hz,hr]
  ring

theorem determinant_bound (w : Gram6.Coord) (hw : 0 < Gram6.minimum w) :
    Gram6.minimum w/4*Real.sqrt ((w 2)^2+(w 5/2)^2) ≤ |(Gram6.aMatrix w).det| := by
  have hs := Real.sq_sqrt (le_of_lt (third_row_sq_pos w hw))
  have hb := determinant_sq_bound w hw
  have hn : 0 ≤ Gram6.minimum w/4*Real.sqrt ((w 2)^2+(w 5/2)^2) := by positivity
  apply (sq_le_sq₀ hn (abs_nonneg _)).mp
  rw [mul_pow,hs,sq_abs]
  exact hb

private theorem cofactor_error_sq_bound (h z R E1 E2 D : ℝ)
    (hh : 0 < h) (hN : 0 < z^2+R^2)
    (hD : (h/4)^2*(z^2+R^2) ≤ D^2)
    (h1 : |E1| < h/8) (h2 : |E2| < h/8) :
    (z*E1+R*E2)^2 < D^2 := by
  have hh8 : 0 < h/8 := by positivity
  have hE1 : E1^2 < (h/8)^2 := sq_lt_sq.mpr (by
    rw [abs_of_pos hh8]
    exact h1)
  have hE2 : E2^2 < (h/8)^2 := sq_lt_sq.mpr (by
    rw [abs_of_pos hh8]
    exact h2)
  have herrors : E1^2+E2^2 < (h/4)^2 := by
    nlinarith only [hE1,hE2,sq_pos_of_pos hh]
  have hc := mul_lt_mul_of_pos_left herrors hN
  have hcs : (z*E1+R*E2)^2 ≤ (z^2+R^2)*(E1^2+E2^2) := by
    nlinarith only [sq_nonneg (z*E2-R*E1)]
  have hD' : (z^2+R^2)*(h/4)^2 ≤ D^2 := by
    simpa only [mul_comm] using hD
  exact hcs.trans_lt (hc.trans_le hD')

theorem orientation_ne_zero (w : Gram6.Coord) (s t : ℝ)
    (hw : 0 < Gram6.minimum w)
    (hs : |s-(w 0*(-w 4+w 5/2)+w 1*(w 2+w 3))| < Gram6.minimum w/8)
    (ht : |t+((w 0)^2+(w 1)^2)| < Gram6.minimum w/8) :
    w 2*s+(w 5/2)*t ≠ 0 := by
  let E1 := s-(w 0*(-w 4+w 5/2)+w 1*(w 2+w 3))
  let E2 := t+((w 0)^2+(w 1)^2)
  have hb := cofactor_error_sq_bound (Gram6.minimum w) (w 2) (w 5/2)
    E1 E2 (Gram6.aMatrix w).det hw (third_row_sq_pos w hw)
    (determinant_sq_bound w hw) hs ht
  intro hz
  have he : w 2*E1+(w 5/2)*E2 = -(Gram6.aMatrix w).det := by
    rw [determinant_formula]
    dsimp [E1,E2]
    linear_combination hz
  rw [he,neg_sq] at hb
  exact (lt_irrefl _ hb)

end PBCounterexample.Quadratic8Geometry
