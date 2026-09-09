import PBCounterexample.Gram6Coordinates

/-! The polynomial base curve and its explicit linear coordinate change. -/

namespace PBCounterexample.Gram6

open Matrix

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

noncomputable def curve (t : ℝ) : Coord := ![
  t^4 - 6*t^2 + 1,
  4*t^3 - 4*t,
  t^4 + 2*t^2 + 1,
  2*t^4 - 2,
  4*t^3 + 4*t,
  2*t^5 + 4*t^3 + 2*t]

noncomputable def curveTangent (t : ℝ) : Coord := ![
  4*t^3 - 12*t,
  12*t^2 - 4,
  4*t^3 + 4*t,
  8*t^3,
  12*t^2 + 4,
  10*t^4 + 12*t^2 + 2]

theorem hasDerivAt_curve (t : ℝ) : HasDerivAt curve (curveTangent t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun s : ℝ => s^4 - 6*s^2 + 1) (4*t^3 - 12*t) t
    convert! ((((hasDerivAt_id t).pow 4).sub
      (((hasDerivAt_id t).pow 2).const_mul 6)).add_const 1) using 1
    norm_num
    ring
  · change HasDerivAt (fun s : ℝ => 4*s^3 - 4*s) (12*t^2 - 4) t
    convert! (((hasDerivAt_id t).pow 3).const_mul 4).sub
      ((hasDerivAt_id t).const_mul 4) using 1
    norm_num
    ring
  · change HasDerivAt (fun s : ℝ => s^4 + 2*s^2 + 1) (4*t^3 + 4*t) t
    convert! ((((hasDerivAt_id t).pow 4).add
      (((hasDerivAt_id t).pow 2).const_mul 2)).add_const 1) using 1
    norm_num
    ring
  · change HasDerivAt (fun s : ℝ => 2*s^4 - 2) (8*t^3) t
    convert! (((hasDerivAt_id t).pow 4).const_mul 2).sub_const 2 using 1
    norm_num
    ring
  · change HasDerivAt (fun s : ℝ => 4*s^3 + 4*s) (12*t^2 + 4) t
    convert! (((hasDerivAt_id t).pow 3).const_mul 4).add
      ((hasDerivAt_id t).const_mul 4) using 1
    norm_num
    ring
  · change HasDerivAt (fun s : ℝ => 2*s^5 + 4*s^3 + 2*s) (10*t^4 + 12*t^2 + 2) t
    convert! ((((hasDerivAt_id t).pow 5).const_mul 2).add
      (((hasDerivAt_id t).pow 3).const_mul 4)).add
      ((hasDerivAt_id t).const_mul 2) using 1
    norm_num
    ring

noncomputable def kernelVector (t : ℝ) : Index → ℝ := ![-t, 1, 1]

noncomputable def rankOneTarget : Matrix Index Index ℝ := !![
  0, 0, 0;
  0, 1, -1;
  0, -1, 1]

noncomputable def fromMonomial (v : Coord) : Coord := ![
  v 0 - 6*v 2 + v 4,
  -4*v 1 + 4*v 3,
  v 0 + 2*v 2 + v 4,
  -2*v 0 + 2*v 4,
  4*v 1 + 4*v 3,
  2*v 1 + 4*v 3 + 2*v 5]

noncomputable def monomialCoordinates (w : Coord) : Coord := ![
  (w 0 + 3*w 2 - 2*w 3)/8,
  (w 4 - w 1)/8,
  (w 2 - w 0)/8,
  (w 4 + w 1)/8,
  (w 0 + 3*w 2 + 2*w 3)/8,
  (4*w 5 - 3*w 4 - w 1)/8]

theorem fromMonomial_monomialCoordinates (w : Coord) :
    fromMonomial (monomialCoordinates w) = w := by
  ext i
  fin_cases i <;>
    norm_num [fromMonomial, monomialCoordinates, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring_nf <;> rfl

theorem monomialCoordinates_fromMonomial (v : Coord) :
    monomialCoordinates (fromMonomial v) = v := by
  ext i
  fin_cases i <;>
    norm_num [fromMonomial, monomialCoordinates, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring_nf <;> rfl

theorem fromMonomial_curve (t : ℝ) :
    fromMonomial ![1, t, t^2, t^3, t^4, t^5] = curve t := by
  ext i
  fin_cases i <;>
    norm_num [fromMonomial, curve, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring

theorem monomialCoordinates_curve (t : ℝ) :
    monomialCoordinates (curve t) = ![1, t, t^2, t^3, t^4, t^5] := by
  rw [← fromMonomial_curve, monomialCoordinates_fromMonomial]

theorem gramMatrix_curve (t : ℝ) : gramMatrix (curve t) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramMatrix, aMatrix, bMatrix, curve, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring

theorem aMatrix_curve_kernel (t : ℝ) : aMatrix (curve t) *ᵥ kernelVector t = 0 := by
  ext i
  fin_cases i <;>
    norm_num [aMatrix, curve, kernelVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring

theorem bMatrix_curve_kernel (t : ℝ) : bMatrix (curve t) *ᵥ kernelVector t = 0 := by
  ext i
  fin_cases i <;>
    norm_num [bMatrix, curve, kernelVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring

theorem gramMatrix_curveTangent (t : ℝ) :
    gramMatrix (curveTangent t) = (12*(1+t^2)^2) • rankOneTarget := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramMatrix, aMatrix, bMatrix, curveTangent, rankOneTarget,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, sixth_entry] <;> ring

end PBCounterexample.Gram6
