import PBCounterexample.Gram5Variations

/-! Algebraic rules for the actual real derivative of polynomial evaluation. -/

namespace PBCounterexample.Gram5

open MvPolynomial
open scoped BigOperators

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

@[simp] theorem differential_C (r : ℝ) (v : Coord) :
    differential (C r) v = 0 := by
  apply (hasDerivAt_eval_affine (C r) v).unique
  simpa only [eval_C] using hasDerivAt_const (0 : ℝ) r

@[simp] theorem differential_zero (v : Coord) : differential 0 v = 0 := by
  simpa only [map_zero] using differential_C 0 v

@[simp] theorem differential_one (v : Coord) : differential 1 v = 0 := by
  simpa only [map_one] using differential_C 1 v

@[simp] theorem differential_X (i : Fin 5) (v : Coord) :
    differential (X i) v = v i := by
  apply (hasDerivAt_eval_affine (X i) v).unique
  simpa only [eval_X, affinePoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq,
    one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (basePoint i)

@[simp] theorem differential_add (P Q : Poly) (v : Coord) :
    differential (P+Q) v = differential P v + differential Q v := by
  apply (hasDerivAt_eval_affine (P+Q) v).unique
  simpa only [map_add, Pi.add_apply] using! (hasDerivAt_eval_affine P v).add
    (hasDerivAt_eval_affine Q v)

@[simp] theorem differential_sub (P Q : Poly) (v : Coord) :
    differential (P-Q) v = differential P v - differential Q v := by
  apply (hasDerivAt_eval_affine (P-Q) v).unique
  simpa only [map_sub, Pi.sub_apply] using! (hasDerivAt_eval_affine P v).sub
    (hasDerivAt_eval_affine Q v)

@[simp] theorem differential_neg (P : Poly) (v : Coord) :
    differential (-P) v = -differential P v := by
  apply (hasDerivAt_eval_affine (-P) v).unique
  simpa only [map_neg, Pi.neg_apply] using! (hasDerivAt_eval_affine P v).neg

@[simp] theorem differential_mul (P Q : Poly) (v : Coord) :
    differential (P*Q) v =
      differential P v * eval basePoint Q + eval basePoint P * differential Q v := by
  apply (hasDerivAt_eval_affine (P*Q) v).unique
  simpa only [map_mul, Pi.mul_apply, affinePoint, zero_smul, add_zero] using!
    (hasDerivAt_eval_affine P v).mul (hasDerivAt_eval_affine Q v)

@[simp] theorem differential_pow (P : Poly) (k : ℕ) (v : Coord) :
    differential (P^k) v = (k : ℝ) * (eval basePoint P)^(k-1) * differential P v := by
  apply (hasDerivAt_eval_affine (P^k) v).unique
  simpa only [map_pow, Pi.pow_apply, affinePoint, zero_smul, add_zero] using!
    (hasDerivAt_eval_affine P v).pow k

@[simp] theorem differential_C_mul (r : ℝ) (P : Poly) (v : Coord) :
    differential (C r*P) v = r*differential P v := by
  simp only [differential_mul, differential_C, eval_C, zero_mul, zero_add]

@[simp] theorem differential_sum {ι : Type*} (S : Finset ι) (P : ι → Poly) (v : Coord) :
    differential (∑ i ∈ S, P i) v = ∑ i ∈ S, differential (P i) v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi, differential_add, ih]

theorem differential_leadingG (v : Coord) :
    differential leadingG v = 2*v 1-v 0-v 2 := by
  norm_num [leadingG, a, b, c, basePoint]
  ring

theorem differential_leadingDeterminant (v : Coord) :
    differential leadingDeterminant v = v 0-3*v 1+3*v 2-v 3 := by
  have h3 : differential (3 : Poly) v = 0 := by
    simpa only [map_ofNat] using differential_C 3 v
  have h2 : differential (2 : Poly) v = 0 := by
    simpa only [map_ofNat] using differential_C 2 v
  norm_num [leadingDeterminant, a, b, c, d, basePoint, h3, h2]
  ring

@[simp] theorem eval_base_leadingG : eval basePoint leadingG = 0 := by
  norm_num [leadingG, a, b, c, basePoint]

@[simp] theorem eval_base_leadingDeterminant : eval basePoint leadingDeterminant = 0 := by
  norm_num [leadingDeterminant, a, b, c, d, basePoint]

theorem differential_leadingG_normal_sign (s : ℝ) :
    differential leadingG (normalDirection + s • signDirection) = 1-s := by
  rw [differential_leadingG]
  norm_num [normalDirection, signDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem differential_leadingDeterminant_normal_sign (s : ℝ) :
    differential leadingDeterminant (normalDirection + s • signDirection) = s := by
  rw [differential_leadingDeterminant]
  norm_num [normalDirection, signDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end PBCounterexample.Gram5
