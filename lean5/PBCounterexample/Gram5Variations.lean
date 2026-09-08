import PBCounterexample.Gram5Data
import PBCounterexample.WeightedPolynomial

/-! Exact affine variations and weighted invariants for the five-dimensional data. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology ContDiff

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

private theorem coordinate_succ_two : (2 : Fin 4).succ = (3 : Fin 5) := rfl
private theorem coordinate_succ_succ_two : (2 : Fin 3).succ.succ = (4 : Fin 5) := rfl
attribute [local simp] coordinate_succ_two coordinate_succ_succ_two

def weights : Fin 5 → ℕ := ![5, 6, 7, 8, 9]
def weightedScale (t : ℝ) (v : Coord) : Coord := WeightedPolynomial.scale weights t v

def basePoint : Coord := ![1, 1, 1, 1, 1]
def normalDirection : Coord := ![0, 2, 3, 3, 2]
def signDirection : Coord := ![0, 0, 1, 2, 2]
def affinePoint (ε : ℝ) (v : Coord) : Coord := basePoint + ε • v

def linearA (v : Coord) : ℝ := v 0 - 4*v 1 + 6*v 2 - 4*v 3 + v 4
def linearB (v : Coord) : ℝ := 3*v 0 - 3*v 1 + 2*v 2 + 2*v 3 - 3*v 4
def linearW (v : Coord) : ℝ := 2*v 0 + v 1 - 4*v 2 + 6*v 3 - 4*v 4

def quadraticA (v : Coord) : ℝ := -4*v 1*v 3 + 3*(v 2)^2
def quadraticB (v : Coord) : ℝ := 2*v 2*v 3 - 3*v 1*v 4
def quadraticW (v : Coord) : ℝ := 3*(v 3)^2 - 4*v 2*v 4
def quadraticF (v : Coord) : ℝ := quadraticW v - quadraticB v + quadraticA v

def correctionEmbedding (u : Fin 3 → ℝ) : Coord :=
  ![0, 0, u 2, u 0 + 2*u 2, u 1 + 2*u 2]

@[simp] theorem correctionEmbedding_zero : correctionEmbedding 0 = 0 := by
  ext i
  fin_cases i <;> norm_num [correctionEmbedding]

@[simp] theorem correctionEmbedding_first (u : Fin 3 → ℝ) :
    correctionEmbedding u 0 = 0 := rfl

theorem correctionEmbedding_smul (s : ℝ) (u : Fin 3 → ℝ) :
    correctionEmbedding (s • u) = s • correctionEmbedding u := by
  ext i
  fin_cases i <;> norm_num [correctionEmbedding, Pi.smul_apply, smul_eq_mul] <;> ring

theorem linearW_eq (v : Coord) : linearW v = linearB v - linearA v := by
  simp only [linearA, linearB, linearW]
  ring

@[simp] theorem linearA_normal : linearA normalDirection = 0 := by
  norm_num [linearA, normalDirection]
@[simp] theorem linearB_normal : linearB normalDirection = 0 := by
  norm_num [linearB, normalDirection]
@[simp] theorem linearA_sign : linearA signDirection = 0 := by
  norm_num [linearA, signDirection]
@[simp] theorem linearB_sign : linearB signDirection = 0 := by
  norm_num [linearB, signDirection]

theorem linearA_correction (u : Fin 3 → ℝ) :
    linearA (correctionEmbedding u) = -4*u 0 + u 1 := by
  norm_num [linearA, correctionEmbedding]
  ring

theorem linearB_correction (u : Fin 3 → ℝ) :
    linearB (correctionEmbedding u) = 2*u 0 - 3*u 1 := by
  norm_num [linearB, correctionEmbedding]
  ring

theorem quadraticF_normal_add_sign (s : ℝ) :
    quadraticF (normalDirection + s • signDirection) = 3*s^2 := by
  norm_num [quadraticF, quadraticA, quadraticB, quadraticW,
    normalDirection, signDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eval_invariantA_affine (ε : ℝ) (v : Coord) (hv : v 0 = 0) :
    eval (affinePoint ε v) invariantA = ε*linearA v + ε^2*quadraticA v := by
  norm_num [affinePoint, invariantA, a, b, c, d, e, basePoint,
    linearA, quadraticA, Matrix.vecHead, Matrix.vecTail,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv]
  ring

theorem eval_invariantB_affine (ε : ℝ) (v : Coord) (hv : v 0 = 0) :
    eval (affinePoint ε v) invariantB = ε*linearB v + ε^2*quadraticB v := by
  norm_num [affinePoint, invariantB, a, b, c, d, e, basePoint,
    linearB, quadraticB, Matrix.vecHead, Matrix.vecTail,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv]
  ring

theorem eval_invariantW_affine (ε : ℝ) (v : Coord) (hv : v 0 = 0) :
    eval (affinePoint ε v) invariantW = ε*linearW v + ε^2*quadraticW v := by
  norm_num [affinePoint, invariantW, a, b, c, d, e, basePoint,
    linearW, quadraticW, Matrix.vecHead, Matrix.vecTail,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv]
  ring

theorem eval_leadingG_affine (ε : ℝ) (v : Coord) (hv : v 0 = 0) :
    eval (affinePoint ε v) leadingG =
      ε*(2*v 1-v 2) + ε^2*(v 1)^2 := by
  norm_num [affinePoint, leadingG, a, b, c, basePoint,
    Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv]
  ring

theorem eval_leadingDeterminant_affine (ε : ℝ) (v : Coord) (hv : v 0 = 0) :
    eval (affinePoint ε v) leadingDeterminant =
      ε*(-3*v 1+3*v 2-v 3) +
      ε^2*(3*v 1*v 2-6*(v 1)^2) - 2*ε^3*(v 1)^3 := by
  norm_num [affinePoint, leadingDeterminant, a, b, c, d, basePoint,
    Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv]
  ring

theorem a_weighted : a.IsWeightedHomogeneous weights 5 := by
  simpa [a, weights] using isWeightedHomogeneous_X ℝ weights (0 : Fin 5)
theorem b_weighted : b.IsWeightedHomogeneous weights 6 := by
  simpa [b, weights] using isWeightedHomogeneous_X ℝ weights (1 : Fin 5)
theorem c_weighted : c.IsWeightedHomogeneous weights 7 := by
  simpa [c, weights] using isWeightedHomogeneous_X ℝ weights (2 : Fin 5)
theorem d_weighted : d.IsWeightedHomogeneous weights 8 := by
  simpa [d, weights] using isWeightedHomogeneous_X ℝ weights (3 : Fin 5)
theorem e_weighted : e.IsWeightedHomogeneous weights 9 := by
  simpa [e, weights] using isWeightedHomogeneous_X ℝ weights (4 : Fin 5)

theorem invariantA_weighted : invariantA.IsWeightedHomogeneous weights 14 := by
  have hbd : (4*b*d).IsWeightedHomogeneous weights 14 := by
    simpa only [map_ofNat] using (b_weighted.C_mul 4).mul d_weighted
  have hc : (3*c^2).IsWeightedHomogeneous weights 14 := by
    simpa [map_ofNat, nsmul_eq_mul] using (c_weighted.pow 2).C_mul 3
  exact ((a_weighted.mul e_weighted).sub hbd).add hc

theorem invariantB_weighted : invariantB.IsWeightedHomogeneous weights 15 := by
  have hcd : (2*c*d).IsWeightedHomogeneous weights 15 := by
    simpa only [map_ofNat] using (c_weighted.C_mul 2).mul d_weighted
  have hbe : (3*b*e).IsWeightedHomogeneous weights 15 := by
    simpa only [map_ofNat] using (b_weighted.C_mul 3).mul e_weighted
  exact (hcd.sub hbe).add (a_weighted.pow 3)

theorem invariantW_weighted : invariantW.IsWeightedHomogeneous weights 16 := by
  have hd : (3*d^2).IsWeightedHomogeneous weights 16 := by
    simpa [map_ofNat, nsmul_eq_mul] using (d_weighted.pow 2).C_mul 3
  have hce : (4*c*e).IsWeightedHomogeneous weights 16 := by
    simpa only [map_ofNat] using (c_weighted.C_mul 4).mul e_weighted
  exact (hd.sub hce).add ((a_weighted.pow 2).mul b_weighted)

theorem leadingG_weighted : leadingG.IsWeightedHomogeneous weights 12 :=
  (b_weighted.pow 2).sub (a_weighted.mul c_weighted)

theorem leadingDeterminant_weighted :
    leadingDeterminant.IsWeightedHomogeneous weights 18 := by
  have h0 : (-a^2*d).IsWeightedHomogeneous weights 18 :=
    (a_weighted.pow 2).neg.mul d_weighted
  have h1 : (3*a*b*c).IsWeightedHomogeneous weights 18 := by
    simpa only [map_ofNat] using ((a_weighted.C_mul 3).mul b_weighted).mul c_weighted
  have h2 : (2*b^3).IsWeightedHomogeneous weights 18 := by
    simpa [map_ofNat, nsmul_eq_mul] using (b_weighted.pow 3).C_mul 2
  exact (h0.add h1).sub h2

theorem contDiff_eval (P : Poly) (k : ℕ∞ω) :
    ContDiff ℝ k (fun x : Coord => eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa using (contDiff_const : ContDiff ℝ k (fun _ : Coord => r))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP =>
    have hi : ContDiff ℝ k (fun x : Coord => x i) := by fun_prop
    simpa only [map_mul, eval_X] using hP.mul hi

def differential (P : Poly) : Coord →L[ℝ] ℝ :=
  fderiv ℝ (fun x : Coord => eval x P) basePoint

theorem hasDerivAt_eval_affine (P : Poly) (v : Coord) :
    HasDerivAt (fun t : ℝ => eval (affinePoint t v) P) (differential P v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => affinePoint t v) v 0 := by
    simpa only [affinePoint, id_eq, one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add basePoint
  have hP := (contDiff_eval P 1).differentiable_one basePoint
  simpa only [differential] using! hP.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp [affinePoint])

end

end PBCounterexample.Gram5
