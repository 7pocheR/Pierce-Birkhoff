import PBCounterexample.Gram7Coordinates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FunProp

/-!
# Polynomial chart for rank-two Gram-zero matrix pairs

The nine parameters are ordered k₀, k₁, k₂, t₀, t₁, C₀₀, C₀₁, C₁₀, C₁₁.
The ambient order contains all nine entries of the nonsymmetric square matrix,
followed by all six entries of the rectangular matrix.
-/

namespace PBCounterexample.Gram7

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open scoped Matrix BigOperators

section Ring

variable {R : Type*} [CommRing R]

def rotationDenominator (u v w : R) : R := 1 + u^2 + v^2 + w^2

def rotationNumerator (u v w : R) : Matrix Index Index R :=
  !![1+u^2-v^2-w^2, 2*(u*v-w), 2*(u*w+v);
     2*(u*v+w), 1-u^2+v^2-w^2, 2*(v*w-u);
     2*(u*w-v), 2*(v*w+u), 1-u^2-v^2+w^2]

theorem rotationNumerator_transpose_mul (u v w : R) :
    (rotationNumerator u v w)ᵀ * rotationNumerator u v w =
      (rotationDenominator u v w)^2 • (1 : Matrix Index Index R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationNumerator, rotationDenominator, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring

theorem rotationNumerator_det (u v w : R) :
    (rotationNumerator u v w).det = (rotationDenominator u v w)^3 := by
  simp [rotationNumerator, rotationDenominator, Matrix.det_fin_three]
  ring

def chartCV (t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) : Matrix Row Index R :=
  !![c₀₀, c₀₁, c₀₀*t₀+c₀₁*t₁; c₁₀, c₁₁, c₁₀*t₀+c₁₁*t₁]

def chartEmbedding (t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) : Matrix Index Index R :=
  !![c₀₀, c₀₁, c₀₀*t₀+c₀₁*t₁;
     c₁₀, c₁₁, c₁₀*t₀+c₁₁*t₁; 0, 0, 0]

def phiA (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) : Matrix Index Index R :=
  rotationNumerator u v w * chartEmbedding t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁

def phiB (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) : Matrix Row Index R :=
  rotationDenominator u v w • chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁

theorem phiA_apply (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) (i j : Index) :
    phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ i j =
      rotationNumerator u v w i 0 * chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ 0 j +
      rotationNumerator u v w i 1 * chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ 1 j := by
  fin_cases j <;>
    simp [phiA, chartEmbedding, chartCV, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phiB_apply (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) (i : Row) (j : Index) :
    phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ i j =
      rotationDenominator u v w * chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ i j := rfl

theorem chartEmbedding_gram (t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) :
    (chartEmbedding t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ *
      chartEmbedding t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ =
    (chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ * chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartEmbedding, chartCV, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phi_gram_zero (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) :
    (phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ *
      phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ -
    (phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ *
      phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ = 0 := by
  have hA :
      (phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ *
        phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ =
      (rotationDenominator u v w)^2 •
        ((chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)ᵀ * chartCV t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁) := by
    simp only [phiA, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rotationNumerator u v w)ᵀ,
      rotationNumerator_transpose_mul]
    simp [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, chartEmbedding_gram]
  rw [hA]
  simp [phiB, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, pow_two]

def phi (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) : Fin 15 → R :=
  let A := phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁
  let B := phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁
  ![A 0 0, A 0 1, A 0 2, A 1 0, A 1 1, A 1 2, A 2 0, A 2 1, A 2 2,
    B 0 0, B 0 1, B 0 2, B 1 0, B 1 1, B 1 2]

@[simp] theorem phi_base : phi (0:R) 0 0 0 0 1 0 0 (-1) =
    ![1,0,0,0,-1,0,0,0,0,1,0,0,0,-1,0] := by
  ext i
  fin_cases i <;> norm_num [phi, phiA_apply, phiB_apply,
    rotationNumerator, rotationDenominator, chartCV, Matrix.cons_val, Fin.succ,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> rfl

theorem phi_map {S : Type*} [CommRing S] (f : R →+* S)
    (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : R) :
    (fun i => f (phi u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ i)) =
      phi (f u) (f v) (f w) (f t₀) (f t₁) (f c₀₀) (f c₀₁) (f c₁₀) (f c₁₁) := by
  ext i
  fin_cases i <;>
    simp [phi, phiA_apply, phiB_apply, rotationNumerator, rotationDenominator,
      chartCV, Matrix.cons_val, Fin.succ, map_ofNat]

end Ring

noncomputable def chartPolynomials : Fin 15 → MvPolynomial (Fin 9) ℤ :=
  phi (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
    (MvPolynomial.X 3) (MvPolynomial.X 4) (MvPolynomial.X 5)
    (MvPolynomial.X 6) (MvPolynomial.X 7) (MvPolynomial.X 8)

theorem chartPolynomials_eval {R : Type*} [CommRing R] (p : Fin 9 → R) :
    (fun i => MvPolynomial.eval₂ (Int.castRingHom R) p (chartPolynomials i)) =
      phi (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) := by
  simpa only [chartPolynomials, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] using
    phi_map (MvPolynomial.eval₂Hom (Int.castRingHom R) p)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
      (MvPolynomial.X 3) (MvPolynomial.X 4) (MvPolynomial.X 5)
      (MvPolynomial.X 6) (MvPolynomial.X 7) (MvPolynomial.X 8)

@[simp] theorem ambientA_phi (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ) :
    ambientA (phi u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁) =
      phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem ambientB_phi (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ) :
    ambientB (phi u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁) =
      phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

noncomputable def ambientGram (a : Ambient) : Matrix Index Index ℝ :=
  (ambientA a)ᵀ * ambientA a - (ambientB a)ᵀ * ambientB a

theorem ambient_phi_gram_zero (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ) :
    ambientGram (phi u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁) = 0 := by
  simpa [ambientGram] using phi_gram_zero u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁

theorem rotationDenominator_pos (u v w : ℝ) : 0 < rotationDenominator u v w := by
  unfold rotationDenominator
  positivity

theorem phiB_leading_minor (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ) :
    ((phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁).submatrix id Fin.castSucc).det =
      (rotationDenominator u v w)^2 * (c₀₀*c₁₁-c₀₁*c₁₀) := by
  simp [Matrix.det_fin_two, phiB_apply, chartCV, Matrix.submatrix]
  ring

theorem phiB_rank_two (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ)
    (hC : c₀₀*c₁₁-c₀₁*c₁₀ ≠ 0) :
    (phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁).rank = 2 := by
  have hm : ((phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁).submatrix id Fin.castSucc).det ≠ 0 := by
    rw [phiB_leading_minor]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt (rotationDenominator_pos u v w))) hC
  have hr := Matrix.rank_of_det_ne_zero hm
  have hl := Matrix.rank_submatrix_le (phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁) id Fin.castSucc
  have hu := Matrix.rank_le_card_height (phiB u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)
  simp only [Fintype.card_fin] at hr hu
  omega

theorem phiA_rank_two (u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁ : ℝ)
    (hC : c₀₀*c₁₁-c₀₁*c₁₀ ≠ 0) :
    (phiA u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁).rank = 2 := by
  have h := sub_eq_zero.mp (phi_gram_zero u v w t₀ t₁ c₀₀ c₀₁ c₁₀ c₁₁)
  have hr := congrArg Matrix.rank h
  rw [Matrix.rank_transpose_mul_self, Matrix.rank_transpose_mul_self,
    phiB_rank_two _ _ _ _ _ _ _ _ _ hC] at hr
  exact hr

noncomputable def activeConstraints (a : Ambient) : Coord := fun i => constraints a i.succ

noncomputable def ambientTrace (a : Ambient) : ℝ :=
  ambientGram a 0 0 + ambientGram a 1 1 - ambientGram a 2 2

noncomputable def omittedDefect (a : Ambient) : ℝ :=
  a 0 - ambient (coordinates a) 0

noncomputable def omittedFactor (a : Ambient) : ℝ :=
  a 0 + ambient (coordinates a) 0

theorem ambientTrace_formula (a : Ambient) :
    ambientTrace a =
      (a 0)^2+(a 3)^2+(a 6)^2+(a 1)^2+(a 4)^2+(a 7)^2+(a 11)^2+(a 14)^2 -
      ((a 2)^2+(a 5)^2+(a 8)^2+(a 9)^2+(a 12)^2+(a 10)^2+(a 13)^2) := by
  simp [ambientTrace, ambientGram, ambientA, ambientB, aIndex, bIndex,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem ambient_entries (z : Coord) : ambient z =
    ![(-1/3) * z 0 + (-1/3) * z 1 + (-1/3) * z 2 + (2/3) * z 3 + (1/3) * z 4 + (-1/3) * z 6,
      (19/45) * z 0 + (-1/9) * z 1 + (-13/90) * z 2 + (-4/9) * z 3 + (11/18) * z 4 + (1/10) * z 5 + (-4/9) * z 6,
      z 0,
      (163/315) * z 0 + (-7/9) * z 1 + (59/630) * z 2 + (8/63) * z 3 + (-37/126) * z 4 + (1/210) * z 5 + (8/63) * z 6,
      (-1/3) * z 0 + (-1/3) * z 1 + (-1/3) * z 2 + (-1/3) * z 3 + (1/3) * z 4 + (2/3) * z 6,
      z 1,
      (-46/105) * z 0 + (-1/3) * z 1 + (11/105) * z 2 + (-3/7) * z 3 + (-5/21) * z 4 + (-38/105) * z 5 + (-3/7) * z 6,
      (-23/63) * z 0 + (-2/9) * z 1 + (37/63) * z 2 + (-5/63) * z 3 + (5/63) * z 4 + (10/21) * z 5 + (-5/63) * z 6,
      z 2,
      z 3,
      z 5,
      (2/35) * z 0 + (31/70) * z 2 + (1/7) * z 3 + (5/14) * z 4 + (17/70) * z 5 + (1/7) * z 6,
      z 4,
      z 6,
      (-2/35) * z 0 + (-31/70) * z 2 + (-1/7) * z 3 + (-5/14) * z 4 + (53/70) * z 5 + (-1/7) * z 6] := by
  ext i
  fin_cases i <;>
    norm_num [ambient, basis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val, Fin.succ] <;> linarith!

theorem ambientTrace_ambient (z : Coord) : ambientTrace (ambient z) = 0 := by
  rw [ambientTrace_formula, ambient_entries]
  change ((-1/3) * z 0 + (-1/3) * z 1 + (-1/3) * z 2 + (2/3) * z 3 + (1/3) * z 4 + (-1/3) * z 6)^2 +
    ((163/315) * z 0 + (-7/9) * z 1 + (59/630) * z 2 + (8/63) * z 3 + (-37/126) * z 4 + (1/210) * z 5 + (8/63) * z 6)^2 +
    ((-46/105) * z 0 + (-1/3) * z 1 + (11/105) * z 2 + (-3/7) * z 3 + (-5/21) * z 4 + (-38/105) * z 5 + (-3/7) * z 6)^2 +
    ((19/45) * z 0 + (-1/9) * z 1 + (-13/90) * z 2 + (-4/9) * z 3 + (11/18) * z 4 + (1/10) * z 5 + (-4/9) * z 6)^2 +
    ((-1/3) * z 0 + (-1/3) * z 1 + (-1/3) * z 2 + (-1/3) * z 3 + (1/3) * z 4 + (2/3) * z 6)^2 +
    ((-23/63) * z 0 + (-2/9) * z 1 + (37/63) * z 2 + (-5/63) * z 3 + (5/63) * z 4 + (10/21) * z 5 + (-5/63) * z 6)^2 +
    ((2/35) * z 0 + (31/70) * z 2 + (1/7) * z 3 + (5/14) * z 4 + (17/70) * z 5 + (1/7) * z 6)^2 +
    ((-2/35) * z 0 + (-31/70) * z 2 + (-1/7) * z 3 + (-5/14) * z 4 + (53/70) * z 5 + (-1/7) * z 6)^2 -
    ((z 0)^2 + (z 1)^2 + (z 2)^2 + (z 3)^2 + (z 4)^2 + (z 5)^2 + (z 6)^2) = 0
  ring

theorem constraints_zero_row (a : Ambient) :
    constraints a 0 = 3 * omittedDefect a := by
  norm_num [constraints, constraintsMatrix, omittedDefect, ambient, coordinates,
    negativeIndex, basis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val, Fin.succ]
  ring!

theorem activeConstraints_update_zero (a : Ambient) (x : ℝ) :
    activeConstraints (Function.update a 0 x) = activeConstraints a := by
  ext i
  fin_cases i <;>
    norm_num [activeConstraints, constraints, constraintsMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Function.update, Matrix.cons_val, Fin.succ]

theorem coordinates_update_zero (a : Ambient) (x : ℝ) :
    coordinates (Function.update a 0 x) = coordinates a := by
  funext i
  change Function.update a 0 x (negativeIndex i) = a (negativeIndex i)
  have h : negativeIndex i ≠ 0 := by fin_cases i <;> decide
  exact Function.update_of_ne h x a

theorem constraints_eq_zero_of_active_defect (a : Ambient)
    (ha : activeConstraints a = 0) (hdef : omittedDefect a = 0) :
    constraints a = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [constraints_zero_row, hdef]
  · exact congrFun ha j

theorem update_zero_eq_ambient (a : Ambient) (ha : activeConstraints a = 0) :
    Function.update a 0 (ambient (coordinates a) 0) = ambient (coordinates a) := by
  let b := Function.update a 0 (ambient (coordinates a) 0)
  have hbc : coordinates b = coordinates a := coordinates_update_zero _ _
  have hb : constraints b = 0 := by
    apply constraints_eq_zero_of_active_defect
    · simpa [b, activeConstraints_update_zero] using ha
    · simp [omittedDefect, hbc, b]
  simpa [hbc] using (ambient_coordinates_of_constraints b hb).symm

theorem ambientTrace_update_zero (a : Ambient) (x : ℝ) :
    ambientTrace (Function.update a 0 x) = ambientTrace a + x^2 - (a 0)^2 := by
  simp [ambientTrace_formula, Function.update]
  ring

theorem omitted_factorization (a : Ambient) (ha : activeConstraints a = 0) :
    ambientTrace a = omittedDefect a * omittedFactor a := by
  have h := ambientTrace_update_zero a (ambient (coordinates a) 0)
  rw [update_zero_eq_ambient a ha, ambientTrace_ambient] at h
  unfold omittedDefect omittedFactor
  nlinarith

theorem constraints_eq_zero_of_active_trace (a : Ambient)
    (ha : activeConstraints a = 0) (htrace : ambientTrace a = 0)
    (hfactor : omittedFactor a ≠ 0) : constraints a = 0 := by
  apply constraints_eq_zero_of_active_defect a ha
  exact (mul_eq_zero.mp ((omitted_factorization a ha).symm.trans htrace)).resolve_right hfactor

end PBCounterexample.Gram7
