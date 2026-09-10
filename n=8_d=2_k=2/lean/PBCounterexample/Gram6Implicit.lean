import PBCounterexample.Gram6CorrectionCoordinates
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual real implicit paths for the six-dimensional Gram construction. -/

namespace PBCounterexample.Gram6

open Matrix Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev ImplicitCoord := Fin 4 → ℝ

private theorem sixth_entry {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

/-- The four correction coordinates in the original six-dimensional space. -/
noncomputable def correctionDisplacement (t : ℝ) (u : ImplicitCoord) : Coord :=
  coordinateCorrection ![u 0, u 1, u 2] + u 3 • kernelDirection t

noncomputable def signedNormal (t ρ δ σ : ℝ) : Coord :=
  normalDirection t ρ + (σ*δ) • kernelDirection t

/-- The last component is not multiplied by the parameter `p.1`. -/
noncomputable def implicitResidual (t ρ δ σ : ℝ) (p : ℝ × ImplicitCoord) :
    ImplicitCoord :=
  let z := correctionDisplacement t p.2
  let R := gramMatrix (signedNormal t ρ δ σ + z) - δ^2 • interiorTarget
  let v := gramCoordinates (gramPolar (ρ • curve t) z + p.1 • R)
  ![v 0, v 1, v 2, gramFunctional t R]

private theorem coordinateCorrection_zero : coordinateCorrection 0 = 0 := by
  ext i
  fin_cases i <;> norm_num [coordinateCorrection, sixth_entry]

@[simp] theorem correctionDisplacement_zero (t : ℝ) :
    correctionDisplacement t 0 = 0 := by
  have h : (![0, 0, 0] : Index → ℝ) = 0 := by ext i; fin_cases i <;> rfl
  simp only [correctionDisplacement, Pi.zero_apply, zero_smul, add_zero, h,
    coordinateCorrection_zero]

theorem correctionDisplacement_smul (t a : ℝ) (u : ImplicitCoord) :
    correctionDisplacement t (a • u) = a • correctionDisplacement t u := by
  have hcoordinates :
      coordinateCorrection ![(a • u) 0, (a • u) 1, (a • u) 2] =
        a • coordinateCorrection ![u 0, u 1, u 2] := by
    ext i
    fin_cases i <;>
      norm_num [coordinateCorrection, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, sixth_entry]
  simp only [Pi.smul_apply, smul_eq_mul] at hcoordinates
  simp only [correctionDisplacement, hcoordinates, Pi.smul_apply,
    smul_eq_mul, smul_add, smul_smul]

private theorem gramPolar_zero_right (v : Coord) : gramPolar v 0 = 0 := by
  simpa only [zero_smul] using gramPolar_smul_right (0 : ℝ) v (0 : Coord)

private theorem gramPolar_add_left (v w z : Coord) :
    gramPolar (v + w) z = gramPolar v z + gramPolar w z := by
  rw [gramPolar_comm, gramPolar_add_right, gramPolar_comm z v, gramPolar_comm z w]

theorem gramCoordinates_base_correctionDisplacement (t ρ : ℝ) (u : ImplicitCoord) :
    gramCoordinates (gramPolar (ρ • curve t) (correctionDisplacement t u)) =
      correctionMatrix t ρ *ᵥ ![u 0, u 1, u 2] := by
  rw [correctionDisplacement, gramPolar_add_right, gramPolar_smul_right,
    gramPolar_base_kernelDirection, smul_zero, add_zero, correctionMatrix_mulVec]

theorem gramFunctional_signedNormal_kernelDirection (t ρ δ σ : ℝ) :
    gramFunctional t (gramPolar (signedNormal t ρ δ σ) (kernelDirection t)) =
      2*σ*δ*interiorScale t := by
  rw [signedNormal, gramPolar_add_left, gramPolar_smul_left, gramFunctional_add,
    gramFunctional_smul, gramFunctional_normal_kernelDirection, gramPolar_self,
    gramFunctional_smul, gramFunctional_gramMatrix_kernelDirection]
  ring

theorem implicitResidual_zero (t ρ δ σ : ℝ) (hσ : σ^2 = 1) :
    implicitResidual t ρ δ σ (0, 0) = 0 := by
  have hlast : gramFunctional t
      (gramMatrix (signedNormal t ρ δ σ) - δ^2 • interiorTarget) = 0 := by
    rw [signedNormal, gramFunctional_sub, gramFunctional_normal_add_kernel,
      gramFunctional_smul, gramFunctional_interiorTarget, mul_pow, hσ]
    ring
  ext i
  fin_cases i <;>
    norm_num [implicitResidual, correctionDisplacement_zero, gramPolar_zero_right,
      zero_smul, zero_add, add_zero, gramCoordinates, hlast, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Matrix.zero_apply,
      Pi.zero_apply]

theorem contDiff_correctionDisplacement (t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (correctionDisplacement t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    norm_num [correctionDisplacement, coordinateCorrection, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      sixth_entry] <;> fun_prop

private theorem contDiff_gramMatrix (n : ℕ∞ω) : ContDiff ℝ n gramMatrix := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramMatrix, aMatrix, bMatrix, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply] <;> fun_prop

private theorem contDiff_gramPolar_right (v : Coord) (n : ℕ∞ω) :
    ContDiff ℝ n (gramPolar v) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramPolar, aMatrix, bMatrix, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply] <;> fun_prop

private theorem contDiff_gramCoordinates (n : ℕ∞ω) : ContDiff ℝ n gramCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> norm_num [gramCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop

private theorem contDiff_gramFunctional (t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (gramFunctional t) := by
  unfold gramFunctional
  fun_prop

theorem contDiff_implicitResidual (t ρ δ σ : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (implicitResidual t ρ δ σ) := by
  have hz : ContDiff ℝ n (fun p : ℝ × ImplicitCoord => correctionDisplacement t p.2) :=
    (contDiff_correctionDisplacement t n).comp contDiff_snd
  have hR : ContDiff ℝ n (fun p : ℝ × ImplicitCoord =>
      gramMatrix (signedNormal t ρ δ σ + correctionDisplacement t p.2) -
        δ^2 • interiorTarget) :=
    ((contDiff_gramMatrix n).comp (contDiff_const.add hz)).sub contDiff_const
  have htop : ContDiff ℝ n (fun p : ℝ × ImplicitCoord =>
      gramCoordinates (gramPolar (ρ • curve t) (correctionDisplacement t p.2) +
        p.1 • (gramMatrix (signedNormal t ρ δ σ + correctionDisplacement t p.2) -
          δ^2 • interiorTarget))) :=
    (contDiff_gramCoordinates n).comp
      (((contDiff_gramPolar_right (ρ • curve t) n).comp hz).add (contDiff_fst.smul hR))
  have hlast := (contDiff_gramFunctional t n).comp hR
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_pi.mp htop 0
  · exact contDiff_pi.mp htop 1
  · exact contDiff_pi.mp htop 2
  · exact hlast

/-- The value of the derivative in a vertical direction. -/
noncomputable def implicitVerticalValue (t ρ δ σ : ℝ) (u : ImplicitCoord) :
    ImplicitCoord :=
  let z := correctionDisplacement t u
  let v := gramCoordinates (gramPolar (ρ • curve t) z)
  ![v 0, v 1, v 2, gramFunctional t (gramPolar (signedNormal t ρ δ σ) z)]

private noncomputable def implicitQuadraticValue (t : ℝ) (u : ImplicitCoord) :
    ImplicitCoord :=
  ![0, 0, 0, gramFunctional t (gramMatrix (correctionDisplacement t u))]

private theorem implicitResidual_vertical_line (t ρ δ σ a : ℝ) (u : ImplicitCoord) :
    implicitResidual t ρ δ σ (0, a • u) =
      implicitResidual t ρ δ σ (0, 0) + a • implicitVerticalValue t ρ δ σ u +
        a^2 • implicitQuadraticValue t u := by
  ext i
  fin_cases i <;>
    norm_num [implicitResidual, implicitVerticalValue, implicitQuadraticValue,
      correctionDisplacement_smul, correctionDisplacement_zero, gramPolar_zero_right,
      gramPolar_smul_right, gramMatrix_add_smul, gramFunctional_add,
      gramFunctional_sub, gramFunctional_smul, zero_smul, zero_add, add_zero,
      gramCoordinates, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.zero_apply] <;> ring

theorem hasDerivAt_implicitResidual_vertical_line (t ρ δ σ : ℝ) (u : ImplicitCoord) :
    HasDerivAt (fun a : ℝ => implicitResidual t ρ δ σ (0, a • u))
      (implicitVerticalValue t ρ δ σ u) 0 := by
  have heq : (fun a : ℝ => implicitResidual t ρ δ σ (0, a • u)) =
      (fun a : ℝ => implicitResidual t ρ δ σ (0, 0) +
        a • implicitVerticalValue t ρ δ σ u + a^2 • implicitQuadraticValue t u) := by
    funext a
    exact implicitResidual_vertical_line t ρ δ σ a u
  rw [heq]
  convert! (((hasDerivAt_const (0 : ℝ) (implicitResidual t ρ δ σ (0, 0))).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (implicitVerticalValue t ρ δ σ u))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (implicitQuadraticValue t u))) using 1 <;>
      simp

noncomputable def implicitVerticalDerivative (t ρ δ σ : ℝ) :
    ImplicitCoord →L[ℝ] ImplicitCoord :=
  fderiv ℝ (implicitResidual t ρ δ σ) (0, 0) ∘L
    ContinuousLinearMap.inr ℝ ℝ ImplicitCoord

theorem implicitVerticalDerivative_apply (t ρ δ σ : ℝ) (u : ImplicitCoord) :
    implicitVerticalDerivative t ρ δ σ u = implicitVerticalValue t ρ δ σ u := by
  have hline : HasDerivAt (fun a : ℝ => ((0 : ℝ), a • u)) (0, u) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1 <;> simp
  have hf := (contDiff_implicitResidual t ρ δ σ 1).differentiable_one (0, 0)
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  change (fderiv ℝ (implicitResidual t ρ δ σ) (0, 0)) (0, u) = _
  exact hcomp.unique (hasDerivAt_implicitResidual_vertical_line t ρ δ σ u)

theorem implicitVerticalDerivative_first_three (t ρ δ σ : ℝ) (u : ImplicitCoord) :
    ![implicitVerticalDerivative t ρ δ σ u 0,
      implicitVerticalDerivative t ρ δ σ u 1,
      implicitVerticalDerivative t ρ δ σ u 2] =
      correctionMatrix t ρ *ᵥ ![u 0, u 1, u 2] := by
  simpa only [implicitVerticalDerivative_apply, implicitVerticalValue, gramCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using
      gramCoordinates_base_correctionDisplacement t ρ u

theorem implicitVerticalDerivative_last (t ρ δ σ : ℝ) (u : ImplicitCoord) :
    implicitVerticalDerivative t ρ δ σ u 3 =
      gramFunctional t (gramPolar (signedNormal t ρ δ σ) (correctionDisplacement t u)) := by
  rw [implicitVerticalDerivative_apply]
  rfl

theorem implicitVerticalDerivative_last_of_first_three_zero (t ρ δ σ : ℝ)
    (u : ImplicitCoord) (hu : (![u 0, u 1, u 2] : Index → ℝ) = 0) :
    implicitVerticalDerivative t ρ δ σ u 3 = u 3 * (2*σ*δ*interiorScale t) := by
  have hz : correctionDisplacement t u = u 3 • kernelDirection t := by
    rw [correctionDisplacement, hu, coordinateCorrection_zero, zero_add]
  rw [implicitVerticalDerivative_last, hz, gramPolar_smul_right,
    gramFunctional_smul, gramFunctional_signedNormal_kernelDirection]

theorem implicitVerticalDerivative_injective (t ρ δ σ : ℝ)
    (hρ : ρ ≠ 0) (hδ : δ ≠ 0) (hσ : σ ≠ 0) :
    Function.Injective (implicitVerticalDerivative t ρ δ σ) := by
  apply (injective_iff_map_eq_zero (implicitVerticalDerivative t ρ δ σ)).mpr
  intro u hu
  have htop : correctionMatrix t ρ *ᵥ ![u 0, u 1, u 2] = 0 := by
    rw [← implicitVerticalDerivative_first_three t ρ δ σ u, hu]
    ext i
    fin_cases i <;> rfl
  have hM : Function.Injective (correctionMatrix t ρ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (correctionMatrix t ρ)).mpr
        (isUnit_iff_ne_zero.mpr (correctionMatrix_det_ne_zero t ρ hρ)))
  have hfirst : (![u 0, u 1, u 2] : Index → ℝ) = 0 := by
    apply hM
    simpa only [Matrix.mulVec_zero] using htop
  have hlast : u 3 * (2*σ*δ*interiorScale t) = 0 := by
    rw [← implicitVerticalDerivative_last_of_first_three_zero t ρ δ σ u hfirst, hu]
    rfl
  have hfactor : 2*σ*δ*interiorScale t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hσ) hδ)
      (ne_of_gt (interiorScale_pos t))
  have hu3 : u 3 = 0 := (mul_eq_zero.mp hlast).resolve_right hfactor
  ext i
  fin_cases i
  · have h0 := congrFun hfirst (0 : Index)
    norm_num [Matrix.cons_val] at h0 ⊢
    exact h0
  · have h1 := congrFun hfirst (1 : Index)
    norm_num [Matrix.cons_val] at h1 ⊢
    exact h1
  · have h2 := congrFun hfirst (2 : Index)
    norm_num [Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h2 ⊢
    exact h2
  · norm_num only [Fin.reduceFinMk]
    exact hu3

theorem implicitVerticalDerivative_isInvertible (t ρ δ σ : ℝ)
    (hρ : ρ ≠ 0) (hδ : δ ≠ 0) (hσ : σ ≠ 0) :
    (implicitVerticalDerivative t ρ δ σ).IsInvertible := by
  let L := implicitVerticalDerivative t ρ δ σ
  have hinj : Function.Injective L := implicitVerticalDerivative_injective t ρ δ σ hρ hδ hσ
  have hsurj : Function.Surjective L :=
    LinearMap.surjective_of_injective (f := L.toLinearMap) hinj
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  ext u i
  rfl

/-- Smooth, actual real solutions of the complete four-equation system. -/
theorem exists_implicitCorrection (t ρ δ σ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hσ : σ^2 = 1) :
    ∃ u : ℝ → ImplicitCoord,
      u 0 = 0 ∧ ContDiffAt ℝ ∞ u 0 ∧ Tendsto u (𝓝 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), implicitResidual t ρ δ σ (ε, u ε) = 0 := by
  have hσ0 : σ ≠ 0 := by intro h; simp [h] at hσ
  have hF : ContDiffAt ℝ ∞ (implicitResidual t ρ δ σ) (0, 0) :=
    (contDiff_implicitResidual t ρ δ σ ∞).contDiffAt
  have hL : (fderiv ℝ (implicitResidual t ρ δ σ) (0, 0) ∘L
      ContinuousLinearMap.inr ℝ ℝ ImplicitCoord).IsInvertible :=
    implicitVerticalDerivative_isInvertible t ρ δ σ (ne_of_gt hρ) (ne_of_gt hδ) hσ0
  let u := hF.implicitFunction (by simp) hL
  have hu0 : u 0 = 0 := hF.implicitFunction_apply_self (by simp) hL
  have hu : ContDiffAt ℝ ∞ u 0 := hF.contDiffAt_implicitFunction (by simp) hL
  refine ⟨u, hu0, hu, ?_, ?_⟩
  · simpa only [hu0] using hu.continuousAt.tendsto
  · simpa only [implicitResidual_zero t ρ δ σ hσ] using
      hF.eventually_apply_implicitFunction (by simp) hL

/-- The complete Gram identity follows from all four residual equations. -/
theorem gramMatrix_of_implicitResidual_eq_zero (t ρ δ σ ε : ℝ)
    (u : ImplicitCoord) (hρ : ρ ≠ 0)
    (hΦ : implicitResidual t ρ δ σ (ε, u) = 0) :
    gramMatrix (ρ • curve t + ε • (signedNormal t ρ δ σ + correctionDisplacement t u)) =
      ε • rankOneTarget + (ε^2*δ^2) • interiorTarget := by
  let z := correctionDisplacement t u
  let y := signedNormal t ρ δ σ
  let R := gramPolar (ρ • curve t) z + ε • (gramMatrix (y + z) - δ^2 • interiorTarget)
  have hπ : gramCoordinates R = 0 := by
    ext i
    fin_cases i
    · have h0 := congrFun hΦ (0 : Fin 4)
      norm_num [implicitResidual, R, y, z, gramCoordinates, Matrix.cons_val] at h0 ⊢
      exact h0
    · have h1 := congrFun hΦ (1 : Fin 4)
      norm_num [implicitResidual, R, y, z, gramCoordinates, Matrix.cons_val] at h1 ⊢
      exact h1
    · have h2 := congrFun hΦ (2 : Fin 4)
      norm_num [implicitResidual, R, y, z, gramCoordinates, Matrix.cons_val,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2 ⊢
      exact h2
  have hlast : gramFunctional t (gramMatrix (y + z) - δ^2 • interiorTarget) = 0 := by
    simpa only [implicitResidual, y, z, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] using
      congrFun hΦ (3 : Fin 4)
  have hℓ : gramFunctional t R = 0 := by
    dsimp only [R]
    rw [gramFunctional_add, gramFunctional_smul, gramFunctional_gramPolar_base,
      hlast, mul_zero, add_zero]
  have hR0 : interiorTarget.IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [interiorTarget, Matrix.transpose_apply]
  have hsym : R.IsSymm := (gramPolar_symmetric (ρ • curve t) z).add
    (((gramMatrix_symmetric (y + z)).sub (hR0.smul (δ^2))).smul ε)
  have hrel : R 0 0 + R 1 1 - R 2 2 = 0 := by
    have hp := gramPolar_relation (ρ • curve t) z
    have hq := gram_relation (y + z)
    simp only [R, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    norm_num [interiorTarget, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    linear_combination hp + ε*hq
  have h02 : R 0 2 = 0 := by
    simp [R, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      gramPolar_entry02, gram_entry02, interiorTarget]
  have hR : R = 0 := gramCoordinates_functional_injective t R hsym hrel h02 hπ hℓ
  have hbase : gramMatrix (ρ • curve t) = 0 := by
    rw [gramMatrix_smul, gramMatrix_curve, smul_zero]
  have hy : gramPolar (ρ • curve t) y = rankOneTarget := by
    dsimp only [y]
    rw [signedNormal, gramPolar_add_right, gramPolar_smul_right,
      gramPolar_base_normal t ρ hρ, gramPolar_base_kernelDirection, smul_zero, add_zero]
  change gramMatrix (ρ • curve t + ε • (y + z)) = _
  rw [gramMatrix_add_smul, hbase, zero_add, gramPolar_add_right, hy]
  ext i j
  have hij := congrFun (congrFun hR i) j
  simp only [R, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul] at hij ⊢
  linear_combination ε*hij

/-- Actual smooth corrections in the original ambient space with the exact Gram target. -/
theorem exists_corrected_gram_path (t ρ δ σ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hσ : σ^2 = 1) :
    ∃ z : ℝ → Coord,
      z 0 = 0 ∧ ContDiffAt ℝ ∞ z 0 ∧ Tendsto z (𝓝 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ),
        gramMatrix (ρ • curve t + ε • (signedNormal t ρ δ σ + z ε)) =
          ε • rankOneTarget + (ε^2*δ^2) • interiorTarget := by
  obtain ⟨u, hu0, hu, hut, hΦ⟩ := exists_implicitCorrection t ρ δ σ hρ hδ hσ
  let z : ℝ → Coord := fun ε => correctionDisplacement t (u ε)
  have hz0 : z 0 = 0 := by simp only [z, hu0, correctionDisplacement_zero]
  have hz : ContDiffAt ℝ ∞ z 0 :=
    (contDiff_correctionDisplacement t ∞).contDiffAt.comp 0 hu
  refine ⟨z, hz0, hz, ?_, ?_⟩
  · simpa only [hz0] using hz.continuousAt.tendsto
  · filter_upwards [hΦ] with ε hε
    exact gramMatrix_of_implicitResidual_eq_zero t ρ δ σ ε (u ε) (ne_of_gt hρ) hε

/-- The two signs yield the same exact matrix for every sufficiently small parameter. -/
theorem exists_opposite_corrected_gram_paths (t ρ δ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ zPlus zMinus : ℝ → Coord,
      zPlus 0 = 0 ∧ zMinus 0 = 0 ∧
      ContDiffAt ℝ ∞ zPlus 0 ∧ ContDiffAt ℝ ∞ zMinus 0 ∧
      Tendsto zPlus (𝓝 0) (𝓝 0) ∧ Tendsto zMinus (𝓝 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ),
        gramMatrix (ρ • curve t + ε • (normalDirection t ρ + δ • kernelDirection t + zPlus ε)) =
            ε • rankOneTarget + (ε^2*δ^2) • interiorTarget ∧
        gramMatrix (ρ • curve t + ε • (normalDirection t ρ - δ • kernelDirection t + zMinus ε)) =
            ε • rankOneTarget + (ε^2*δ^2) • interiorTarget := by
  obtain ⟨zPlus, hp0, hp, hpt, hpQ⟩ :=
    exists_corrected_gram_path t ρ δ 1 hρ hδ (by norm_num)
  obtain ⟨zMinus, hm0, hm, hmt, hmQ⟩ :=
    exists_corrected_gram_path t ρ δ (-1) hρ hδ (by norm_num)
  refine ⟨zPlus, zMinus, hp0, hm0, hp, hm, hpt, hmt, ?_⟩
  filter_upwards [hpQ, hmQ] with ε hpε hmε
  constructor
  · simpa only [signedNormal, one_mul] using hpε
  · simpa only [signedNormal, neg_one_mul, neg_smul, sub_eq_add_neg] using hmε

end PBCounterexample.Gram6
