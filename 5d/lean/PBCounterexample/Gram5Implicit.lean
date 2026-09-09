import PBCounterexample.Gram5Variations
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual jointly parameterized real solutions of the three matching equations. -/

namespace PBCounterexample.Gram5

open Matrix Filter
open scoped Topology ContDiff

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

abbrev CorrectionCoord := Fin 3 → ℝ
abbrev Parameters := ℝ × ℝ

def targetScale (t : ℝ) : ℝ := 3 - 3*t/8 + t^2
def normalScale (t : ℝ) : ℝ := Real.sqrt (targetScale t/3)

theorem targetScale_pos (t : ℝ) : 0 < targetScale t := by
  have h := sq_nonneg (t - 3/16)
  dsimp [targetScale]
  nlinarith

@[simp] theorem normalScale_zero : normalScale 0 = 1 := by
  norm_num [normalScale, targetScale]

theorem normalScale_sq (t : ℝ) : (normalScale t)^2 = targetScale t/3 :=
  Real.sq_sqrt (div_nonneg (targetScale_pos t).le (by norm_num))

theorem contDiff_normalScale (k : ℕ∞ω) : ContDiff ℝ k normalScale := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hf : ContDiffAt ℝ k (fun x : ℝ => targetScale x/3) t := by
    unfold targetScale
    fun_prop
  have hs : ContDiffAt ℝ k Real.sqrt (targetScale t/3) :=
    Real.contDiffAt_sqrt (ne_of_gt (div_pos (targetScale_pos t) (by norm_num)))
  change ContDiffAt ℝ k (fun x : ℝ => Real.sqrt (targetScale x/3)) t
  simpa only [Function.comp_def] using! hs.comp t hf

def signedNormal (δ σ t : ℝ) : Coord :=
  normalDirection + (σ*δ*normalScale t) • signDirection

def implicitResidual (δ σ : ℝ) (p : Parameters × CorrectionCoord) : CorrectionCoord :=
  let ε := p.1.1
  let t := p.1.2
  let z := correctionEmbedding p.2
  let v := signedNormal δ σ t + z
  ![linearA z + ε*(quadraticA v - t^2*δ^2),
    linearB z + ε*(quadraticB v - (3*t/8)*δ^2),
    quadraticF v - δ^2*targetScale t]

def verticalMatrix (δ σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-4, 1, 0; 2, -3, 0;
    4+10*σ*δ, -6-4*σ*δ, 6*σ*δ]

theorem verticalMatrix_det (δ σ : ℝ) : (verticalMatrix δ σ).det = 60*σ*δ := by
  norm_num [verticalMatrix, Matrix.det_fin_three]
  ring

theorem implicitResidual_zero_slice (δ σ t : ℝ) (hσ : σ^2 = 1) :
    implicitResidual δ σ ((0, t), 0) = 0 := by
  have hlast : quadraticF (signedNormal δ σ t) - δ^2*targetScale t = 0 := by
    rw [signedNormal, quadraticF_normal_add_sign]
    rw [mul_pow, mul_pow, hσ, normalScale_sq]
    ring
  ext i
  fin_cases i <;>
    norm_num [implicitResidual, correctionEmbedding_zero, linearA,
      linearB, hlast]

theorem contDiff_implicitResidual (δ σ : ℝ) (k : ℕ∞ω) :
    ContDiff ℝ k (implicitResidual δ σ) := by
  have hr : ContDiff ℝ k (fun p : Parameters × CorrectionCoord => normalScale p.1.2) :=
    (contDiff_normalScale k).comp (contDiff_snd.comp contDiff_fst)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    norm_num [implicitResidual, signedNormal, correctionEmbedding,
      normalDirection, signDirection, linearA, linearB, quadraticA,
      quadraticB, quadraticW, quadraticF, targetScale,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> fun_prop

theorem implicitResidual_vertical_line (δ σ t : ℝ) (u : CorrectionCoord) :
    implicitResidual δ σ ((0, 0), t • u) =
      implicitResidual δ σ ((0, 0), 0) +
      t • (verticalMatrix δ σ *ᵥ u) +
      t^2 • (![0, 0, quadraticF (correctionEmbedding u)] : CorrectionCoord) := by
  ext i
  fin_cases i <;>
    norm_num [implicitResidual, verticalMatrix, signedNormal,
      correctionEmbedding, normalDirection, signDirection, linearA,
      linearB, quadraticA, quadraticB, quadraticW, quadraticF,
      targetScale, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem hasDerivAt_implicitResidual_vertical_line (δ σ : ℝ) (u : CorrectionCoord) :
    HasDerivAt (fun t : ℝ => implicitResidual δ σ ((0, 0), t • u))
      (verticalMatrix δ σ *ᵥ u) 0 := by
  have heq : (fun t : ℝ => implicitResidual δ σ ((0, 0), t • u)) =
      (fun t : ℝ => implicitResidual δ σ ((0, 0), 0) +
        t • (verticalMatrix δ σ *ᵥ u) +
        t^2 • (![0, 0, quadraticF (correctionEmbedding u)] : CorrectionCoord)) :=
    funext fun t => implicitResidual_vertical_line δ σ t u
  rw [heq]
  convert! (((hasDerivAt_const (0 : ℝ) (implicitResidual δ σ ((0, 0), 0))).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (verticalMatrix δ σ *ᵥ u))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const
      (![0, 0, quadraticF (correctionEmbedding u)] : CorrectionCoord))) using 1 <;> simp

def verticalDerivative (δ σ : ℝ) : CorrectionCoord →L[ℝ] CorrectionCoord :=
  fderiv ℝ (implicitResidual δ σ) ((0, 0), 0) ∘L
    ContinuousLinearMap.inr ℝ Parameters CorrectionCoord

theorem verticalDerivative_apply (δ σ : ℝ) (u : CorrectionCoord) :
    verticalDerivative δ σ u = verticalMatrix δ σ *ᵥ u := by
  have hline : HasDerivAt (fun t : ℝ => ((0 : Parameters), t • u)) (0, u) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (0 : Parameters)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1 <;> simp
  have hF := (contDiff_implicitResidual δ σ 1).differentiable_one ((0, 0), 0)
  have hc := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  change (fderiv ℝ (implicitResidual δ σ) ((0, 0), 0)) (0, u) = _
  exact hc.unique (hasDerivAt_implicitResidual_vertical_line δ σ u)

theorem verticalDerivative_isInvertible (δ σ : ℝ) (hδ : δ ≠ 0) (hσ : σ ≠ 0) :
    (verticalDerivative δ σ).IsInvertible := by
  have hdet : (verticalMatrix δ σ).det ≠ 0 := by
    rw [verticalMatrix_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hσ) hδ
  have hm : Function.Injective (verticalMatrix δ σ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  let L := verticalDerivative δ σ
  have hi : Function.Injective L := by
    intro u v huv
    apply hm
    simpa only [L, verticalDerivative_apply] using huv
  have hs : Function.Surjective L :=
    LinearMap.surjective_of_injective (f := L.toLinearMap) hi
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, ?_⟩
  ext u i
  rfl

/-- The equations and regularity hold throughout a single open rectangle.
The zero correction at epsilon zero holds along its entire lambda interval. -/
theorem exists_implicitCorrection (δ σ : ℝ) (hδ : 0 < δ) (hσ : σ^2 = 1) :
    ∃ u : Parameters → CorrectionCoord, ∃ η : ℝ, 0 < η ∧
      (∀ ε t : ℝ, |ε| < η → |t| < η →
        implicitResidual δ σ ((ε, t), u (ε, t)) = 0) ∧
      (∀ ε t : ℝ, |ε| < η → |t| < η → ContDiffAt ℝ 1 u (ε, t)) ∧
      (∀ t : ℝ, |t| < η → u (0, t) = 0) := by
  have hσ0 : σ ≠ 0 := by intro h; simp [h] at hσ
  have hF : ContDiffAt ℝ ∞ (implicitResidual δ σ) ((0, 0), 0) :=
    (contDiff_implicitResidual δ σ ∞).contDiffAt
  have hL : (fderiv ℝ (implicitResidual δ σ) ((0, 0), 0) ∘L
      ContinuousLinearMap.inr ℝ Parameters CorrectionCoord).IsInvertible :=
    verticalDerivative_isInvertible δ σ (ne_of_gt hδ) hσ0
  let u := hF.implicitFunction (by simp) hL
  have hu : ContDiffAt ℝ ∞ u (0, 0) :=
    hF.contDiffAt_implicitFunction (by simp) hL
  have hu1 : ContDiffAt ℝ 1 u (0, 0) := hu.of_le (by simp)
  have hreg : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ 1 u p :=
    hu1.eventually (by simp)
  have heq : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)),
      implicitResidual δ σ (p, u p) = 0 := by
    simpa only [implicitResidual_zero_slice δ σ 0 hσ] using
      hF.eventually_apply_implicitFunction (by simp) hL
  have hslice : ∀ᶠ t : ℝ in 𝓝 0, u (0, t) = 0 := by
    have ht : Tendsto (fun t : ℝ => (((0 : ℝ), t), (0 : CorrectionCoord)))
        (𝓝 0) (𝓝 (((0 : ℝ), (0 : ℝ)), (0 : CorrectionCoord))) :=
      ((continuous_const.prodMk continuous_id).prodMk continuous_const).tendsto 0
    have huniq := ht.eventually
      (hF.eventually_apply_eq_iff_implicitFunction (by simp) hL)
    filter_upwards [huniq] with t ht
    apply ht.mp
    rw [implicitResidual_zero_slice δ σ t hσ,
      implicitResidual_zero_slice δ σ 0 hσ]
  have hslice' : ∀ᶠ p : Parameters in 𝓝 (0, 0), u (0, p.2) = 0 :=
    (continuous_snd.tendsto (0, 0)).eventually hslice
  have hall := heq.and (hreg.and hslice')
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hall
  have hrect (ε t : ℝ) (hε : |ε| < η) (ht : |t| < η) :
      implicitResidual δ σ ((ε, t), u (ε, t)) = 0 ∧
        ContDiffAt ℝ 1 u (ε, t) ∧ u (0, t) = 0 := by
    apply hball
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq,
      sub_zero, max_lt_iff] using And.intro hε ht
  refine ⟨u, η, hη, ?_, ?_, ?_⟩
  · exact fun ε t hε ht => (hrect ε t hε ht).1
  · exact fun ε t hε ht => (hrect ε t hε ht).2.1
  · intro t ht
    exact (hrect 0 t (by simpa using hη) ht).2.2

end

end PBCounterexample.Gram5
