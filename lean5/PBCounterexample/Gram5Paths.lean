import PBCounterexample.Gram5Implicit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Corrected real points on a joint rectangle and their exact matching values. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology ContDiff

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- The correction is defined on the full parameter plane; its equations and
regularity are required on one common open rectangle. -/
structure CorrectionFamily (δ σ : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  correction : Parameters → CorrectionCoord
  equation : ∀ ε t : ℝ, |ε| < radius → |t| < radius →
    implicitResidual δ σ ((ε, t), correction (ε, t)) = 0
  regular : ∀ ε t : ℝ, |ε| < radius → |t| < radius →
    ContDiffAt ℝ 1 correction (ε, t)
  zero_slice : ∀ t : ℝ, |t| < radius → correction (0, t) = 0

theorem exists_correctionFamily (δ σ : ℝ) (hδ : 0 < δ) (hσ : σ^2 = 1) :
    Nonempty (CorrectionFamily δ σ) := by
  obtain ⟨u, η, hη, heq, hreg, hzero⟩ := exists_implicitCorrection δ σ hδ hσ
  exact ⟨⟨η, hη, u, heq, hreg, hzero⟩⟩

namespace CorrectionFamily

variable {δ σ : ℝ} (F : CorrectionFamily δ σ)

def direction (ε t : ℝ) : Coord :=
  signedNormal δ σ t + correctionEmbedding (F.correction (ε, t))

def point (ε t : ℝ) : Coord := affinePoint ε (F.direction ε t)

def scaledPoint (ε t : ℝ) : Coord := weightedScale t (F.point ε t)

@[simp] theorem direction_first (ε t : ℝ) : F.direction ε t 0 = 0 := by
  simp [direction, signedNormal, normalDirection, signDirection]

@[simp] theorem point_zero (t : ℝ) : F.point 0 t = basePoint := by
  simp [point, affinePoint]

theorem direction_zero (t : ℝ) (ht : |t| < F.radius) :
    F.direction 0 t = signedNormal δ σ t := by
  simp only [direction, F.zero_slice t ht, correctionEmbedding_zero, add_zero]

@[simp] theorem direction_zero_zero :
    F.direction 0 0 = normalDirection + (σ*δ) • signDirection := by
  rw [F.direction_zero 0 (by simpa using F.radius_pos)]
  simp [signedNormal]

theorem linearA_direction (ε t : ℝ) :
    linearA (F.direction ε t) = linearA (correctionEmbedding (F.correction (ε, t))) := by
  norm_num [direction, signedNormal, normalDirection, signDirection,
    linearA, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem linearB_direction (ε t : ℝ) :
    linearB (F.direction ε t) = linearB (correctionEmbedding (F.correction (ε, t))) := by
  norm_num [direction, signedNormal, normalDirection, signDirection,
    linearB, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem matchedA (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    eval (F.point ε t) invariantA = t^2*ε^2*δ^2 := by
  have heq := congrFun (F.equation ε t hε ht) 0
  change linearA (correctionEmbedding (F.correction (ε, t))) +
    ε*(quadraticA (F.direction ε t) - t^2*δ^2) = 0 at heq
  rw [point, eval_invariantA_affine ε _ (F.direction_first ε t), F.linearA_direction]
  calc
    ε*linearA (correctionEmbedding (F.correction (ε, t))) +
        ε^2*quadraticA (F.direction ε t) =
      ε*(linearA (correctionEmbedding (F.correction (ε, t))) +
        ε*(quadraticA (F.direction ε t) - t^2*δ^2)) + t^2*ε^2*δ^2 := by ring
    _ = _ := by rw [heq]; ring

theorem matchedB (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    eval (F.point ε t) invariantB = (3*t/8)*ε^2*δ^2 := by
  have heq := congrFun (F.equation ε t hε ht) 1
  change linearB (correctionEmbedding (F.correction (ε, t))) +
    ε*(quadraticB (F.direction ε t) - (3*t/8)*δ^2) = 0 at heq
  rw [point, eval_invariantB_affine ε _ (F.direction_first ε t), F.linearB_direction]
  calc
    ε*linearB (correctionEmbedding (F.correction (ε, t))) +
        ε^2*quadraticB (F.direction ε t) =
      ε*(linearB (correctionEmbedding (F.correction (ε, t))) +
        ε*(quadraticB (F.direction ε t) - (3*t/8)*δ^2)) + (3*t/8)*ε^2*δ^2 := by ring
    _ = _ := by rw [heq]; ring

theorem matchedW (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    eval (F.point ε t) invariantW = 3*ε^2*δ^2 := by
  have heq := congrFun (F.equation ε t hε ht) 2
  change quadraticF (F.direction ε t) - δ^2*targetScale t = 0 at heq
  have hF : eval (F.point ε t) invariantW =
      eval (F.point ε t) invariantB - eval (F.point ε t) invariantA +
        ε^2*quadraticF (F.direction ε t) := by
    simp only [point, eval_invariantW_affine ε _ (F.direction_first ε t),
      eval_invariantB_affine ε _ (F.direction_first ε t),
      eval_invariantA_affine ε _ (F.direction_first ε t), linearW_eq, quadraticF]
    ring
  rw [hF, F.matchedA ε t hε ht, F.matchedB ε t hε ht, sub_eq_zero.mp heq]
  unfold targetScale
  ring

theorem contDiffAt_direction (ε t : ℝ) (hε : |ε| < F.radius)
    (ht : |t| < F.radius) :
    ContDiffAt ℝ 1 (fun p : Parameters => F.direction p.1 p.2) (ε, t) := by
  have hu := F.regular ε t hε ht
  have he : ContDiff ℝ 1 correctionEmbedding := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> norm_num [correctionEmbedding] <;> fun_prop
  have hy : ContDiff ℝ 1 (fun p : Parameters => signedNormal δ σ p.2) := by
    have hr : ContDiff ℝ 1 (fun p : Parameters => normalScale p.2) :=
      (contDiff_normalScale 1).comp contDiff_snd
    unfold signedNormal
    fun_prop
  exact hy.contDiffAt.add (he.contDiffAt.comp (ε, t) hu)

theorem contDiffAt_point (ε t : ℝ) (hε : |ε| < F.radius)
    (ht : |t| < F.radius) :
    ContDiffAt ℝ 1 (fun p : Parameters => F.point p.1 p.2) (ε, t) := by
  have hd := F.contDiffAt_direction ε t hε ht
  change ContDiffAt ℝ 1 (fun p : Parameters => basePoint + p.1 • F.direction p.1 p.2) _
  exact contDiffAt_const.add (contDiffAt_fst.smul hd)

theorem tendsto_point_lambda (ε : ℝ) (hε : |ε| < F.radius) :
    Tendsto (fun t : ℝ => F.point ε t) (𝓝 0) (𝓝 (F.point ε 0)) := by
  have hF := (F.contDiffAt_point ε 0 hε (by simpa using F.radius_pos)).continuousAt
  exact hF.tendsto.comp ((continuous_const.prodMk continuous_id).tendsto 0)

theorem tendsto_point_epsilon :
    Tendsto (fun ε : ℝ => F.point ε 0) (𝓝 0) (𝓝 basePoint) := by
  have hF := (F.contDiffAt_point 0 0 (by simpa using F.radius_pos)
    (by simpa using F.radius_pos)).continuousAt
  simpa only [F.point_zero, Function.comp_def, id_eq] using! hF.tendsto.comp
    ((continuous_id.prodMk continuous_const).tendsto 0)

theorem hasDerivAt_point_epsilon :
    HasDerivAt (fun ε : ℝ => F.point ε 0)
      (normalDirection + (σ*δ) • signDirection) 0 := by
  have hd := F.contDiffAt_direction 0 0 (by simpa using F.radius_pos)
    (by simpa using F.radius_pos)
  have hslice : ContDiffAt ℝ 1 (fun ε : ℝ => (ε, (0 : ℝ))) 0 := by fun_prop
  have hs : ContDiffAt ℝ 1 (fun ε : ℝ => F.direction ε 0) 0 := by
    simpa only [Function.comp_def] using!
      hd.comp (f := fun ε : ℝ => (ε, (0 : ℝ))) 0 hslice
  have hder := hs.differentiableAt_one.hasDerivAt
  simpa only [point, affinePoint, id_eq, Pi.smul_apply,
    zero_smul, one_smul, zero_add, F.direction_zero_zero] using!
      ((hasDerivAt_id (0 : ℝ)).smul hder).const_add basePoint

theorem hasDerivAt_eval_point_epsilon (P : Poly) :
    HasDerivAt (fun ε : ℝ => eval (F.point ε 0) P)
      (differential P (normalDirection + (σ*δ) • signDirection)) 0 := by
  have hP := (contDiff_eval P 1).differentiable_one basePoint
  simpa only [differential] using! hP.hasFDerivAt.comp_hasDerivAt_of_eq 0
    F.hasDerivAt_point_epsilon (F.point_zero 0).symm

theorem tendsto_eval_point_epsilon (P : Poly) :
    Tendsto (fun ε : ℝ => eval (F.point ε 0) P)
      (𝓝 0) (𝓝 (eval basePoint P)) :=
  (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp F.tendsto_point_epsilon

theorem tendsto_eval_point_div (P : Poly) (hP : eval basePoint P = 0) :
    Tendsto (fun ε : ℝ => eval (F.point ε 0) P / ε)
      (𝓝[>] 0) (𝓝 (differential P (normalDirection + (σ*δ) • signDirection))) := by
  simpa only [zero_add, F.point_zero, hP, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using
      (F.hasDerivAt_eval_point_epsilon P).tendsto_slope_zero_right

end CorrectionFamily

end

end PBCounterexample.Gram5
