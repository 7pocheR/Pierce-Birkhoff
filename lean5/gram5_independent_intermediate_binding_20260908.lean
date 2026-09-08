import gram5_independent_binding_20260908

/-!
Intermediate bindings to the independently expanded coefficient and path
definitions.  The independent contract remains unchanged.  In particular, its
coefficient-sum differential is identified with the actual differential before
the complete low-weight kernel is transported.
-/

noncomputable section

open MvPolynomial Gram5IndependentContract
open scoped BigOperators Topology

namespace PBCounterexample.Gram5IndependentIntermediateBinding

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

theorem basePoint_eq : Gram5.basePoint = one := by
  ext i
  fin_cases i <;> rfl

theorem weights_eq : Gram5.weights = weight := rfl

theorem scale_eq (lam : ℝ) (z : Point) :
    Gram5IndependentContract.scale lam z =
      WeightedPolynomial.scale Gram5.weights lam z := rfl

theorem normalDirection_eq : Gram5.normalDirection = n := rfl
theorem signDirection_eq : Gram5.signDirection = j := rfl
theorem invariantA_eq : Gram5.invariantA = testA := rfl
theorem invariantB_eq : Gram5.invariantB = testB := rfl
theorem invariantW_eq : Gram5.invariantW = testW := rfl

theorem monomialWeight_eq (m : Fin 5 →₀ ℕ) :
    Finsupp.weight Gram5.weights m = monomialWeight m := by
  rw [Finsupp.weight_eq_sum]
  simp only [monomialWeight, weights_eq, nsmul_eq_mul, Nat.cast_id, mul_comm]

theorem ofWeight_iff (w : ℕ) (p : Poly) :
    OfWeight w p ↔ p.IsWeightedHomogeneous Gram5.weights w := by
  constructor
  · intro h m hm
    simpa only [monomialWeight_eq] using h m hm
  · intro h m hm
    simpa only [monomialWeight_eq] using h hm

theorem differential_monomial (m : Fin 5 →₀ ℕ) (r : ℝ) (v : Point) :
    Gram5.differential (monomial m r) v =
      r * ∑ i : Fin 5, (m i : ℝ) * v i := by
  rw [MvPolynomial.monomial_eq, Gram5.differential_C_mul]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  norm_num [Fin.prod_univ_succ, Fin.sum_univ_succ, Gram5.basePoint] <;> ring

/-- This equality holds for every real polynomial, not only a fixed finite
basis or a bounded-degree collection. -/
theorem differential_eq_linearAtOne (p : Poly) (v : Point) :
    Gram5.differential p v = linearAtOne p v := by
  calc
    Gram5.differential p v = Gram5.differential
        (∑ m ∈ p.support, monomial m (p.coeff m)) v :=
      congrArg (fun P : Poly => Gram5.differential P v) p.as_sum
    _ = linearAtOne p v := by
      rw [Gram5.differential_sum]
      simp only [differential_monomial, linearAtOne]

theorem exceptional_iff (w : ℕ) (p : Poly) :
    Gram5.IsExceptional w p ↔ Exceptional w p := by
  simp only [Gram5.IsExceptional, Exceptional,
    invariantA_eq, invariantB_eq, invariantW_eq]

theorem exceptional_value_derivative_zero (w : ℕ) (p : Poly)
    (hp : Gram5.IsExceptional w p) :
    eval Gram5.basePoint p = 0 ∧
      Gram5.differential p Gram5.normalDirection = 0 := by
  have h2 : Gram5.differential (2 : Poly) Gram5.normalDirection = 0 := by
    simpa only [map_ofNat] using Gram5.differential_C 2 Gram5.normalDirection
  have h3 : Gram5.differential (3 : Poly) Gram5.normalDirection = 0 := by
    simpa only [map_ofNat] using Gram5.differential_C 3 Gram5.normalDirection
  have h4 : Gram5.differential (4 : Poly) Gram5.normalDirection = 0 := by
    simpa only [map_ofNat] using Gram5.differential_C 4 Gram5.normalDirection
  unfold Gram5.normalDirection at h2 h3 h4
  have hA : eval Gram5.basePoint Gram5.invariantA = 0 ∧
      Gram5.differential Gram5.invariantA Gram5.normalDirection = 0 := by
    constructor <;> norm_num [Gram5.invariantA, Gram5.a, Gram5.b, Gram5.c,
      Gram5.d, Gram5.e, Gram5.basePoint, Gram5.normalDirection, h3, h4]
  have hB : eval Gram5.basePoint Gram5.invariantB = 0 ∧
      Gram5.differential Gram5.invariantB Gram5.normalDirection = 0 := by
    constructor <;> norm_num [Gram5.invariantB, Gram5.a, Gram5.b, Gram5.c,
      Gram5.d, Gram5.e, Gram5.basePoint, Gram5.normalDirection, h2, h3]
  have hW : eval Gram5.basePoint Gram5.invariantW = 0 ∧
      Gram5.differential Gram5.invariantW Gram5.normalDirection = 0 := by
    constructor <;> norm_num [Gram5.invariantW, Gram5.a, Gram5.b, Gram5.c,
      Gram5.d, Gram5.e, Gram5.basePoint, Gram5.normalDirection, h3, h4]
  rcases hp with rfl | ⟨_, r, rfl⟩ | ⟨_, r, rfl⟩ | ⟨_, r, rfl⟩
  · simp
  · simp only [map_mul, eval_C, Gram5.differential_C_mul, hA.1, hA.2, mul_zero,
      and_self]
  · simp only [map_mul, eval_C, Gram5.differential_C_mul, hB.1, hB.2, mul_zero,
      and_self]
  · simp only [map_mul, eval_C, Gram5.differential_C_mul, hW.1, hW.2, mul_zero,
      and_self]

theorem complete_kernel_claim : CompleteKernelClaim := by
  intro w hw p hp
  constructor
  · rintro ⟨hvalue, hderivative⟩
    apply (exceptional_iff w p).mp
    apply Gram5.isExceptional_of_value_derivative_zero p w
      ((ofWeight_iff w p).mp hp) hw
    · simpa only [basePoint_eq] using hvalue
    · simpa only [differential_eq_linearAtOne, normalDirection_eq] using hderivative
  · intro hexceptional
    have h := exceptional_value_derivative_zero w p
      ((exceptional_iff w p).mpr hexceptional)
    simpa only [basePoint_eq, differential_eq_linearAtOne, normalDirection_eq] using h

theorem component_eq (w : ℕ) (p : Poly) :
    component w p = weightedHomogeneousComponent Gram5.weights w p := by
  rw [weightedHomogeneousComponent_apply, Finset.sum_filter]
  simp only [component, monomialWeight_eq]

theorem weighted_decomposition_claim : WeightedDecompositionClaim := by
  intro p
  classical
  ext m
  simp only [coeff_sum, component_eq, coeff_weightedHomogeneousComponent,
    monomialWeight_eq]
  by_cases hm : p.coeff m = 0
  · simp only [hm, ite_self, Finset.sum_const_zero]
  · have hmem : monomialWeight m ∈ p.support.image monomialWeight :=
      Finset.mem_image.mpr ⟨m, mem_support_iff.mpr hm, rfl⟩
    simp [hmem]

theorem weighted_evaluation_claim : WeightedEvaluationClaim := by
  intro w p hp lam z
  rw [scale_eq]
  exact WeightedPolynomial.eval_scale_of_weightedHomogeneous
    ((ofWeight_iff w p).mp hp) z lam

theorem initialDirection_eq (delta : ℝ) (side : Bool) (lam : ℝ) :
    initialDirection delta side lam =
      Gram5.signedNormal delta (orientation side) lam := rfl

theorem correction_eq (u : Fin 3 → ℝ) :
    correction u = Gram5.correctionEmbedding u := rfl

theorem residual_eq (delta : ℝ) (side : Bool) (epsilon lam : ℝ)
    (u : Fin 3 → ℝ) :
    residual delta side epsilon lam u =
      Gram5.implicitResidual delta (orientation side) ((epsilon, lam), u) := rfl

theorem jacobian_eq (delta : ℝ) (side : Bool) :
    Gram5.verticalMatrix delta (orientation side) = expectedJacobian delta side := rfl

/-- Both actual families are restricted to one common positive rectangle. -/
def ofFamilies {delta : ℝ}
    (Fplus : Gram5.CorrectionFamily delta 1)
    (Fminus : Gram5.CorrectionFamily delta (-1)) : CorrectedPathData delta where
  epsilonRadius := min Fplus.radius Fminus.radius
  lambdaRadius := min Fplus.radius Fminus.radius
  epsilonRadius_pos := lt_min Fplus.radius_pos Fminus.radius_pos
  lambdaRadius_pos := lt_min Fplus.radius_pos Fminus.radius_pos
  z side := match side with
    | false => Fminus.correction
    | true => Fplus.correction
  smooth side := by
    intro p hp
    cases side with
    | false =>
        exact (Fminus.regular p.1 p.2
          (hp.1.trans_le (min_le_right _ _))
          (hp.2.trans_le (min_le_right _ _))).contDiffWithinAt
    | true =>
        exact (Fplus.regular p.1 p.2
          (hp.1.trans_le (min_le_left _ _))
          (hp.2.trans_le (min_le_left _ _))).contDiffWithinAt
  zero_at_epsilon_zero side lam hlam := by
    cases side with
    | false => exact Fminus.zero_slice lam (hlam.trans_le (min_le_right _ _))
    | true => exact Fplus.zero_slice lam (hlam.trans_le (min_le_left _ _))
  residual_zero side epsilon lam hepsilon hlam := by
    rw [residual_eq]
    cases side with
    | false =>
        exact Fminus.equation epsilon lam
          (hepsilon.trans_le (min_le_right _ _))
          (hlam.trans_le (min_le_right _ _))
    | true =>
        exact Fplus.equation epsilon lam
          (hepsilon.trans_le (min_le_left _ _))
          (hlam.trans_le (min_le_left _ _))

theorem actual_ift_claim : ActualIFTClaim := by
  intro delta hdelta
  obtain ⟨Fplus⟩ := Gram5.exists_correctionFamily delta 1 hdelta (by norm_num)
  obtain ⟨Fminus⟩ := Gram5.exists_correctionFamily delta (-1) hdelta (by norm_num)
  exact ⟨ofFamilies Fplus Fminus⟩

theorem normalizedPoint_eq {delta : ℝ} (data : CorrectedPathData delta)
    (side : Bool) (epsilon lam : ℝ) :
    normalizedPoint data side epsilon lam = Gram5.affinePoint epsilon
      (Gram5.signedNormal delta (orientation side) lam +
        Gram5.correctionEmbedding (data.z side (epsilon, lam))) := by
  simp only [normalizedPoint, Gram5.affinePoint, basePoint_eq,
    initialDirection_eq, correction_eq]

theorem normalizedPoint_ofFamilies_true {delta : ℝ}
    (Fplus : Gram5.CorrectionFamily delta 1)
    (Fminus : Gram5.CorrectionFamily delta (-1)) (epsilon lam : ℝ) :
    normalizedPoint (ofFamilies Fplus Fminus) true epsilon lam =
      Fplus.point epsilon lam := by
  exact normalizedPoint_eq (ofFamilies Fplus Fminus) true epsilon lam

theorem normalizedPoint_ofFamilies_false {delta : ℝ}
    (Fplus : Gram5.CorrectionFamily delta 1)
    (Fminus : Gram5.CorrectionFamily delta (-1)) (epsilon lam : ℝ) :
    normalizedPoint (ofFamilies Fplus Fminus) false epsilon lam =
      Fminus.point epsilon lam := by
  exact normalizedPoint_eq (ofFamilies Fplus Fminus) false epsilon lam

theorem actualPoint_ofFamilies_true {delta : ℝ}
    (Fplus : Gram5.CorrectionFamily delta 1)
    (Fminus : Gram5.CorrectionFamily delta (-1)) (epsilon lam : ℝ) :
    actualPoint (ofFamilies Fplus Fminus) true epsilon lam =
      Fplus.scaledPoint epsilon lam := by
  simp only [actualPoint, normalizedPoint_ofFamilies_true,
    Gram5.CorrectionFamily.scaledPoint, Gram5.weightedScale, scale_eq]

theorem actualPoint_ofFamilies_false {delta : ℝ}
    (Fplus : Gram5.CorrectionFamily delta 1)
    (Fminus : Gram5.CorrectionFamily delta (-1)) (epsilon lam : ℝ) :
    actualPoint (ofFamilies Fplus Fminus) false epsilon lam =
      Fminus.scaledPoint epsilon lam := by
  simp only [actualPoint, normalizedPoint_ofFamilies_false,
    Gram5.CorrectionFamily.scaledPoint, Gram5.weightedScale, scale_eq]

theorem isOpen_rectangle (epsilonRadius lambdaRadius : ℝ) :
    IsOpen (rectangle epsilonRadius lambdaRadius) :=
  (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem fixed_epsilon_continuity_claim : FixedEpsilonContinuityClaim := by
  intro delta data epsilon hepsilon side
  have hmem : (epsilon, (0 : ℝ)) ∈ rectangle data.epsilonRadius data.lambdaRadius :=
    ⟨hepsilon, by simpa using data.lambdaRadius_pos⟩
  have hz := (data.smooth side).continuousOn.continuousAt
    ((isOpen_rectangle _ _).mem_nhds hmem)
  have hzslice : ContinuousAt (fun lam : ℝ => data.z side (epsilon, lam)) 0 :=
    hz.comp (continuous_const.prodMk continuous_id).continuousAt
  have hnormal : Continuous (Gram5.signedNormal delta (orientation side)) := by
    have hr := (Gram5.contDiff_normalScale 1).continuous
    unfold Gram5.signedNormal
    fun_prop
  have hembedding : Continuous Gram5.correctionEmbedding := by
    apply continuous_pi
    intro i
    fin_cases i <;> norm_num [Gram5.correctionEmbedding] <;> fun_prop
  have hd := hnormal.continuousAt.add (hembedding.continuousAt.comp hzslice)
  have hfinal : ContinuousAt (fun lam : ℝ => Gram5.basePoint + epsilon •
      (Gram5.signedNormal delta (orientation side) lam +
        Gram5.correctionEmbedding (data.z side (epsilon, lam)))) 0 :=
    continuousAt_const.add (hd.const_smul epsilon)
  have hfunction : normalizedPoint data side epsilon =
      (fun lam : ℝ => Gram5.basePoint + epsilon •
        (Gram5.signedNormal delta (orientation side) lam +
          Gram5.correctionEmbedding (data.z side (epsilon, lam)))) := by
    funext lam
    exact normalizedPoint_eq data side epsilon lam
  rw [hfunction]
  exact hfinal

/-- Exact matching holds for any data satisfying the independent residual
contract, not only for the data assembled from the implementation families. -/
theorem exact_target_claim : ExactTargetClaim := by
  intro delta data side epsilon lam hepsilon hlam
  let u := data.z side (epsilon, lam)
  let v := Gram5.signedNormal delta (orientation side) lam +
    Gram5.correctionEmbedding u
  have hv : v 0 = 0 := by
    simp [v, Gram5.signedNormal, Gram5.normalDirection, Gram5.signDirection,
      Gram5.correctionEmbedding]
  have hpoint : normalizedPoint data side epsilon lam =
      Gram5.affinePoint epsilon v :=
    normalizedPoint_eq data side epsilon lam
  have heq := data.residual_zero side epsilon lam hepsilon hlam
  rw [residual_eq] at heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change Gram5.linearA (Gram5.correctionEmbedding u) +
    epsilon*(Gram5.quadraticA v-lam^2*delta^2) = 0 at h0
  change Gram5.linearB (Gram5.correctionEmbedding u) +
    epsilon*(Gram5.quadraticB v-(3*lam/8)*delta^2) = 0 at h1
  change Gram5.quadraticF v-delta^2*Gram5.targetScale lam = 0 at h2
  have hlinA : Gram5.linearA v = Gram5.linearA (Gram5.correctionEmbedding u) := by
    norm_num [v, Gram5.linearA, Gram5.signedNormal, Gram5.normalDirection,
      Gram5.signDirection, Gram5.correctionEmbedding, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;> ring
  have hlinB : Gram5.linearB v = Gram5.linearB (Gram5.correctionEmbedding u) := by
    norm_num [v, Gram5.linearB, Gram5.signedNormal, Gram5.normalDirection,
      Gram5.signDirection, Gram5.correctionEmbedding, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;> ring
  have hA : eval (normalizedPoint data side epsilon lam) testA =
      lam^2*epsilon^2*delta^2 := by
    rw [hpoint, ← invariantA_eq, Gram5.eval_invariantA_affine epsilon v hv, hlinA]
    calc
      epsilon*Gram5.linearA (Gram5.correctionEmbedding u) +
          epsilon^2*Gram5.quadraticA v =
        epsilon*(Gram5.linearA (Gram5.correctionEmbedding u) +
          epsilon*(Gram5.quadraticA v-lam^2*delta^2)) +
            lam^2*epsilon^2*delta^2 := by ring
      _ = _ := by rw [h0]; ring
  have hB : eval (normalizedPoint data side epsilon lam) testB =
      (3*lam/8)*epsilon^2*delta^2 := by
    rw [hpoint, ← invariantB_eq, Gram5.eval_invariantB_affine epsilon v hv, hlinB]
    calc
      epsilon*Gram5.linearB (Gram5.correctionEmbedding u) +
          epsilon^2*Gram5.quadraticB v =
        epsilon*(Gram5.linearB (Gram5.correctionEmbedding u) +
          epsilon*(Gram5.quadraticB v-(3*lam/8)*delta^2)) +
            (3*lam/8)*epsilon^2*delta^2 := by ring
      _ = _ := by rw [h1]; ring
  have hW : eval (normalizedPoint data side epsilon lam) testW =
      3*epsilon^2*delta^2 := by
    have hidentity : eval (normalizedPoint data side epsilon lam) testW =
        eval (normalizedPoint data side epsilon lam) testB -
        eval (normalizedPoint data side epsilon lam) testA +
          epsilon^2*Gram5.quadraticF v := by
      rw [hpoint, ← invariantA_eq, ← invariantB_eq, ← invariantW_eq,
        Gram5.eval_invariantW_affine epsilon v hv,
        Gram5.eval_invariantB_affine epsilon v hv,
        Gram5.eval_invariantA_affine epsilon v hv, Gram5.linearW_eq]
      unfold Gram5.quadraticF
      ring
    rw [hidentity, hA, hB, sub_eq_zero.mp h2]
    unfold Gram5.targetScale
    ring
  exact ⟨hA, hB, hW⟩

/-- The order is an arbitrary finite family, then actual common path data,
then one fixed positive epsilon, then every sufficiently small positive lambda. -/
theorem weighted_finite_collection_claim : WeightedFiniteCollectionClaim := by
  intro S
  obtain ⟨delta, hdelta, hsmall, Fplus, Fminus, epsilon,
    hepsilon, hepsilonPlus, hepsilonMinus, heventually⟩ :=
      Gram5.exists_finite_threshold_paths S
  let data := ofFamilies Fplus Fminus
  have hepsilonBound : epsilon < data.epsilonRadius := by
    exact lt_min
      ((le_abs_self epsilon).trans_lt hepsilonPlus)
      ((le_abs_self epsilon).trans_lt hepsilonMinus)
  obtain ⟨bound, hbound, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp heventually
  let lambdaBound := min bound data.lambdaRadius
  refine ⟨delta, hdelta, hsmall, data, epsilon, hepsilon, hepsilonBound,
    lambdaBound, lt_min hbound data.lambdaRadius_pos, min_le_right _ _, ?_⟩
  intro lam hlam hlambdaBound
  have h := hinterval ⟨hlam, hlambdaBound.trans_le (min_le_left _ _)⟩
  simpa only [data, actualPoint_ofFamilies_true, actualPoint_ofFamilies_false,
    Gram5IndependentBinding.implementation_f_eq_selected, Set.mem_setOf_eq] using h

end PBCounterexample.Gram5IndependentIntermediateBinding
