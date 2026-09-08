import PBCounterexample.Gram6Kernel
import PBCounterexample.Gram6Variations
import PBCounterexample.RadialTests

/-! Finite choices of the curve parameter and the signed normal displacement. -/

noncomputable section

namespace PBCounterexample.Gram6

open Matrix MvPolynomial Filter
open scoped BigOperators Topology

private def quadraticPolarCoefficients (c : Fin 21 → ℝ) (v w : Coord) : ℝ :=
  ∑ i, c i * (v (quadraticPairs i).1 * w (quadraticPairs i).2 +
    w (quadraticPairs i).1 * v (quadraticPairs i).2)

/-- The first variation of the homogeneous degree-two part of a polynomial. -/
def quadraticVariation (p : MvPolynomial (Fin 6) ℝ) (v w : Coord) : ℝ :=
  quadraticPolarCoefficients (fun i => p.coeff (quadraticExponent i)) v w

private theorem homogeneous_two_eq_canonical (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) :
    p = quadraticPolynomial (fun i => p.coeff (quadraticExponent i)) :=
  LowDegreeCoordinates.homogeneous_two_eq_sum quadraticPairs
    quadraticExponent_injective quadraticPairs_complete p hp

private theorem eval_homogeneous_two (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) (v : Coord) :
    eval v p = ∑ i, p.coeff (quadraticExponent i) *
      (v (quadraticPairs i).1 * v (quadraticPairs i).2) := by
  have h := congrArg (eval v) (homogeneous_two_eq_canonical p hp)
  simpa only [quadraticPolynomial, map_sum, map_mul, eval_C, eval_X] using h

theorem quadraticVariation_smul_left (p : MvPolynomial (Fin 6) ℝ)
    (v w : Coord) (a : ℝ) : quadraticVariation p (a • v) w = a * quadraticVariation p v w := by
  simp only [quadraticVariation, quadraticPolarCoefficients, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticVariation_smul_right (p : MvPolynomial (Fin 6) ℝ)
    (v w : Coord) (a : ℝ) : quadraticVariation p v (a • w) = a * quadraticVariation p v w := by
  simp only [quadraticVariation, quadraticPolarCoefficients, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticVariation_add_right (p : MvPolynomial (Fin 6) ℝ)
    (v w z : Coord) :
    quadraticVariation p v (w + z) = quadraticVariation p v w + quadraticVariation p v z := by
  simp only [quadraticVariation, quadraticPolarCoefficients, Pi.add_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticVariation_self (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) (v : Coord) :
    quadraticVariation p v v = 2 * eval v p := by
  rw [eval_homogeneous_two p hp v]
  simp only [quadraticVariation, quadraticPolarCoefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_add_smul_of_homogeneous_two (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) (v w : Coord) (a : ℝ) :
    eval (v + a • w) p = eval v p + a * quadraticVariation p v w + a^2 * eval w p := by
  simp only [eval_homogeneous_two p hp, quadraticVariation, quadraticPolarCoefficients,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem hasDerivAt_quadraticPolynomial (c : Fin 21 → ℝ)
    {v : ℝ → Coord} {v' : Coord} {t : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => eval (v s) (quadraticPolynomial c))
      (quadraticPolarCoefficients c (v t) v') t := by
  have hraw : HasDerivAt
      (fun s => ∑ i, c i * (v s (quadraticPairs i).1 * v s (quadraticPairs i).2))
      (∑ i, c i * (v' (quadraticPairs i).1 * v t (quadraticPairs i).2 +
        v t (quadraticPairs i).1 * v' (quadraticPairs i).2)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hasDerivAt_pi.mp hv (quadraticPairs i).1).mul
      (hasDerivAt_pi.mp hv (quadraticPairs i).2)).const_mul (c i)
  have hd : (∑ i, c i * (v' (quadraticPairs i).1 * v t (quadraticPairs i).2 +
      v t (quadraticPairs i).1 * v' (quadraticPairs i).2)) =
      quadraticPolarCoefficients c (v t) v' := by
    unfold quadraticPolarCoefficients
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply (hraw.congr_deriv hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s => by
    simp only [quadraticPolynomial, map_sum, map_mul, eval_C, eval_X]

theorem hasDerivAt_eval_homogeneous_two (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) {v : ℝ → Coord} {v' : Coord} {t : ℝ}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => eval (v s) p) (quadraticVariation p (v t) v') t := by
  have hrep := homogeneous_two_eq_canonical p hp
  simpa only [← hrep, quadraticVariation] using
    hasDerivAt_quadraticPolynomial (fun i => p.coeff (quadraticExponent i)) hv

private theorem hasDerivAt_quadraticPolarCoefficients (c : Fin 21 → ℝ)
    {v w : ℝ → Coord} {v' w' : Coord} {t : ℝ}
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => quadraticPolarCoefficients c (v s) (w s))
      (quadraticPolarCoefficients c v' (w t) +
        quadraticPolarCoefficients c (v t) w') t := by
  have hraw : HasDerivAt
      (fun s => ∑ i, c i * (v s (quadraticPairs i).1 * w s (quadraticPairs i).2 +
        w s (quadraticPairs i).1 * v s (quadraticPairs i).2))
      (∑ i, c i * ((v' (quadraticPairs i).1 * w t (quadraticPairs i).2 +
        v t (quadraticPairs i).1 * w' (quadraticPairs i).2) +
        (w' (quadraticPairs i).1 * v t (quadraticPairs i).2 +
          w t (quadraticPairs i).1 * v' (quadraticPairs i).2))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (((hasDerivAt_pi.mp hv (quadraticPairs i).1).mul
      (hasDerivAt_pi.mp hw (quadraticPairs i).2)).add
      ((hasDerivAt_pi.mp hw (quadraticPairs i).1).mul
        (hasDerivAt_pi.mp hv (quadraticPairs i).2))).const_mul (c i)
  apply hraw.congr_deriv
  simp only [quadraticPolarCoefficients, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_quadraticVariation (p : MvPolynomial (Fin 6) ℝ)
    {v w : ℝ → Coord} {v' w' : Coord} {t : ℝ}
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => quadraticVariation p (v s) (w s))
      (quadraticVariation p v' (w t) + quadraticVariation p (v t) w') t :=
  hasDerivAt_quadraticPolarCoefficients _ hv hw

theorem hasDerivAt_curveTangent_acceleration (t : ℝ) :
    HasDerivAt curveTangent (curveAcceleration t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun s : ℝ => 4*s^3 - 12*s) (12*t^2 - 12) t
    convert! (((hasDerivAt_id t).pow 3).const_mul 4).sub
      ((hasDerivAt_id t).const_mul 12) using 1 <;> norm_num <;> ring
  · change HasDerivAt (fun s : ℝ => 12*s^2 - 4) (24*t) t
    convert! (((hasDerivAt_id t).pow 2).const_mul 12).sub_const 4 using 1 <;>
      norm_num <;> ring
  · change HasDerivAt (fun s : ℝ => 4*s^3 + 4*s) (12*t^2 + 4) t
    convert! (((hasDerivAt_id t).pow 3).const_mul 4).add
      ((hasDerivAt_id t).const_mul 4) using 1 <;> norm_num <;> ring
  · change HasDerivAt (fun s : ℝ => 8*s^3) (24*t^2) t
    convert! ((hasDerivAt_id t).pow 3).const_mul 8 using 1 <;> norm_num <;> ring
  · change HasDerivAt (fun s : ℝ => 12*s^2 + 4) (24*t) t
    convert! (((hasDerivAt_id t).pow 2).const_mul 12).add_const 4 using 1 <;>
      norm_num <;> ring
  · change HasDerivAt (fun s : ℝ => 10*s^4 + 12*s^2 + 2) (40*t^3 + 24*t) t
    convert! ((((hasDerivAt_id t).pow 4).const_mul 10).add
      (((hasDerivAt_id t).pow 2).const_mul 12)).add_const 2 using 1 <;>
        norm_num <;> ring

theorem quadraticVariation_curve_acceleration (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) (hc : ∀ s : ℝ, eval (curve s) p = 0) (t : ℝ) :
    quadraticVariation p (curve t) (curveAcceleration t) = -2 * eval (curveTangent t) p := by
  have hfirst (s : ℝ) : quadraticVariation p (curve s) (curveTangent s) = 0 := by
    have hzero : HasDerivAt (fun x : ℝ => eval (curve x) p) 0 s :=
      (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall hc)
    exact (hasDerivAt_eval_homogeneous_two p hp (hasDerivAt_curve s)).unique hzero
  have hzero : HasDerivAt (fun s : ℝ =>
      quadraticVariation p (curve s) (curveTangent s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall hfirst)
  have hsecond := (hasDerivAt_quadraticVariation p (hasDerivAt_curve t)
    (hasDerivAt_curveTangent_acceleration t)).unique hzero
  rw [quadraticVariation_self p hp] at hsecond
  linarith only [hsecond]

/-- The normal derivative identity holds for every real homogeneous quadratic in the curve ideal. -/
theorem quadraticVariation_base_normal (p : MvPolynomial (Fin 6) ℝ)
    (hp : p.IsHomogeneous 2) (hc : ∀ s : ℝ, eval (curve s) p = 0)
    (t ρ : ℝ) (hρ : ρ ≠ 0) :
    quadraticVariation p (ρ • curve t) (normalDirection t ρ) =
      eval (curveTangent t) p / tangentScale t := by
  have hd : tangentScale t ≠ 0 := ne_of_gt (tangentScale_pos t)
  rw [normalDirection, quadraticVariation_smul_left, quadraticVariation_smul_right,
    quadraticVariation_curve_acceleration p hp hc]
  field_simp [hρ, hd]
  <;> ring

def alongCurvePolynomial (p : MvPolynomial (Fin 6) ℝ) : Polynomial ℝ :=
  eval₂Hom Polynomial.C (fun i : Fin 6 => Polynomial.X^i.val) (pullToMonomial p)

def alongTangentPolynomial (p : MvPolynomial (Fin 6) ℝ) : Polynomial ℝ :=
  eval₂Hom Polynomial.C
    (fun i : Fin 6 => Polynomial.C (i.val : ℝ) * Polynomial.X^(i.val - 1))
    (pullToMonomial p)

theorem eval_alongCurvePolynomial (p : MvPolynomial (Fin 6) ℝ) (t : ℝ) :
    (alongCurvePolynomial p).eval t = eval (curve t) p := by
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext a
    simp
  change (Polynomial.evalRingHom t)
    (eval₂Hom Polynomial.C (fun i : Fin 6 => Polynomial.X^i.val) (pullToMonomial p)) = _
  rw [MvPolynomial.map_eval₂Hom, hC]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X]
  change eval (monomialCurve t) (pullToMonomial p) = _
  rw [eval_pullToMonomial, fromMonomial_monomialCurve]

theorem eval_alongTangentPolynomial (p : MvPolynomial (Fin 6) ℝ) (t : ℝ) :
    (alongTangentPolynomial p).eval t = eval (curveTangent t) p := by
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext a
    simp
  change (Polynomial.evalRingHom t) (eval₂Hom Polynomial.C
    (fun i : Fin 6 => Polynomial.C (i.val : ℝ) * Polynomial.X^(i.val - 1))
    (pullToMonomial p)) = _
  rw [MvPolynomial.map_eval₂Hom, hC]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  change eval (monomialTangent t) (pullToMonomial p) = _
  rw [eval_pullToMonomial, fromMonomial_monomialTangent]

theorem alongCurvePolynomial_eq_zero_iff (p : MvPolynomial (Fin 6) ℝ) :
    alongCurvePolynomial p = 0 ↔ ∀ t : ℝ, eval (curve t) p = 0 := by
  constructor
  · intro h t
    rw [← eval_alongCurvePolynomial, h, Polynomial.eval_zero]
  · intro h
    apply Polynomial.funext
    intro t
    simpa only [eval_alongCurvePolynomial, Polynomial.eval_zero] using h t

theorem alongTangentPolynomial_eq_zero_iff (p : MvPolynomial (Fin 6) ℝ) :
    alongTangentPolynomial p = 0 ↔ ∀ t : ℝ, eval (curveTangent t) p = 0 := by
  constructor
  · intro h t
    rw [← eval_alongTangentPolynomial, h, Polynomial.eval_zero]
  · intro h
    apply Polynomial.funext
    intro t
    simpa only [eval_alongTangentPolynomial, Polynomial.eval_zero] using h t

private theorem eventually_polynomial_eval_ne_zero (p : Polynomial ℝ) :
    ∀ᶠ t in Filter.cofinite, p ≠ 0 → p.eval t ≠ 0 := by
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun _ h => (h hp).elim
  · exact (Polynomial.eventually_eval_ne_zero_cofinite hp).mono fun _ h _ => h

/-- One real parameter avoids every nonzero curve and tangent polynomial in a finite family. -/
theorem exists_finite_curve_parameter (S : Finset (MvPolynomial (Fin 6) ℝ)) :
    ∃ t : ℝ, ∀ p ∈ S,
      ((∃ s : ℝ, eval (curve s) p ≠ 0) → eval (curve t) p ≠ 0) ∧
      ((∃ s : ℝ, eval (curveTangent s) p ≠ 0) → eval (curveTangent t) p ≠ 0) := by
  classical
  have hev : ∀ᶠ t in Filter.cofinite, ∀ p ∈ S,
      (alongCurvePolynomial p ≠ 0 → (alongCurvePolynomial p).eval t ≠ 0) ∧
      (alongTangentPolynomial p ≠ 0 → (alongTangentPolynomial p).eval t ≠ 0) := by
    apply (Filter.eventually_all_finset S).mpr
    intro p _
    exact (eventually_polynomial_eval_ne_zero (alongCurvePolynomial p)).and
      (eventually_polynomial_eval_ne_zero (alongTangentPolynomial p))
  obtain ⟨t, ht⟩ := hev.exists
  refine ⟨t, ?_⟩
  intro p hp
  constructor
  · rintro ⟨s, hs⟩
    have hne : alongCurvePolynomial p ≠ 0 := fun h =>
      hs ((alongCurvePolynomial_eq_zero_iff p).mp h s)
    simpa only [eval_alongCurvePolynomial] using (ht p hp).1 hne
  · rintro ⟨s, hs⟩
    have hne : alongTangentPolynomial p ≠ 0 := fun h =>
      hs ((alongTangentPolynomial_eq_zero_iff p).mp h s)
    simpa only [eval_alongTangentPolynomial] using (ht p hp).2 hne

private theorem exists_positive_finite_variation_bound
    {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ S, a i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ * |b i| < |a i| / 2 := by
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ i ∈ S, δ * |b i| < |a i| / 2 := by
    apply (Filter.eventually_all_finset S).mpr
    intro i hi
    apply (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const
    change (0 : ℝ) * |b i| < |a i| / 2
    simpa only [zero_mul] using half_pos (abs_pos.mpr (ha i hi))
  obtain ⟨η, hη, hbound⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η / 2, half_pos hη, hbound ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hη)]
  exact half_lt_self hη

/-- All normal first variations that must be nonzero admit one common positive displacement. -/
theorem exists_finite_normal_parameters (S : Finset (MvPolynomial (Fin 6) ℝ)) :
    ∃ t δ : ℝ, 0 < δ ∧
      (∀ p ∈ S, (∃ s : ℝ, eval (curve s) p ≠ 0) → eval (curve t) p ≠ 0) ∧
      ∀ p ∈ S, p.IsHomogeneous 2 → (∀ s : ℝ, eval (curve s) p = 0) →
        (∃ s : ℝ, eval (curveTangent s) p ≠ 0) →
        quadraticVariation p (curve t) (normalDirection t 1) ≠ 0 ∧
        δ * |quadraticVariation p (curve t) (kernelDirection t)| <
          |quadraticVariation p (curve t) (normalDirection t 1)| / 2 := by
  classical
  obtain ⟨t, ht⟩ := exists_finite_curve_parameter S
  let T := S.filter (fun p => p.IsHomogeneous 2 ∧
    (∀ s : ℝ, eval (curve s) p = 0) ∧ (∃ s : ℝ, eval (curveTangent s) p ≠ 0))
  let a := fun p : MvPolynomial (Fin 6) ℝ =>
    quadraticVariation p (curve t) (normalDirection t 1)
  let b := fun p : MvPolynomial (Fin 6) ℝ =>
    quadraticVariation p (curve t) (kernelDirection t)
  have ha : ∀ p ∈ T, a p ≠ 0 := by
    intro p hp
    obtain ⟨hpS, hp2, hpc, hpt⟩ := Finset.mem_filter.mp hp
    have hid := quadraticVariation_base_normal p hp2 hpc t 1 (by norm_num)
    simp only [one_smul] at hid
    change quadraticVariation p (curve t) (normalDirection t 1) ≠ 0
    rw [hid]
    exact div_ne_zero ((ht p hpS).2 hpt) (ne_of_gt (tangentScale_pos t))
  obtain ⟨δ, hδ, hδall⟩ := exists_positive_finite_variation_bound T a b ha
  refine ⟨t, δ, hδ, fun p hp => (ht p hp).1, ?_⟩
  intro p hpS hp2 hpc hpt
  have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hpS, hp2, hpc, hpt⟩
  exact ⟨ha p hpT, hδall p hpT⟩

/-- Parameter selection for precisely the finite homogeneous test family supplied by `RadialTests`.
Every polynomial is either zero, nonzero at the base, has a controlled nonzero normal derivative,
or is an exact real linear combination of the three joint-kernel Gram polynomials. -/
theorem exists_finite_homogeneous_parameters (S : Finset (MvPolynomial (Fin 6) ℝ))
    (hS : ∀ p ∈ S, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2) :
    ∃ t δ : ℝ, 0 < δ ∧ ∀ p ∈ S,
      p = 0 ∨ eval (curve t) p ≠ 0 ∨
      (p.IsHomogeneous 2 ∧ (∀ s : ℝ, eval (curve s) p = 0) ∧
        ((quadraticVariation p (curve t) (normalDirection t 1) ≠ 0 ∧
          δ * |quadraticVariation p (curve t) (kernelDirection t)| <
            |quadraticVariation p (curve t) (normalDirection t 1)| / 2) ∨
          ∃ a b c : ℝ, p = C a * gramPolynomial 0 0 + C b * gramPolynomial 0 1 +
            C c * (gramPolynomial 1 2 + gramPolynomial 2 2))) := by
  classical
  obtain ⟨t, δ, hδ, ht, hn⟩ := exists_finite_normal_parameters S
  refine ⟨t, δ, hδ, ?_⟩
  intro p hp
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  by_cases hpc : ∃ s : ℝ, eval (curve s) p ≠ 0
  · exact Or.inr (Or.inl (ht p hp hpc))
  have hc : ∀ s : ℝ, eval (curve s) p = 0 := by
    intro s
    by_contra hs
    exact hpc ⟨s, hs⟩
  have hp2 : p.IsHomogeneous 2 := by
    rcases hS p hp with hp1 | hp2
    · exact (hp0 (homogeneous_linear_original_kernel p hp1 hc)).elim
    · exact hp2
  refine Or.inr (Or.inr ⟨hp2, hc, ?_⟩)
  by_cases hpt : ∃ s : ℝ, eval (curveTangent s) p ≠ 0
  · exact Or.inl (hn p hp hp2 hc hpt)
  · apply Or.inr
    apply homogeneous_quadratic_original_kernel p hp2 hc
    intro s
    by_contra hs
    exact hpt ⟨s, hs⟩

end PBCounterexample.Gram6

end
