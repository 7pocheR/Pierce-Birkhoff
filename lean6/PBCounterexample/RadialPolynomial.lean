import PBCounterexample.RadialScalar
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.Ring

namespace PBCounterexample.Radial

open Filter Topology
open scoped BigOperators

noncomputable section

variable {σ : Type*}

theorem eval_homogeneous_scale {p : MvPolynomial σ ℝ} {n : ℕ}
    (hp : p.IsHomogeneous n) (z : σ → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun i => t * z i) p = t ^ n * MvPolynomial.eval z p := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d.support.sum d = n := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using
      hp (MvPolynomial.mem_support_iff.1 hd)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd']
  ring

theorem sum_homogeneousComponent_extended (p : MvPolynomial σ ℝ) :
    (∑ n ∈ Finset.range (p.totalDegree + 3), MvPolynomial.homogeneousComponent n p) = p := by
  calc
    _ = ∑ n ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent n p := by
      apply (Finset.sum_subset (by intro n hn; simp only [Finset.mem_range] at *; omega) ?_).symm
      intro n hn hnot
      apply MvPolynomial.homogeneousComponent_eq_zero
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    _ = p := MvPolynomial.sum_homogeneousComponent p

def radialPolynomial (p : MvPolynomial σ ℝ) (z : σ → ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (p.totalDegree + 3),
    Polynomial.C (MvPolynomial.eval z (MvPolynomial.homogeneousComponent n p)) * Polynomial.X ^ n

theorem radialPolynomial_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) (t : ℝ) :
    (radialPolynomial p z).eval t = MvPolynomial.eval (fun i => t * z i) p := by
  conv_rhs => rw [← sum_homogeneousComponent_extended p]
  simp only [MvPolynomial.eval_sum]
  simp only [radialPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro n hn
  rw [eval_homogeneous_scale (MvPolynomial.homogeneousComponent_isHomogeneous n p)]
  ring

theorem radialPolynomial_coeff (p : MvPolynomial σ ℝ) (z : σ → ℝ) (n : ℕ)
    (hn : n < p.totalDegree + 3) :
    (radialPolynomial p z).coeff n =
      MvPolynomial.eval z (MvPolynomial.homogeneousComponent n p) := by
  classical
  simp [radialPolynomial, Finset.mem_range, hn]

theorem polynomial_eval_expand (p : Polynomial ℝ) (t : ℝ) :
    p.eval t = p.coeff 0 + t * (p.coeff 1 + t * p.divX.divX.eval t) := by
  have h₀ := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add p)
  have h₁ := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add p.divX)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.coeff_divX, zero_add] at h₀ h₁
  rw [← h₀, ← h₁]
  ring

def limitingValue (a b c : ℝ) : ℝ :=
  if a < 0 then -1 else if 0 < a then 1 else
    if b < 0 then -1 else if 0 < b then 1 else clip c

theorem sign_limitingValue (a b c : ℝ) :
    Real.sign (limitingValue a b c) =
      if a = 0 then (if b = 0 then Real.sign c else Real.sign b) else Real.sign a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [limitingValue, ha, ne_of_lt ha, Real.sign_of_neg ha,
      Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num)]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · simp [limitingValue, hb, ne_of_lt hb, Real.sign_of_neg hb,
        Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num)]
    · simp [limitingValue, sign_clip]
    · simp [limitingValue, hb, ne_of_gt hb, not_lt_of_ge hb.le, Real.sign_of_pos hb]
  · simp [limitingValue, ha, ne_of_gt ha, not_lt_of_ge ha.le, Real.sign_of_pos ha]

theorem sign_limitingValue_congr (a b c b' c' : ℝ)
    (hb : Real.sign b = Real.sign b') (hc : Real.sign c = Real.sign c') :
    Real.sign (limitingValue a b c) = Real.sign (limitingValue a b' c') := by
  have hb0 : b = 0 ↔ b' = 0 := by
    calc
      b = 0 ↔ Real.sign b = 0 := Real.sign_eq_zero_iff.symm
      _ ↔ Real.sign b' = 0 := by rw [hb]
      _ ↔ b' = 0 := Real.sign_eq_zero_iff
  simp only [sign_limitingValue, hb0, hb, hc]

theorem tendsto_clip_polynomial (p : Polynomial ℝ) :
    Tendsto (fun t : ℝ => clip (p.eval t / t ^ 2)) (𝓝[>] 0)
      (𝓝 (limitingValue (p.coeff 0) (p.coeff 1) (p.coeff 2))) := by
  have hr : ContinuousAt (fun t : ℝ => p.divX.divX.eval t) 0 := by fun_prop
  simp only [polynomial_eval_expand p]
  rcases lt_trichotomy (p.coeff 0) 0 with ha | ha | ha
  · simpa [limitingValue, ha] using
      tendsto_clip_quadratic_of_constant_neg (p.coeff 0) (p.coeff 1) _ hr ha
  · rcases lt_trichotomy (p.coeff 1) 0 with hb | hb | hb
    · simpa [limitingValue, ha, hb] using
        tendsto_clip_quadratic_of_linear_neg (p.coeff 1) _ hr hb
    · simpa [limitingValue, ha, hb, ← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_divX] using
        tendsto_clip_quadratic_of_low_coefficients_zero _ hr
    · simpa [limitingValue, ha, hb, not_lt_of_ge hb.le] using
        tendsto_clip_quadratic_of_linear_pos (p.coeff 1) _ hr hb
  · simpa [limitingValue, ha, not_lt_of_ge ha.le] using
      tendsto_clip_quadratic_of_constant_pos (p.coeff 0) (p.coeff 1) _ hr ha

def leafLimit (p : MvPolynomial σ ℝ) (z : σ → ℝ) : ℝ :=
  limitingValue (p.coeff 0)
    (MvPolynomial.eval z (MvPolynomial.homogeneousComponent 1 p))
    (MvPolynomial.eval z (MvPolynomial.homogeneousComponent 2 p))

theorem tendsto_clip_mvPolynomial (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    Tendsto (fun t : ℝ => clip (MvPolynomial.eval (fun i => t * z i) p / t ^ 2))
      (𝓝[>] 0) (𝓝 (leafLimit p z)) := by
  have h₀ := radialPolynomial_coeff p z 0 (by omega)
  have h₁ := radialPolynomial_coeff p z 1 (by omega)
  have h₂ := radialPolynomial_coeff p z 2 (by omega)
  simpa [radialPolynomial_eval, h₀, h₁, h₂, leafLimit] using
    tendsto_clip_polynomial (radialPolynomial p z)

end

end PBCounterexample.Radial
