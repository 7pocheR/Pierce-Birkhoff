import PBCounterexample.SignTopology
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-! Nonvanishing from a polynomial approximation with a higher-order error. -/

namespace PBCounterexample

open Filter Asymptotics Polynomial
open scoped Topology

/-- A nonzero coefficient below the error order forces the actual function
to be nonzero at all sufficiently small positive arguments. The polynomial
may have further coefficients above the stated error order. -/
theorem eventually_ne_zero_of_polynomial_approximation
    {g : ℝ → ℝ} {p : Polynomial ℝ} {N : ℕ}
    (herr : (fun t => g t - p.eval t) =O[𝓝 (0 : ℝ)] (fun t => t ^ N))
    (hcoeff : ∃ k < N, p.coeff k ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≠ 0 := by
  obtain ⟨k, hk, hpk⟩ := hcoeff
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hpk
  let m := p.natTrailingDegree
  have hm : m < N := (p.natTrailingDegree_le_of_ne_zero hpk).trans_lt hk
  obtain ⟨q, hpq⟩ : ∃ q : Polynomial ℝ, p = X ^ m * q :=
    X_pow_dvd_iff.mpr (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
  have hq : q.eval 0 ≠ 0 := by
    have hc := (coeff_natTrailingDegree_ne_zero.mpr hp)
    have hrel : p.coeff m = q.coeff 0 := by
      rw [hpq]
      simpa using coeff_X_pow_mul q m 0
    rw [← coeff_zero_eq_eval_zero, ← hrel]
    exact hc
  have ho : (fun t => g t - p.eval t) =o[𝓝 (0 : ℝ)] (fun t => t ^ m) :=
    herr.trans_isLittleO (isLittleO_pow_pow hm)
  have hlim : Tendsto (fun t => g t / t ^ m) (𝓝[>] (0 : ℝ)) (𝓝 (q.eval 0)) := by
    have he : Tendsto (fun t => (g t - p.eval t) / t ^ m)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      ho.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
    have hqc : Tendsto (fun t : ℝ => q.eval t) (𝓝[>] 0) (𝓝 (q.eval 0)) :=
      q.continuous.tendsto 0 |>.mono_left nhdsWithin_le_nhds
    have hs := he.add hqc
    simp only [zero_add] at hs
    apply hs.congr'
    filter_upwards [show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin] with t ht
    have ht0 : t ^ m ≠ 0 := pow_ne_zero _ ht.ne'
    simp only [hpq, eval_mul, eval_pow, eval_X]
    field_simp
    ring
  have hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t / t ^ m ≠ 0 :=
    hlim.eventually (isOpen_ne.mem_nhds hq)
  filter_upwards [hn] with t ht
  intro hz
  exact ht (by simp [hz])

/-- Finitely many independently certified nonzero polynomial approximations
give one positive parameter satisfying all nonvanishing conditions. -/
theorem exists_positive_time_nonzero_of_polynomial_approximations
    {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ)
    (p : ι → Polynomial ℝ) (N : ℕ)
    (herr : ∀ i ∈ s, (fun t => g i t - (p i).eval t) =O[𝓝 (0 : ℝ)] (fun t => t ^ N))
    (hcoeff : ∀ i ∈ s, ∃ k < N, (p i).coeff k ≠ 0)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧ ∀ i ∈ s, g i t ≠ 0 := by
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ s, g i t ≠ 0 :=
    (Filter.eventually_all_finset s).mpr fun i hi =>
      eventually_ne_zero_of_polynomial_approximation (herr i hi) (hcoeff i hi)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ U := nhdsWithin_le_nhds hU
  obtain ⟨t, htU, htp, hte⟩ := (hu.and (hpos.and he)).exists
  exact ⟨t, htU, htp, hte⟩

/-- Eventual vanishing of an approximated function forces every certified
coefficient below the error order to vanish. -/
theorem coefficients_eq_zero_of_eventually_zero_approximation
    {g : ℝ → ℝ} {p : Polynomial ℝ} {N : ℕ}
    (herr : (fun t => g t - p.eval t) =O[𝓝 (0 : ℝ)] (fun t => t ^ N))
    (hzero : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t = 0) :
    ∀ k < N, p.coeff k = 0 := by
  intro k hk
  by_contra hpk
  have hne := eventually_ne_zero_of_polynomial_approximation herr ⟨k, hk, hpk⟩
  obtain ⟨t, ht, hnt⟩ := (hzero.and hne).exists
  exact hnt ht

/-- The common-value alternative for a finite family of polynomial tests
needs to hold only eventually along the two paths. -/
theorem exists_positive_time_same_polynomial_signs_of_eventual
    {σ : Type*} (s : Finset (MvPolynomial σ ℝ))
    (a b : ℝ → (σ → ℝ)) (o : σ → ℝ)
    (ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 o))
    (hb : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 o))
    (hs : ∀ p ∈ s,
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MvPolynomial.eval (a t) p = MvPolynomial.eval (b t) p) ∨
      MvPolynomial.eval o p ≠ 0)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧ ∀ p ∈ s,
      Real.sign (MvPolynomial.eval (a t) p) = Real.sign (MvPolynomial.eval (b t) p) := by
  have heach : ∀ p ∈ s, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Real.sign (MvPolynomial.eval (a t) p) = Real.sign (MvPolynomial.eval (b t) p) := by
    intro p hp
    rcases hs p hp with heq | hne
    · exact heq.mono fun _ ht => congrArg Real.sign ht
    · have hap := eventually_real_sign_eq_of_tendsto
        ((MvPolynomial.continuous_eval p).tendsto o |>.comp ha) hne
      have hbp := eventually_real_sign_eq_of_tendsto
        ((MvPolynomial.continuous_eval p).tendsto o |>.comp hb) hne
      filter_upwards [hap, hbp] with t hta htb
      exact hta.trans htb.symm
  have hall := (Filter.eventually_all_finset s).mpr heach
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ U := nhdsWithin_le_nhds hU
  exact (hu.and (hpos.and hall)).exists

end PBCounterexample
