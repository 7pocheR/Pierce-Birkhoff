import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Linear and symmetric bilinear representations of polynomials of degree at most two. -/

namespace PBCounterexample.QuadraticDecomposition

open scoped BigOperators

noncomputable section

variable {σ : Type*}

theorem exponent_degree_le_two (d : σ →₀ ℕ) (hd : d.degree ≤ 2) :
    d = 0 ∨ (∃ i, d = Finsupp.single i 1) ∨
      ∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  by_cases hzero : d.degree = 0
  · exact Or.inl ((Finsupp.degree_eq_zero_iff d).1 hzero)
  by_cases hone : d.degree = 1
  · right; left
    have hr : d ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hone
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi.symm⟩
  have htwo : d.degree = 2 := by omega
  obtain ⟨a, had, ha⟩ := Finsupp.exists_le_degree_eq d 1 (by omega)
  obtain ⟨b, hab⟩ := le_iff_exists_add.mp had
  have hb : b.degree = 1 := by
    have hdeg := congrArg Finsupp.degree hab
    simp only [map_add, ha, htwo] at hdeg
    omega
  have hra : a ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact ha
  have hrb : b ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hb
  obtain ⟨i, rfl⟩ := hra
  obtain ⟨j, rfl⟩ := hrb
  exact Or.inr (Or.inr ⟨i, j, hab⟩)

def coordinateBilinear (i j : σ) : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => (x i * y j + x j * y i) / 2
      map_add' := by intros; simp only [Pi.add_apply]; ring
      map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by intros; ext y; simp only [Pi.add_apply, LinearMap.add_apply,
    LinearMap.coe_mk, AddHom.coe_mk]; ring
  map_smul' := by intros; ext y; simp only [Pi.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]; ring

theorem coordinateBilinear_symmetric (i j : σ) (x y : σ → ℝ) :
    coordinateBilinear i j x y = coordinateBilinear i j y x := by
  change (x i * y j + x j * y i) / 2 = (y i * x j + y j * x i) / 2
  ring

theorem coordinateBilinear_diagonal (i j : σ) (x : σ → ℝ) :
    coordinateBilinear i j x x = x i * x j := by
  change (x i * x j + x j * x i) / 2 = x i * x j
  ring

theorem monomial_representation (d : σ →₀ ℕ) (a : ℝ) (hd : d.degree ≤ 2) :
    ∃ (c : ℝ) (L : (σ → ℝ) →ₗ[ℝ] ℝ)
      (Q : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) →ₗ[ℝ] ℝ),
      (∀ x y, Q x y = Q y x) ∧
      ∀ z, MvPolynomial.eval z (MvPolynomial.monomial d a) = c + L z + Q z z := by
  rcases exponent_degree_le_two d hd with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · refine ⟨a, 0, 0, by simp, ?_⟩
    intro z
    simp [← MvPolynomial.C_apply]
  · refine ⟨0, a • LinearMap.proj i, 0, by simp, ?_⟩
    intro z
    simp [← MvPolynomial.C_mul_X_eq_monomial]
  · refine ⟨0, 0, a • coordinateBilinear i j, ?_, ?_⟩
    · intro x y
      simp only [LinearMap.smul_apply, smul_eq_mul, coordinateBilinear_symmetric i j x y]
    · intro z
      rw [MvPolynomial.monomial_add_single]
      simp [← MvPolynomial.C_mul_X_eq_monomial, coordinateBilinear_diagonal, mul_assoc]

theorem polynomial_representation (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 2) :
    ∃ (c : ℝ) (L : (σ → ℝ) →ₗ[ℝ] ℝ)
      (Q : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) →ₗ[ℝ] ℝ),
      (∀ x y, Q x y = Q y x) ∧
      ∀ z, MvPolynomial.eval z p = c + L z + Q z z := by
  classical
  have hmon : ∀ d : σ →₀ ℕ,
      ∃ (c : ℝ) (L : (σ → ℝ) →ₗ[ℝ] ℝ)
        (Q : (σ → ℝ) →ₗ[ℝ] (σ → ℝ) →ₗ[ℝ] ℝ),
        (∀ x y, Q x y = Q y x) ∧
        (d ∈ p.support → ∀ z,
          MvPolynomial.eval z (MvPolynomial.monomial d (p.coeff d)) = c + L z + Q z z) := by
    intro d
    by_cases hd : d ∈ p.support
    · have hdegree : d.degree ≤ 2 := (MvPolynomial.le_totalDegree hd).trans hp
      obtain ⟨c, L, Q, hQ, hrep⟩ := monomial_representation d (p.coeff d) hdegree
      exact ⟨c, L, Q, hQ, fun _ => hrep⟩
    · exact ⟨0, 0, 0, by simp, fun h => (hd h).elim⟩
  choose c L Q hsym hrep using hmon
  refine ⟨∑ d ∈ p.support, c d, ∑ d ∈ p.support, L d,
    ∑ d ∈ p.support, Q d, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun d _ => hsym d x y)
  · intro z
    calc
      MvPolynomial.eval z p =
          ∑ d ∈ p.support, MvPolynomial.eval z (MvPolynomial.monomial d (p.coeff d)) := by
        rw [← MvPolynomial.eval_sum, MvPolynomial.support_sum_monomial_coeff]
      _ = ∑ d ∈ p.support, (c d + L d z + Q d z z) :=
        Finset.sum_congr rfl (fun d hd => hrep d hd z)
      _ = _ := by simp [Finset.sum_add_distrib]

end

end PBCounterexample.QuadraticDecomposition
