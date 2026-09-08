import Mathlib

/-!
# The quadratic form of a symmetric matrix with zero row sums
-/

namespace PBCounterexample.Laplacian

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem sum_squared_differences (L : Matrix n n ℝ)
    (hsymm : L.IsSymm) (hrow : ∀ i, ∑ j, L i j = 0) (z : n → ℝ) :
    (∑ i, ∑ j, (-L i j) * (z i - z j) ^ 2) = 2 * (z ⬝ᵥ (L *ᵥ z)) := by
  have hcol (j : n) : ∑ i, L i j = 0 := by
    simpa only [hsymm.apply] using hrow j
  have hleft : (∑ i, ∑ j, L i j * z i ^ 2) = 0 := by
    simp_rw [← Finset.sum_mul, hrow, zero_mul]
    simp
  have hright : (∑ i, ∑ j, L i j * z j ^ 2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, zero_mul]
    simp
  calc
    (∑ i, ∑ j, (-L i j) * (z i - z j) ^ 2) =
        (∑ i, ∑ j, ((2 * (z i * (L i j * z j)) - L i j * z i ^ 2) -
          L i j * z j ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (z ⬝ᵥ (L *ᵥ z)) := by
      simp_rw [Finset.sum_sub_distrib]
      rw [hleft, hright, sub_zero, sub_zero]
      simp only [dotProduct, mulVec, ← Finset.mul_sum]

theorem constant_of_quadratic_zero (L : Matrix n n ℝ)
    (hsymm : L.IsSymm) (hrow : ∀ i, ∑ j, L i j = 0)
    (hoff : ∀ i j, i ≠ j → L i j < 0) (z : n → ℝ)
    (hz : z ⬝ᵥ (L *ᵥ z) = 0) : ∀ i j, z i = z j := by
  have hnonneg (i j : n) : 0 ≤ (-L i j) * (z i - z j) ^ 2 := by
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonneg (le_of_lt (neg_pos.mpr (hoff i j hij))) (sq_nonneg _)
  have hsum : (∑ i, ∑ j, (-L i j) * (z i - z j) ^ 2) = 0 := by
    rw [sum_squared_differences L hsymm hrow z, hz, mul_zero]
  have hrows : ∀ i, (∑ j, (-L i j) * (z i - z j) ^ 2) = 0 := by
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Finset.sum_nonneg (fun j _ => hnonneg k j))).mp hsum i (Finset.mem_univ i)
  intro i j
  by_cases hij : i = j
  · exact congrArg z hij
  have hterm : (-L i j) * (z i - z j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg i k)).mp
      (hrows i) j (Finset.mem_univ j)
  have hsquare : (z i - z j) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (neg_pos.mpr (hoff i j hij)))
  nlinarith [sq_nonneg (z i - z j)]

end PBCounterexample.Laplacian
