import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Identifying a matrix kernel from an annihilated column space and ranks. -/

namespace PBCounterexample

open Matrix Module

theorem matrix_kernel_eq_range_of_rank_sum
    {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin r) K)
    (hzero : A * B = 0) (hrank : A.rank + B.rank = n) :
    LinearMap.ker A.mulVecLin = LinearMap.range B.mulVecLin := by
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    change A *ᵥ (B *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  have hn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdim : finrank K (LinearMap.range B.mulVecLin) =
      finrank K (LinearMap.ker A.mulVecLin) := by
    change finrank K (LinearMap.range A.mulVecLin) +
      finrank K (LinearMap.range B.mulVecLin) = n at hrank
    simp only [Module.finrank_pi, Fintype.card_fin] at hn
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

theorem matrix_mulVec_eq_zero_iff_of_full_column_rank
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hrank : A.rank = n)
    (v : Fin n → K) : A *ᵥ v = 0 ↔ v = 0 := by
  have hn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change finrank K (LinearMap.range A.mulVecLin) = n at hrank
  have hd : finrank K (LinearMap.ker A.mulVecLin) = 0 := by
    simp only [Module.finrank_pi, Fintype.card_fin] at hn
    omega
  have hk : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hd
  change v ∈ LinearMap.ker A.mulVecLin ↔ v = 0
  rw [hk]
  rfl

end PBCounterexample
