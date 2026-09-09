import Mathlib

namespace PBCounterexample.OrbitNormalization

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def rankOneUnit (u v : n → ℝ) (h : 1 + v ⬝ᵥ u ≠ 0) :
    (Matrix n n ℝ)ˣ where
  val := 1 + vecMulVec u v
  inv := 1 - (1 + v ⬝ᵥ u)⁻¹ • vecMulVec u v
  val_inv := by
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      vecMulVec_mul_vecMulVec, vecMulVec_smul]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  inv_val := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      vecMulVec_mul_vecMulVec, vecMulVec_smul]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring

@[simp] theorem rankOneUnit_val (u v : n → ℝ) (h : 1 + v ⬝ᵥ u ≠ 0) :
    (rankOneUnit u v h : Matrix n n ℝ) = 1 + vecMulVec u v := rfl

theorem exists_distinct_coordinates (u t : n → ℝ) (hu : u ≠ 0) (ht : t ≠ 0)
    (htu : t ⬝ᵥ u = 0) : ∃ i j : n, i ≠ j ∧ u i ≠ 0 ∧ t j ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  change u i ≠ 0 at hi
  by_contra h
  push_neg at h
  have hrest : ∀ j, j ≠ i → t j = 0 := by
    intro j hji
    exact h i j (Ne.symm hji) hi
  have hsum : t ⬝ᵥ u = t i * u i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hrest j hji, zero_mul]
    · simp
  have hti : t i = 0 := (mul_eq_zero.mp (hsum.symm.trans htu)).resolve_right hi
  apply ht
  funext j
  by_cases hj : j = i
  · subst j
    exact hti
  · exact hrest j hj

theorem exists_unit_with_column_and_inverse_row_at (u t : n → ℝ) (i j : n)
    (hij : i ≠ j) (hu : u i ≠ 0) (ht : t j ≠ 0) (htu : t ⬝ᵥ u = 0) :
    ∃ U : (Matrix n n ℝ)ˣ,
      (↑U : Matrix n n ℝ) *ᵥ Pi.single i 1 = u ∧
      Pi.single j 1 ᵥ* (↑(U⁻¹) : Matrix n n ℝ) = t := by
  let ei : n → ℝ := Pi.single i 1
  let ej : n → ℝ := Pi.single j 1
  have ha : 1 + ei ⬝ᵥ (u - ei) ≠ 0 := by
    simpa [ei, dotProduct_sub] using hu
  let A := rankOneUnit (u - ei) ei ha
  have hA : (↑A : Matrix n n ℝ) *ᵥ ei = u := by
    simp only [A, rankOneUnit_val, add_mulVec, one_mulVec, vecMulVec_mulVec]
    simp [ei]
  let t' : n → ℝ := t ᵥ* (↑A : Matrix n n ℝ)
  have hti : t' i = 0 := by
    have h := congrArg (fun w : n → ℝ => t ⬝ᵥ w) hA
    change t ⬝ᵥ (↑A : Matrix n n ℝ).col i = 0
    simpa [ei] using h.trans htu
  have htj : t' j = t j := by
    simp [t', A, vecMul_add, vecMul_vecMulVec, ei, hij, Ne.symm hij]
  have hw : 1 + (t' - ej) ⬝ᵥ ej ≠ 0 := by
    simpa [ej, sub_dotProduct, htj] using ht
  let W := rankOneUnit ej (t' - ej) hw
  have hWi : (↑W : Matrix n n ℝ) *ᵥ ei = ei := by
    have hdot : (t' - ej) ⬝ᵥ ei = 0 := by
      simp [ei, ej, sub_dotProduct, hti, hij]
    simp only [W, rankOneUnit_val, add_mulVec, one_mulVec, vecMulVec_mulVec, hdot]
    simp
  have hWj : ej ᵥ* (↑W : Matrix n n ℝ) = t' := by
    simp only [W, rankOneUnit_val, vecMul_add, vecMul_one, vecMul_vecMulVec]
    simp [ej]
  have hWinvi : (↑(W⁻¹) : Matrix n n ℝ) *ᵥ ei = ei := by
    calc
      (↑(W⁻¹) : Matrix n n ℝ) *ᵥ ei =
          (↑(W⁻¹) : Matrix n n ℝ) *ᵥ ((↑W : Matrix n n ℝ) *ᵥ ei) := by rw [hWi]
      _ = ei := by rw [mulVec_mulVec]; simp
  refine ⟨A * W⁻¹, ?_, ?_⟩
  · change ((↑A : Matrix n n ℝ) * (↑(W⁻¹) : Matrix n n ℝ)) *ᵥ ei = u
    rw [← mulVec_mulVec, hWinvi, hA]
  · change ej ᵥ* (↑((A * W⁻¹)⁻¹) : Matrix n n ℝ) = t
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    rw [← vecMul_vecMul, hWj]
    change (t ᵥ* (↑A : Matrix n n ℝ)) ᵥ* (↑(A⁻¹) : Matrix n n ℝ) = t
    rw [vecMul_vecMul]
    simp

def permutationUnit (σ : Equiv.Perm n) : (Matrix n n ℝ)ˣ where
  val := (σ⁻¹).permMatrix ℝ
  inv := σ.permMatrix ℝ
  val_inv := by rw [← permMatrix_mul]; simp
  inv_val := by rw [← permMatrix_mul]; simp

theorem permutationUnit_mulVec_single (σ : Equiv.Perm n) (i : n) :
    (↑(permutationUnit σ) : Matrix n n ℝ) *ᵥ Pi.single i 1 = Pi.single (σ i) 1 := by
  change (σ⁻¹).permMatrix ℝ *ᵥ Pi.single i 1 = Pi.single (σ i) 1
  rw [permMatrix_mulVec]
  funext j
  change (Pi.single i (1 : ℝ) : n → ℝ) (σ.symm j) =
    (Pi.single (σ i) (1 : ℝ) : n → ℝ) j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem single_vecMul_permutationUnit_inv (σ : Equiv.Perm n) (i : n) :
    Pi.single i 1 ᵥ* (↑((permutationUnit σ)⁻¹) : Matrix n n ℝ) = Pi.single (σ i) 1 := by
  change Pi.single i 1 ᵥ* σ.permMatrix ℝ = Pi.single (σ i) 1
  rw [vecMul_permMatrix]
  funext j
  change (Pi.single i (1 : ℝ) : n → ℝ) (σ.symm j) =
    (Pi.single (σ i) (1 : ℝ) : n → ℝ) j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem exists_permutation_two (a b i j : n) (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm n, σ a = i ∧ σ b = j := by
  let σ := Equiv.swap a i * Equiv.swap b (Equiv.swap a i j)
  have hja : Equiv.swap a i j ≠ a := by
    simpa only [ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] using Ne.symm hij
  refine ⟨σ, ?_, ?_⟩
  · dsimp [σ]
    rw [Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hja), Equiv.swap_apply_left]
  · simp [σ, Equiv.Perm.mul_apply]

theorem exists_unit_with_column_and_inverse_row (a b : n) (hab : a ≠ b)
    (u t : n → ℝ) (hu : u ≠ 0) (ht : t ≠ 0) (htu : t ⬝ᵥ u = 0) :
    ∃ U : (Matrix n n ℝ)ˣ,
      (↑U : Matrix n n ℝ) *ᵥ Pi.single a 1 = u ∧
      Pi.single b 1 ᵥ* (↑(U⁻¹) : Matrix n n ℝ) = t := by
  obtain ⟨i, j, hij, hui, htj⟩ := exists_distinct_coordinates u t hu ht htu
  obtain ⟨A, hA, hAi⟩ := exists_unit_with_column_and_inverse_row_at u t i j hij hui htj htu
  obtain ⟨σ, hσa, hσb⟩ := exists_permutation_two a b i j hab hij
  refine ⟨A * permutationUnit σ, ?_, ?_⟩
  · simp only [Units.val_mul, ← mulVec_mulVec, permutationUnit_mulVec_single, hσa, hA]
  · simp only [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul,
      single_vecMul_permutationUnit_inv, hσb, hAi]

end PBCounterexample.OrbitNormalization
