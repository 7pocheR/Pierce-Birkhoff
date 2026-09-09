import Mathlib

/-! Algebraic facts about bilinear forms on matrix spaces. -/

namespace PBCounterexample.OrbitAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n ℝ

def unit (i j : n) : Mat n :=
  fun r c => if r = i then if c = j then 1 else 0 else 0

def vectorUnit (i : n) : n → ℝ := fun r => if r = i then 1 else 0

def outer (u v : n → ℝ) : Mat n := fun i j => u i * v j

def diagonalSum (A : Mat n) : ℝ := ∑ i, A i i

theorem matrix_expansion (A : Mat n) :
    A = ∑ i, ∑ j, A i j • unit i j := by
  ext r c
  simp [unit, Matrix.sum_apply]

theorem linear_eval_expansion (L : Mat n →ₗ[ℝ] ℝ) (A : Mat n) :
    L A = ∑ i, ∑ j, A i j * L (unit i j) := by
  calc
    L A = L (∑ i, ∑ j, A i j • unit i j) := congrArg L (matrix_expansion A)
    _ = ∑ i, ∑ j, A i j * L (unit i j) := by simp

theorem outer_vectorUnit (i j : n) :
    outer (vectorUnit i) (vectorUnit j) = unit i j := by
  ext r c
  simp only [outer, vectorUnit, unit]
  split_ifs <;> norm_num

theorem outer_sum_sub (i j : n) :
    outer (vectorUnit i + vectorUnit j) (vectorUnit i - vectorUnit j) =
      unit i i - unit i j + unit j i - unit j j := by
  ext r c
  simp only [outer, vectorUnit, unit, Pi.add_apply, Pi.sub_apply,
    Matrix.add_apply, Matrix.sub_apply]
  split_ifs <;> ring

@[simp] theorem diagonalSum_unit (i j : n) :
    diagonalSum (unit i j) = if i = j then 1 else 0 := by
  simp [diagonalSum, unit]

@[simp] theorem diagonalSum_add (A B : Mat n) :
    diagonalSum (A + B) = diagonalSum A + diagonalSum B := by
  simp [diagonalSum, Finset.sum_add_distrib]

@[simp] theorem diagonalSum_sub (A B : Mat n) :
    diagonalSum (A - B) = diagonalSum A - diagonalSum B := by
  simp [diagonalSum, Finset.sum_sub_distrib]

@[simp] theorem diagonalSum_smul (r : ℝ) (A : Mat n) :
    diagonalSum (r • A) = r * diagonalSum A := by
  simp [diagonalSum, Finset.mul_sum]

/-- A linear functional that annihilates every traceless outer product is a
constant multiple of the trace. -/
theorem linear_eq_trace_of_outer_vanish (o : n) (L : Mat n →ₗ[ℝ] ℝ)
    (hL : ∀ u v : n → ℝ, diagonalSum (outer u v) = 0 → L (outer u v) = 0) :
    ∀ A : Mat n, L A = diagonalSum A * L (unit o o) := by
  have hoff : ∀ i j : n, i ≠ j → L (unit i j) = 0 := by
    intro i j hij
    have h := hL (vectorUnit i) (vectorUnit j)
    simpa [outer_vectorUnit, hij] using h
  have hdiag : ∀ i : n, L (unit i i) = L (unit o o) := by
    intro i
    by_cases hi : i = o
    · subst i
      rfl
    have ht : diagonalSum
        (outer (vectorUnit i + vectorUnit o) (vectorUnit i - vectorUnit o)) = 0 := by
      rw [outer_sum_sub]
      simp [hi, Ne.symm hi]
    have hv := hL (vectorUnit i + vectorUnit o) (vectorUnit i - vectorUnit o) ht
    rw [outer_sum_sub] at hv
    simp only [map_sub, map_add, hoff i o hi, hoff o i (Ne.symm hi)] at hv
    linarith
  intro A
  rw [linear_eval_expansion]
  calc
    (∑ i, ∑ j, A i j * L (unit i j)) =
        ∑ i, A i i * L (unit o o) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [hdiag]
      · intro j _ hji
        rw [hoff i j (Ne.symm hji), mul_zero]
      · simp
    _ = diagonalSum A * L (unit o o) := by
      simp [diagonalSum, Finset.sum_mul]

/-- Rank-one traceless matrices span the space of all traceless matrices. -/
theorem linear_vanish_on_traceless (o : n) (L : Mat n →ₗ[ℝ] ℝ)
    (hL : ∀ u v : n → ℝ, diagonalSum (outer u v) = 0 → L (outer u v) = 0)
    (A : Mat n) (hA : diagonalSum A = 0) : L A = 0 := by
  rw [linear_eq_trace_of_outer_vanish o L hL A, hA, zero_mul]

/-- Vanishing on pairs of traceless outer products implies vanishing on pairs
of arbitrary traceless matrices. -/
theorem bilinear_vanish_on_traceless (o : n)
    (T : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ)
    (hT : ∀ u v s t : n → ℝ,
      diagonalSum (outer u v) = 0 → diagonalSum (outer s t) = 0 →
      T (outer u v) (outer s t) = 0)
    (A C : Mat n) (hA : diagonalSum A = 0) (hC : diagonalSum C = 0) :
    T A C = 0 := by
  apply linear_vanish_on_traceless o (T A) _ C hC
  intro s t hst
  let L : Mat n →ₗ[ℝ] ℝ :=
    { toFun := fun B => T B (outer s t)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  exact linear_vanish_on_traceless o L
    (fun u v huv => hT u v s t huv hst) A hA

/-- A bilinear form that vanishes on the product of the traceless subspaces
is the sum of two terms each factoring through one trace. -/
theorem bilinear_trace_decomposition (o : n)
    (T : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ)
    (hT : ∀ A C : Mat n, diagonalSum A = 0 → diagonalSum C = 0 → T A C = 0) :
    ∃ L M : Mat n →ₗ[ℝ] ℝ, ∀ A C : Mat n,
      T A C = diagonalSum A * L C + diagonalSum C * M A := by
  let E : Mat n := unit o o
  let M : Mat n →ₗ[ℝ] ℝ :=
    { toFun := fun A => T A E - diagonalSum A * T E E
      map_add' := by intros; simp [add_mul]; ring
      map_smul' := by intros; simp; ring }
  refine ⟨T E, M, ?_⟩
  intro A C
  have hA : diagonalSum (A - diagonalSum A • E) = 0 := by simp [E]
  have hC : diagonalSum (C - diagonalSum C • E) = 0 := by simp [E]
  have h := hT (A - diagonalSum A • E) (C - diagonalSum C • E) hA hC
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  change T A C = diagonalSum A * T E C +
    diagonalSum C * (T A E - diagonalSum A * T E E)
  nlinarith [h]

theorem bilinear_trace_decomposition_of_outer_vanish (o : n)
    (T : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ)
    (hT : ∀ u v s t : n → ℝ,
      diagonalSum (outer u v) = 0 → diagonalSum (outer s t) = 0 →
      T (outer u v) (outer s t) = 0) :
    ∃ L M : Mat n →ₗ[ℝ] ℝ, ∀ A C : Mat n,
      T A C = diagonalSum A * L C + diagonalSum C * M A :=
  bilinear_trace_decomposition o T (bilinear_vanish_on_traceless o T hT)

theorem bilinear_eval_expansion (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) (X Y : Mat n) :
    B X Y = ∑ i, ∑ j, ∑ k, ∑ l, B (unit i j) (unit k l) * X i j * Y k l := by
  calc
    B X Y = ∑ i, ∑ j, X i j * B (unit i j) Y :=
      linear_eval_expansion (B.flip Y) X
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [linear_eval_expansion (B (unit i j)) Y]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

def reshuffle (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ where
  toFun A :=
    { toFun := fun C => ∑ i, ∑ j, ∑ k, ∑ l, B (unit i j) (unit k l) * A i l * C k j
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intros
        simp [Finset.mul_sum, mul_assoc, mul_left_comm] }
  map_add' := by intros; ext C; simp [add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; ext C; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem reshuffle_outer (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) (u v s t : n → ℝ) :
    reshuffle B (outer u t) (outer s v) = B (outer u v) (outer s t) := by
  rw [bilinear_eval_expansion B]
  change (∑ i, ∑ j, ∑ k, ∑ l,
      B (unit i j) (unit k l) * (u i * t l) * (s k * v j)) =
    ∑ i, ∑ j, ∑ k, ∑ l,
      B (unit i j) (unit k l) * (u i * v j) * (s k * t l)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem reshuffle_unit (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ) (i j k l : n) :
    reshuffle B (unit i l) (unit k j) = B (unit i j) (unit k l) := by
  simpa only [outer_vectorUnit] using
    reshuffle_outer B (vectorUnit i) (vectorUnit j) (vectorUnit k) (vectorUnit l)

def matrixMul (X Y : Mat n) : Mat n := fun i k => ∑ j, X i j * Y j k

theorem outer_eq_vecMulVec (u v : n → ℝ) : outer u v = Matrix.vecMulVec u v := rfl

theorem diagonalSum_eq_trace (A : Mat n) : diagonalSum A = Matrix.trace A := rfl

theorem matrixMul_unit (i j k l : n) :
    matrixMul (unit i j) (unit k l) = if j = k then unit i l else 0 := by
  ext r c
  simp [matrixMul, unit]
  split_ifs <;> simp_all [unit]

@[simp] theorem matrixMul_add_left (X Y Z : Mat n) :
    matrixMul (X + Y) Z = matrixMul X Z + matrixMul Y Z := by
  ext i j
  simp [matrixMul, add_mul, Finset.sum_add_distrib]

@[simp] theorem matrixMul_add_right (X Y Z : Mat n) :
    matrixMul X (Y + Z) = matrixMul X Y + matrixMul X Z := by
  ext i j
  simp [matrixMul, mul_add, Finset.sum_add_distrib]

@[simp] theorem matrixMul_smul_left (r : ℝ) (X Y : Mat n) :
    matrixMul (r • X) Y = r • matrixMul X Y := by
  ext i j
  simp [matrixMul, Finset.mul_sum, mul_assoc]

@[simp] theorem matrixMul_smul_right (r : ℝ) (X Y : Mat n) :
    matrixMul X (r • Y) = r • matrixMul X Y := by
  ext i j
  simp [matrixMul, Finset.mul_sum, mul_left_comm]

def productForm (L M : Mat n →ₗ[ℝ] ℝ) : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ where
  toFun X :=
    { toFun := fun Y => L (matrixMul Y X) + M (matrixMul X Y)
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  map_add' := by intros; ext Y; simp; ring
  map_smul' := by intros; ext Y; simp; ring

/-- Bilinear forms on matrices that vanish on all rank-one pairs with both
products zero are precisely sums of linear functionals of the two products. -/
theorem bilinear_products_decomposition (o : n)
    (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] ℝ)
    (hB : ∀ u v s t : n → ℝ,
      diagonalSum (outer u t) = 0 → diagonalSum (outer s v) = 0 →
      B (outer u v) (outer s t) = 0) :
    ∃ L M : Mat n →ₗ[ℝ] ℝ, ∀ X Y : Mat n,
      B X Y = L (matrixMul Y X) + M (matrixMul X Y) := by
  obtain ⟨L, M, hLM⟩ := bilinear_trace_decomposition_of_outer_vanish o (reshuffle B)
    (fun u t s v hut hsv => by rw [reshuffle_outer]; exact hB u v s t hut hsv)
  have hunit : ∀ i j k l : n,
      B (unit i j) (unit k l) =
        L (matrixMul (unit k l) (unit i j)) + M (matrixMul (unit i j) (unit k l)) := by
    intro i j k l
    have h := hLM (unit i l) (unit k j)
    rw [reshuffle_unit] at h
    simpa only [diagonalSum_unit, matrixMul_unit, apply_ite, map_zero,
      ite_mul, one_mul, zero_mul, eq_comm] using h
  refine ⟨L, M, ?_⟩
  intro X Y
  change B X Y = productForm L M X Y
  rw [bilinear_eval_expansion B, bilinear_eval_expansion (productForm L M)]
  simp only [hunit, productForm, LinearMap.coe_mk, AddHom.coe_mk]

end PBCounterexample.OrbitAlgebra
