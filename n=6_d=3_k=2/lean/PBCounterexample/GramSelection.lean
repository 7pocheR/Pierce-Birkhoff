import PBCounterexample.PolynomialSelection
import PBCounterexample.Laplacian

/-!
# Polynomial selections from a three-column Gram difference

The matrix polynomials may have arbitrary degree. Strict positivity of the six
simplex labels makes the square matrix invertible, which gives a continuous
selection on a finite closed semialgebraic cover of the whole coordinate space.
-/

namespace PBCounterexample.GramSelection

open Matrix MvPolynomial
open scoped BigOperators

abbrev I := Fin 3
abbrev J := Fin 4
abbrev Label := {ij : J × J // ij.1 < ij.2}

instance : Nonempty Label := ⟨⟨(0, 1), by decide⟩⟩

variable {σ : Type*}
variable (A : Matrix I I (MvPolynomial σ ℝ))
variable (B : Matrix (Fin 2) I (MvPolynomial σ ℝ))

def simplex : Matrix J I ℝ := fun i j => (if i.val = j.val then 4 else 0) - 1

noncomputable def gramPolynomial : Matrix I I (MvPolynomial σ ℝ) := Aᵀ * A - Bᵀ * B

noncomputable def gram (z : σ → ℝ) : Matrix I I ℝ :=
  (A.map (eval z))ᵀ * A.map (eval z) - (B.map (eval z))ᵀ * B.map (eval z)

noncomputable def laplacian (z : σ → ℝ) : Matrix J J ℝ :=
  simplex * gram A B z * simplexᵀ

noncomputable def qPolynomial (a : Label) : MvPolynomial σ ℝ :=
  -(∑ k : I, ∑ l : I,
    C (simplex a.val.1 k) * gramPolynomial A B k l * C (simplex a.val.2 l))

noncomputable def determinantPolynomial : MvPolynomial σ ℝ := A.det

noncomputable def minimum : (σ → ℝ) → ℝ :=
  PolynomialSelection.minimum (qPolynomial A B)

noncomputable def f : (σ → ℝ) → ℝ :=
  PolynomialSelection.f (qPolynomial A B) (determinantPolynomial A)

@[simp] theorem eval_gramPolynomial (z : σ → ℝ) (i j : I) :
    eval z (gramPolynomial A B i j) = gram A B z i j := by
  simp [gramPolynomial, gram, Matrix.mul_apply]

theorem eval_qPolynomial (a : Label) (z : σ → ℝ) :
    eval z (qPolynomial A B a) = -laplacian A B z a.val.1 a.val.2 := by
  simp only [qPolynomial, map_neg, map_sum, map_mul, eval_C,
    eval_gramPolynomial, laplacian, Matrix.mul_apply, Matrix.transpose_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

@[simp] theorem eval_determinantPolynomial (z : σ → ℝ) :
    eval z (determinantPolynomial A) = (A.map (eval z)).det :=
  (eval z).map_det A

theorem gram_symm (z : σ → ℝ) : (gram A B z).IsSymm := by
  change (gram A B z)ᵀ = gram A B z
  simp [gram, Matrix.transpose_mul]

theorem laplacian_symm (z : σ → ℝ) : (laplacian A B z).IsSymm := by
  change (simplex * gram A B z * simplexᵀ)ᵀ = simplex * gram A B z * simplexᵀ
  rw [transpose_mul, transpose_mul, transpose_transpose, gram_symm, Matrix.mul_assoc]

theorem simplex_column_sum (j : I) : ∑ i : J, simplex i j = 0 := by
  fin_cases j <;> norm_num [simplex, Fin.sum_univ_succ]

theorem laplacian_row_sum (z : σ → ℝ) (i : J) : ∑ j : J, laplacian A B z i j = 0 := by
  change (∑ j : J, ∑ k : I, (simplex * gram A B z) i k * simplex j k) = 0
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, simplex_column_sum, mul_zero]
  simp

noncomputable def liftVector (v : I → ℝ) : J → ℝ :=
  ![v 0 / 4, v 1 / 4, v 2 / 4, -(v 0 + v 1 + v 2) / 4]

theorem transpose_simplex_liftVector (v : I → ℝ) : simplexᵀ *ᵥ liftVector v = v := by
  ext i
  fin_cases i <;>
    simp [simplex, liftVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem quadratic_pullback (z : σ → ℝ) (w : J → ℝ) :
    w ⬝ᵥ (laplacian A B z *ᵥ w) =
      (simplexᵀ *ᵥ w) ⬝ᵥ (gram A B z *ᵥ (simplexᵀ *ᵥ w)) := by
  unfold laplacian
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

theorem laplacian_offdiag_neg {z : σ → ℝ} (hz : 0 < minimum A B z)
    (i j : J) (hij : i ≠ j) : laplacian A B z i j < 0 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hq : 0 < eval z (qPolynomial A B ⟨(i, j), hij⟩) :=
      lt_of_lt_of_le hz (PolynomialSelection.minimum_le (qPolynomial A B) z ⟨(i, j), hij⟩)
    rw [eval_qPolynomial] at hq
    exact neg_pos.mp hq
  · have hq : 0 < eval z (qPolynomial A B ⟨(j, i), hji⟩) :=
      lt_of_lt_of_le hz (PolynomialSelection.minimum_le (qPolynomial A B) z ⟨(j, i), hji⟩)
    rw [eval_qPolynomial] at hq
    simpa only [(laplacian_symm A B z).apply i j] using neg_pos.mp hq

theorem quadratic_laplacian_nonneg {z : σ → ℝ} (hz : 0 < minimum A B z)
    (w : J → ℝ) : 0 ≤ w ⬝ᵥ (laplacian A B z *ᵥ w) := by
  have hn (i j : J) : 0 ≤ (-laplacian A B z i j) * (w i - w j)^2 := by
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonneg (le_of_lt (neg_pos.mpr (laplacian_offdiag_neg A B hz i j hij)))
        (sq_nonneg _)
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hn i j))
  rw [Laplacian.sum_squared_differences _ (laplacian_symm A B z)
    (laplacian_row_sum A B z)] at hs
  linarith

theorem quadratic_gram_nonpos_of_kernel (z : σ → ℝ) (v : I → ℝ)
    (hv : A.map (eval z) *ᵥ v = 0) : v ⬝ᵥ (gram A B z *ᵥ v) ≤ 0 := by
  rw [gram, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    hv, Matrix.mulVec_zero, dotProduct_zero, zero_sub,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [Matrix.transpose_transpose]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => mul_self_nonneg _)

theorem matrix_kernel_zero {z : σ → ℝ} (hz : 0 < minimum A B z) (v : I → ℝ)
    (hv : A.map (eval z) *ᵥ v = 0) : v = 0 := by
  have hp : 0 ≤ liftVector v ⬝ᵥ (laplacian A B z *ᵥ liftVector v) :=
    quadratic_laplacian_nonneg A B hz _
  have hn : liftVector v ⬝ᵥ (laplacian A B z *ᵥ liftVector v) ≤ 0 := by
    rw [quadratic_pullback, transpose_simplex_liftVector]
    exact quadratic_gram_nonpos_of_kernel A B z v hv
  have hc := Laplacian.constant_of_quadratic_zero _ (laplacian_symm A B z)
    (laplacian_row_sum A B z) (laplacian_offdiag_neg A B hz) (liftVector v)
    (le_antisymm hn hp)
  have hzero : simplexᵀ *ᵥ liftVector v = 0 := by
    ext j
    change (∑ i : J, simplex i j * liftVector v i) = 0
    simp_rw [hc _ 0, ← Finset.sum_mul, simplex_column_sum, zero_mul]
  rwa [transpose_simplex_liftVector] at hzero

theorem determinant_ne_zero {z : σ → ℝ} (hz : 0 < minimum A B z) :
    (A.map (eval z)).det ≠ 0 := by
  have hi : _root_.Function.Injective (A.map (eval z)).mulVec := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply matrix_kernel_zero A B hz
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

noncomputable def polynomialCover : FiniteClosedPolynomialCover (f A B) :=
  PolynomialSelection.polynomialCover (qPolynomial A B) (determinantPolynomial A)
    (fun z hz => by simpa using determinant_ne_zero A B hz)

theorem continuous_f : Continuous (f A B) := (polynomialCover A B).continuous

theorem label_count : Fintype.card Label = 6 := by decide

theorem polynomialCover_count : (polynomialCover A B).count = 7 := by
  change Fintype.card (Option Label) = 7
  rw [Fintype.card_option, label_count]

theorem gramPolynomial_homogeneous
    (hA : ∀ i j, (A i j).IsHomogeneous 1)
    (hB : ∀ i j, (B i j).IsHomogeneous 1) (i j : I) :
    (gramPolynomial A B i j).IsHomogeneous 2 := by
  change ((∑ k : I, A k i * A k j) -
    ∑ k : Fin 2, B k i * B k j).IsHomogeneous 2
  apply MvPolynomial.IsHomogeneous.sub
  · apply MvPolynomial.IsHomogeneous.sum
    intro k _
    exact (hA k i).mul (hA k j)
  · apply MvPolynomial.IsHomogeneous.sum
    intro k _
    exact (hB k i).mul (hB k j)

theorem qPolynomial_homogeneous
    (hA : ∀ i j, (A i j).IsHomogeneous 1)
    (hB : ∀ i j, (B i j).IsHomogeneous 1) (a : Label) :
    (qPolynomial A B a).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.neg
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  simpa only [mul_comm] using
    (((gramPolynomial_homogeneous A B hA hB k l).C_mul
      (simplex a.val.1 k)).C_mul (simplex a.val.2 l))

theorem polynomialCover_homogeneous
    (hA : ∀ i j, (A i j).IsHomogeneous 1)
    (hB : ∀ i j, (B i j).IsHomogeneous 1)
    (i : Fin (polynomialCover A B).count) :
    ((polynomialCover A B).label i).IsHomogeneous 2 :=
  PolynomialSelection.polynomialCover_homogeneous _ _ _
    (qPolynomial_homogeneous A B hA hB) i

theorem f_positive_homogeneous
    (hA : ∀ i j, (A i j).IsHomogeneous 1)
    (hB : ∀ i j, (B i j).IsHomogeneous 1)
    (t : ℝ) (ht : 0 < t) (z : σ → ℝ) :
    f A B (t • z) = t^2 * f A B z := by
  apply PolynomialSelection.f_positive_homogeneous _ _
    (qPolynomial_homogeneous A B hA hB) ?_ t ht z
  intro s hs w
  have hscale : A.map (eval (s • w)) = s • A.map (eval w) := by
    ext i j
    change eval (fun k => s * w k) (A i j) = s * eval w (A i j)
    simpa only [pow_one] using Radial.eval_homogeneous_scale (hA i j) w s
  rw [eval_determinantPolynomial, eval_determinantPolynomial, hscale,
    Matrix.det_smul]
  exact mul_pos_iff_of_pos_left (pow_pos hs _)

end PBCounterexample.GramSelection
