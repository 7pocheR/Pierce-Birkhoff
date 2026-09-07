import PBCounterexample.PolynomialSelection
import PBCounterexample.Laplacian

/-!
# The polynomial labels on two symmetric five by five matrices
-/

namespace PBCounterexample.SymmetricFunction

open Matrix MvPolynomial
open scoped BigOperators

abbrev I := Fin 5
abbrev J := Fin 6
abbrev Upper := {ij : I × I // ij.1 ≤ ij.2}
abbrev Coord := Bool × Upper
abbrev Point := Coord → ℝ
abbrev Mat := Matrix I I ℝ
abbrev Label := {ij : J × J // ij.1 < ij.2}

instance : Nonempty Label := ⟨⟨(0, 1), by decide⟩⟩

def entry (i j : I) : Upper := ⟨(min i j, max i j), min_le_max⟩

theorem entry_comm (i j : I) : entry i j = entry j i := by
  simp [entry, min_comm, max_comm]

def X (z : Point) : Mat := fun i j => z (false, entry i j)
def Y (z : Point) : Mat := fun i j => z (true, entry i j)

def ofMatrices (B C : Mat) : Point :=
  fun c => if c.1 then C c.2.val.1 c.2.val.2 else B c.2.val.1 c.2.val.2

theorem X_symm (z : Point) : (X z).IsSymm := by
  ext i j
  exact congrArg (fun k => z (false, k)) (entry_comm j i)

theorem Y_symm (z : Point) : (Y z).IsSymm := by
  ext i j
  exact congrArg (fun k => z (true, k)) (entry_comm j i)

@[simp] theorem ofMatrices_X_Y (z : Point) : ofMatrices (X z) (Y z) = z := by
  ext ⟨b, ⟨⟨i, j⟩, hij⟩⟩
  cases b <;> simp [ofMatrices, X, Y, entry, min_eq_left hij, max_eq_right hij]

theorem X_ofMatrices (B C : Mat) (hB : B.IsSymm) : X (ofMatrices B C) = B := by
  ext i j
  by_cases hij : i ≤ j
  · simp [X, ofMatrices, entry, min_eq_left hij, max_eq_right hij]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simpa [X, ofMatrices, entry, min_eq_right hji, max_eq_left hji] using hB.apply i j

theorem Y_ofMatrices (B C : Mat) (hC : C.IsSymm) : Y (ofMatrices B C) = C := by
  ext i j
  by_cases hij : i ≤ j
  · simp [Y, ofMatrices, entry, min_eq_left hij, max_eq_right hij]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simpa [Y, ofMatrices, entry, min_eq_right hji, max_eq_left hji] using hC.apply i j

def A : Matrix J I ℝ := fun i j => (if i.val = j.val then 6 else 0) - 1

noncomputable def S (z : Point) : Mat :=
  fun i j => ((X z * Y z) i j + (X z * Y z) j i) / 2

noncomputable def L (z : Point) : Matrix J J ℝ := A * S z * Aᵀ

noncomputable def productPolynomial (i j : I) : MvPolynomial Coord ℝ :=
  ∑ k : I, MvPolynomial.X (false, entry i k) * MvPolynomial.X (true, entry k j)

noncomputable def symmetricProductPolynomial (i j : I) : MvPolynomial Coord ℝ :=
  (productPolynomial i j + productPolynomial j i) * C (1 / 2)

noncomputable def qPolynomial (a : Label) : MvPolynomial Coord ℝ :=
  -(∑ k : I, ∑ l : I,
    C (A a.val.1 k) * symmetricProductPolynomial k l * C (A a.val.2 l))

noncomputable def determinantPolynomial : MvPolynomial Coord ℝ :=
  Matrix.det (fun i j : I => MvPolynomial.X (false, entry i j))

noncomputable def q (a : Label) (z : Point) : ℝ := eval z (qPolynomial a)
noncomputable def h : Point → ℝ := PolynomialSelection.minimum qPolynomial
noncomputable def f : Point → ℝ := PolynomialSelection.f qPolynomial determinantPolynomial

@[simp] theorem eval_productPolynomial (z : Point) (i j : I) :
    eval z (productPolynomial i j) = (X z * Y z) i j := by
  simp [productPolynomial, Matrix.mul_apply, X, Y]

@[simp] theorem eval_symmetricProductPolynomial (z : Point) (i j : I) :
    eval z (symmetricProductPolynomial i j) = S z i j := by
  simp [symmetricProductPolynomial, S, div_eq_mul_inv]

theorem q_eq (a : Label) (z : Point) : q a z = -L z a.val.1 a.val.2 := by
  simp only [q, qPolynomial, map_neg, map_sum, map_mul, eval_C,
    eval_symmetricProductPolynomial, L, Matrix.mul_apply, Matrix.transpose_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

@[simp] theorem eval_determinantPolynomial (z : Point) :
    eval z determinantPolynomial = (X z).det := by
  calc
    eval z determinantPolynomial =
        ((eval z).mapMatrix (fun i j : I => MvPolynomial.X (false, entry i j))).det :=
      (eval z).map_det _
    _ = (X z).det := by
      congr 1
      ext i j
      exact MvPolynomial.eval_X _

theorem productPolynomial_homogeneous (i j : I) :
    (productPolynomial i j).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (MvPolynomial.isHomogeneous_X ℝ _).mul (MvPolynomial.isHomogeneous_X ℝ _)

theorem qPolynomial_homogeneous (a : Label) : (qPolynomial a).IsHomogeneous 2 := by
  have hs (k l : I) : (symmetricProductPolynomial k l).IsHomogeneous 2 := by
    simpa [symmetricProductPolynomial, mul_comm] using
      ((productPolynomial_homogeneous k l).add
        (productPolynomial_homogeneous l k)).C_mul (1 / 2)
  apply MvPolynomial.IsHomogeneous.neg
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  simpa only [mul_comm] using
    ((hs k l).C_mul (A a.val.1 k)).C_mul (A a.val.2 l)

theorem S_symm (z : Point) : (S z).IsSymm := by
  ext i j
  simp [S, add_comm]

theorem L_symm (z : Point) : (L z).IsSymm := by
  change (A * S z * Aᵀ)ᵀ = A * S z * Aᵀ
  rw [transpose_mul, transpose_mul, transpose_transpose, S_symm z, Matrix.mul_assoc]

theorem A_column_sum (j : I) : ∑ i : J, A i j = 0 := by
  fin_cases j <;> norm_num [A, Fin.sum_univ_succ]

theorem L_row_sum (z : Point) (i : J) : ∑ j : J, L z i j = 0 := by
  change (∑ j : J, ∑ k : I, (A * S z) i k * A j k) = 0
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, A_column_sum, mul_zero]
  simp

noncomputable def liftVector (v : I → ℝ) : J → ℝ :=
  ![v 0 / 6, v 1 / 6, v 2 / 6, v 3 / 6, v 4 / 6,
    -(v 0 + v 1 + v 2 + v 3 + v 4) / 6]

theorem transpose_A_liftVector (v : I → ℝ) : Aᵀ *ᵥ liftVector v = v := by
  ext i
  fin_cases i <;>
    simp [A, liftVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem quadratic_pullback (z : Point) (w : J → ℝ) :
    w ⬝ᵥ (L z *ᵥ w) = (Aᵀ *ᵥ w) ⬝ᵥ (S z *ᵥ (Aᵀ *ᵥ w)) := by
  unfold L
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

theorem quadratic_S (z : Point) (v : I → ℝ) :
    v ⬝ᵥ (S z *ᵥ v) = v ⬝ᵥ ((X z * Y z) *ᵥ v) := by
  have hs : S z = (1 / 2 : ℝ) • ((X z * Y z) + (X z * Y z)ᵀ) := by
    ext i j
    simp only [S, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.transpose_apply]
    ring
  rw [hs, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

theorem quadratic_S_zero_of_X_kernel (z : Point) (v : I → ℝ)
    (hv : X z *ᵥ v = 0) : v ⬝ᵥ (S z *ᵥ v) = 0 := by
  rw [quadratic_S, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, X_symm z, hv, zero_dotProduct]

theorem L_offdiag_neg {z : Point} (hz : 0 < h z) (i j : J) (hij : i ≠ j) :
    L z i j < 0 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hq : 0 < q ⟨(i, j), hij⟩ z :=
      lt_of_lt_of_le hz (PolynomialSelection.minimum_le qPolynomial z ⟨(i, j), hij⟩)
    rw [q_eq] at hq
    exact neg_pos.mp hq
  · have hq : 0 < q ⟨(j, i), hji⟩ z :=
      lt_of_lt_of_le hz (PolynomialSelection.minimum_le qPolynomial z ⟨(j, i), hji⟩)
    rw [q_eq] at hq
    simpa only [(L_symm z).apply i j] using neg_pos.mp hq

theorem X_kernel_zero {z : Point} (hz : 0 < h z) (v : I → ℝ)
    (hv : X z *ᵥ v = 0) : v = 0 := by
  have hquad : liftVector v ⬝ᵥ (L z *ᵥ liftVector v) = 0 := by
    rw [quadratic_pullback, transpose_A_liftVector]
    exact quadratic_S_zero_of_X_kernel z v hv
  have hc := Laplacian.constant_of_quadratic_zero (L z) (L_symm z)
    (L_row_sum z) (L_offdiag_neg hz) (liftVector v) hquad
  have hzero : Aᵀ *ᵥ liftVector v = 0 := by
    ext j
    change (∑ i : J, A i j * liftVector v i) = 0
    simp_rw [hc _ 0, ← Finset.sum_mul, A_column_sum, zero_mul]
  rwa [transpose_A_liftVector] at hzero

theorem determinant_X_ne_zero {z : Point} (hz : 0 < h z) : (X z).det ≠ 0 := by
  have hi : _root_.Function.Injective (X z).mulVec := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply X_kernel_zero hz
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

noncomputable def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover qPolynomial determinantPolynomial
    (fun z hz => by simpa using determinant_X_ne_zero hz)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem coordinate_count : Fintype.card Coord = 30 := by decide

theorem label_count : Fintype.card Label = 15 := by decide

theorem polynomialCover_count : polynomialCover.count = 16 := by
  change Fintype.card (Option Label) = 16
  rw [Fintype.card_option, label_count]

theorem polynomialCover_homogeneous (i : Fin polynomialCover.count) :
    (polynomialCover.label i).IsHomogeneous 2 :=
  PolynomialSelection.polynomialCover_homogeneous _ _ _ qPolynomial_homogeneous i

theorem X_smul (t : ℝ) (z : Point) : X (t • z) = t • X z := rfl

theorem f_positive_homogeneous (t : ℝ) (ht : 0 < t) (z : Point) :
    f (t • z) = t ^ 2 * f z := by
  apply PolynomialSelection.f_positive_homogeneous _ _ qPolynomial_homogeneous ?_ t ht z
  intro s hs w
  rw [eval_determinantPolynomial, eval_determinantPolynomial, X_smul, Matrix.det_smul]
  exact mul_pos_iff_of_pos_left (pow_pos hs _)

set_option maxRecDepth 10000 in
theorem A_gram_offdiag (a : Label) :
    (A * Aᵀ) a.val.1 a.val.2 = if a.val.2 = 5 then -1 else -7 := by
  rcases a with ⟨⟨i, j⟩, hij⟩
  change i.val < j.val at hij
  have hj : j = (5 : Fin 6) ↔ j.val = 5 := Fin.ext_iff
  simp only [hj]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [A, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem q_of_scalar_product (z : Point) (c : ℝ)
    (hp : X z * Y z = c • (1 : Mat)) (a : Label) :
    q a z = if a.val.2 = 5 then c else 7 * c := by
  have hs : S z = c • (1 : Mat) := by
    ext i j
    simp only [S, hp, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  rw [q_eq, L, hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, A_gram_offdiag]
  split_ifs <;> ring

theorem h_of_scalar_product (z : Point) (c : ℝ) (hc : 0 ≤ c)
    (hp : X z * Y z = c • (1 : Mat)) : h z = c := by
  apply le_antisymm
  · calc
      h z ≤ q ⟨(0, 5), by decide⟩ z :=
        PolynomialSelection.minimum_le qPolynomial z _
      _ = c := by rw [q_of_scalar_product z c hp]; simp
  · apply (PolynomialSelection.le_minimum_iff qPolynomial z c).mpr
    intro a
    change c ≤ q a z
    rw [q_of_scalar_product z c hp]
    split_ifs <;> linarith

end PBCounterexample.SymmetricFunction
