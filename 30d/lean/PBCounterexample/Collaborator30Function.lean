import PBCounterexample.SymmetricPerturbation

/-!
# Forty quadratic labels on two symmetric five by five matrices

The labels are `(XY)ᵢᵢ + 4τ(XY)ᵢⱼ`, for ordered pairs `i ≠ j` and
`τ ∈ {-1, 1}`. The positive minimum is selected when `det X > 0`.
-/

namespace PBCounterexample.Collaborator30Function

open Matrix MvPolynomial
open SymmetricFunction (I Coord Point Mat X Y)
open scoped BigOperators

abbrev Label := {ij : I × I // ij.1 ≠ ij.2} × Bool

instance : Nonempty Label := ⟨(⟨(0, 1), by decide⟩, true)⟩

def sign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def qPolynomial (a : Label) : MvPolynomial Coord ℝ :=
  SymmetricFunction.productPolynomial a.1.val.1 a.1.val.1 +
    C (4 * sign a.2) * SymmetricFunction.productPolynomial a.1.val.1 a.1.val.2

noncomputable def q (a : Label) (z : Point) : ℝ := eval z (qPolynomial a)

noncomputable def h : Point → ℝ := PolynomialSelection.minimum qPolynomial

noncomputable def f : Point → ℝ :=
  PolynomialSelection.f qPolynomial SymmetricFunction.determinantPolynomial

theorem q_eq (a : Label) (z : Point) :
    q a z = (X z * Y z) a.1.val.1 a.1.val.1 +
      4 * sign a.2 * (X z * Y z) a.1.val.1 a.1.val.2 := by
  simp [q, qPolynomial]

theorem f_eq (z : Point) : f z =
    if 0 < h z ∧ 0 < (X z).det then h z else 0 := by
  simp only [f, h, PolynomialSelection.f, SymmetricFunction.eval_determinantPolynomial]
  exact if_congr Iff.rfl rfl rfl

theorem qPolynomial_homogeneous (a : Label) : (qPolynomial a).IsHomogeneous 2 :=
  (SymmetricFunction.productPolynomial_homogeneous _ _).add
    ((SymmetricFunction.productPolynomial_homogeneous _ _).C_mul _)

theorem h_le_q (z : Point) (a : Label) : h z ≤ q a z :=
  PolynomialSelection.minimum_le qPolynomial z a

theorem off_diagonal_bound {z : Point} (hz : 0 < h z)
    (i j : I) (hij : i ≠ j) :
    4 * |(X z * Y z) i j| < (X z * Y z) i i := by
  have hp : 0 < q (⟨(i, j), hij⟩, true) z :=
    lt_of_lt_of_le hz (h_le_q z _)
  have hm : 0 < q (⟨(i, j), hij⟩, false) z :=
    lt_of_lt_of_le hz (h_le_q z _)
  simp [q_eq, sign] at hp hm
  rcases le_total 0 ((X z * Y z) i j) with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg]
    linarith
  · rw [abs_of_nonpos hnonpos]
    linarith

theorem row_strictly_diagonally_dominant {z : Point} (hz : 0 < h z) (i : I) :
    ∑ j ∈ Finset.univ.erase i, |(X z * Y z) i j| < (X z * Y z) i i := by
  have hcard : (Finset.univ.erase i : Finset I).card = 4 := by simp
  have hnonempty : (Finset.univ.erase i : Finset I).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; decide)
  calc
    _ < ∑ _j ∈ Finset.univ.erase i, (X z * Y z) i i / 4 := by
      apply Finset.sum_lt_sum_of_nonempty hnonempty
      intro j hj
      have hb := off_diagonal_bound hz i j (Finset.ne_of_mem_erase hj).symm
      linarith
    _ = (X z * Y z) i i := by simp [hcard]; ring

theorem determinant_product_ne_zero {z : Point} (hz : 0 < h z) :
    (X z * Y z).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hi := row_strictly_diagonally_dominant hz i
  have hd : 0 < (X z * Y z) i i :=
    lt_of_le_of_lt (Finset.sum_nonneg fun j _ => abs_nonneg _) hi
  simpa only [Real.norm_eq_abs, abs_of_pos hd] using hi

theorem determinant_X_ne_zero {z : Point} (hz : 0 < h z) : (X z).det ≠ 0 := by
  have hp := determinant_product_ne_zero hz
  rw [Matrix.det_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

theorem determinant_Y_ne_zero {z : Point} (hz : 0 < h z) : (Y z).det ≠ 0 := by
  have hp := determinant_product_ne_zero hz
  rw [Matrix.det_mul] at hp
  exact (mul_ne_zero_iff.mp hp).2

noncomputable def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover qPolynomial SymmetricFunction.determinantPolynomial
    (fun z hz => by simpa using determinant_X_ne_zero hz)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem label_count : Fintype.card Label = 40 := by decide

theorem polynomialCover_count : polynomialCover.count = 41 := by
  change Fintype.card (Option Label) = 41
  rw [Fintype.card_option, label_count]

theorem polynomialCover_homogeneous (i : Fin polynomialCover.count) :
    (polynomialCover.label i).IsHomogeneous 2 :=
  PolynomialSelection.polynomialCover_homogeneous _ _ _ qPolynomial_homogeneous i

theorem f_positive_homogeneous (t : ℝ) (ht : 0 < t) (z : Point) :
    f (t • z) = t ^ 2 * f z := by
  apply PolynomialSelection.f_positive_homogeneous _ _ qPolynomial_homogeneous ?_ t ht z
  intro s hs w
  rw [SymmetricFunction.eval_determinantPolynomial,
    SymmetricFunction.eval_determinantPolynomial, SymmetricFunction.X_smul, Matrix.det_smul]
  exact mul_pos_iff_of_pos_left (pow_pos hs _)

theorem q_of_scalar_product (z : Point) (c : ℝ)
    (hp : X z * Y z = c • (1 : Mat)) (a : Label) : q a z = c := by
  rw [q_eq, hp]
  simp [Matrix.smul_apply, Matrix.one_apply, a.1.property]

theorem h_of_scalar_product (z : Point) (c : ℝ)
    (hp : X z * Y z = c • (1 : Mat)) : h z = c := by
  obtain ⟨a, ha⟩ := PolynomialSelection.exists_minimum_eq qPolynomial z
  exact ha.trans (q_of_scalar_product z c hp a)

theorem h_pointPath (U : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    h (SymmetricPerturbation.pointPath U η t) = t ^ 2 :=
  h_of_scalar_product _ _ (SymmetricPerturbation.pointPath_XY U η t hη)

theorem f_plus (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    f (SymmetricPerturbation.pointPath U 1 t) = t ^ 2 := by
  have hh := h_pointPath U 1 t (by norm_num)
  rw [f_eq, if_pos ⟨by rw [hh]; exact pow_pos ht 2,
    SymmetricPerturbation.determinant_X_plus_pos U t ht⟩, hh]

theorem f_minus (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    f (SymmetricPerturbation.pointPath U (-1) t) = 0 := by
  have hd := SymmetricPerturbation.determinant_X_minus_neg U t ht
  rw [f_eq, if_neg (fun h => not_lt_of_ge (le_of_lt hd) h.2)]

theorem f_plus_pos (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    0 < f (SymmetricPerturbation.pointPath U 1 t) := by
  rw [f_plus U t ht]
  exact pow_pos ht 2

end PBCounterexample.Collaborator30Function
