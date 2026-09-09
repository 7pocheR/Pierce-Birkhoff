import PBCounterexample.Semialgebraic

/-!
# The function on pairs of independent six by six real matrices

The coordinate type has 72 elements. Each of the 192 quadratic labels uses
one row and one choice of signs on that row's five off-diagonal entries.
-/

namespace PBCounterexample.Function

open MvPolynomial
open scoped BigOperators

abbrev I := Fin 6
abbrev Coord := Bool × I × I
abbrev Point := Coord → ℝ
abbrev Mat := Matrix I I ℝ
abbrev Label := (i : I) × ({j : I // j ≠ i} → Bool)

instance : Nonempty Label := ⟨⟨0, fun _ => false⟩⟩

def X (z : Point) : Mat := fun i j => z (false, i, j)
def Y (z : Point) : Mat := fun i j => z (true, i, j)

def ofMatrices (A B : Mat) : Point :=
  fun c => if c.1 then B c.2.1 c.2.2 else A c.2.1 c.2.2

@[simp] theorem X_ofMatrices (A B : Mat) : X (ofMatrices A B) = A := rfl

@[simp] theorem Y_ofMatrices (A B : Mat) : Y (ofMatrices A B) = B := rfl

@[simp] theorem ofMatrices_X_Y (z : Point) : ofMatrices (X z) (Y z) = z := by
  ext ⟨b, i, j⟩
  cases b <;> rfl

def matrixPairEquiv : Point ≃ Mat × Mat where
  toFun z := (X z, Y z)
  invFun p := ofMatrices p.1 p.2
  left_inv := ofMatrices_X_Y
  right_inv _ := rfl

def sign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def productPolynomial (i j : I) : MvPolynomial Coord ℝ :=
  ∑ k : I, MvPolynomial.X (false, i, k) * MvPolynomial.X (true, k, j)

noncomputable def qPolynomial (a : Label) : MvPolynomial Coord ℝ :=
  productPolynomial a.1 a.1 -
    ∑ j : {j : I // j ≠ a.1}, C (sign (a.2 j)) * productPolynomial a.1 j

noncomputable def determinantPolynomial : MvPolynomial Coord ℝ :=
  Matrix.det (fun i j : I => MvPolynomial.X (false, i, j))

noncomputable def q (a : Label) (z : Point) : ℝ := eval z (qPolynomial a)

noncomputable def h (z : Point) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Label => q a z)

noncomputable def f (z : Point) : ℝ :=
  if 0 < h z ∧ 0 < (X z).det then h z else 0

@[simp] theorem eval_productPolynomial (z : Point) (i j : I) :
    eval z (productPolynomial i j) = (X z * Y z) i j := by
  simp [productPolynomial, Matrix.mul_apply, X, Y]

theorem q_eq (a : Label) (z : Point) :
    q a z = (X z * Y z) a.1 a.1 -
      ∑ j : {j : I // j ≠ a.1}, sign (a.2 j) * (X z * Y z) a.1 j := by
  simp [q, qPolynomial]

@[simp] theorem eval_determinantPolynomial (z : Point) :
    eval z determinantPolynomial = (X z).det := by
  calc
    eval z determinantPolynomial =
        ((eval z).mapMatrix (fun i j : I => MvPolynomial.X (false, i, j))).det :=
      (eval z).map_det _
    _ = (X z).det := by
      congr 1
      ext i j
      change eval z (MvPolynomial.X (false, i, j)) = z (false, i, j)
      exact MvPolynomial.eval_X _

theorem productPolynomial_homogeneous (i j : I) :
    (productPolynomial i j).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (MvPolynomial.isHomogeneous_X ℝ _).mul (MvPolynomial.isHomogeneous_X ℝ _)

theorem qPolynomial_homogeneous (a : Label) : (qPolynomial a).IsHomogeneous 2 := by
  apply (productPolynomial_homogeneous a.1 a.1).sub
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (productPolynomial_homogeneous a.1 j).C_mul _

theorem qPolynomial_degree (a : Label) : (qPolynomial a).totalDegree ≤ 2 :=
  (qPolynomial_homogeneous a).totalDegree_le

theorem h_le_q (z : Point) (a : Label) : h z ≤ q a z :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem le_h_iff (z : Point) (r : ℝ) : r ≤ h z ↔ ∀ a, r ≤ q a z := by
  simp [h]

theorem exists_h_eq_q (z : Point) : ∃ a, h z = q a z := by
  simpa [h] using
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty (fun a : Label => q a z)

theorem continuous_q (a : Label) : Continuous (q a) :=
  MvPolynomial.continuous_eval (qPolynomial a)

theorem continuous_h : Continuous h :=
  Continuous.finset_inf'_apply _ (fun a _ => continuous_q a)

theorem sign_mul_le_abs (b : Bool) (r : ℝ) : sign b * r ≤ |r| := by
  cases b <;> simp [sign, le_abs_self, neg_le_abs]

theorem sign_of_nonneg_mul (r : ℝ) : sign (decide (0 ≤ r)) * r = |r| := by
  by_cases hr : 0 ≤ r
  · simp [sign, hr, abs_of_nonneg hr]
  · simp [sign, hr, abs_of_neg (lt_of_not_ge hr)]

theorem row_strictly_diagonally_dominant {z : Point} (hz : 0 < h z) (i : I) :
    ∑ j ∈ Finset.univ.erase i, |(X z * Y z) i j| < (X z * Y z) i i := by
  let a : Label := ⟨i, fun j => decide (0 ≤ (X z * Y z) i j)⟩
  have hq : 0 < q a z := lt_of_lt_of_le hz (h_le_q z a)
  rw [q_eq] at hq
  dsimp [a] at hq
  simp_rw [sign_of_nonneg_mul] at hq
  rw [Finset.sum_subtype (p := fun j : I => j ≠ i) (Finset.univ.erase i) (by simp)]
  linarith

theorem determinant_X_ne_zero {z : Point} (hz : 0 < h z) : (X z).det ≠ 0 := by
  have hp : (X z * Y z).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have hi := row_strictly_diagonally_dominant hz i
    have hdiag : 0 < (X z * Y z) i i :=
      lt_of_le_of_lt (Finset.sum_nonneg fun j _ => abs_nonneg _) hi
    simpa only [Real.norm_eq_abs, abs_of_pos hdiag] using hi
  rw [Matrix.det_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

noncomputable def zeroRegion : Set Point :=
  {z | (X z).det ≤ 0} ∪ ⋃ a : Label, {z | q a z ≤ 0}

noncomputable def quadraticRegion (a : Label) : Set Point :=
  {z | 0 ≤ (X z).det} ∩ (⋂ b : Label, {z | 0 ≤ q b z}) ∩
    (⋂ b : Label, {z | q a z ≤ q b z})

noncomputable def region : Option Label → Set Point
  | none => zeroRegion
  | some a => quadraticRegion a

noncomputable def labelPolynomial : Option Label → MvPolynomial Coord ℝ
  | none => 0
  | some a => qPolynomial a

theorem isClosed_zeroRegion : IsClosed zeroRegion := by
  apply IsClosed.union
  · simpa using isClosed_le (MvPolynomial.continuous_eval determinantPolynomial) continuous_const
  · exact isClosed_iUnion_of_finite fun a => isClosed_le (continuous_q a) continuous_const

theorem isClosed_quadraticRegion (a : Label) : IsClosed (quadraticRegion a) := by
  apply IsClosed.inter
  · apply IsClosed.inter
    · simpa using isClosed_le continuous_const (MvPolynomial.continuous_eval determinantPolynomial)
    · exact isClosed_iInter fun b => isClosed_le continuous_const (continuous_q b)
  · exact isClosed_iInter fun b => isClosed_le (continuous_q a) (continuous_q b)

theorem semialgebraic_zeroRegion : IsSemialgebraic zeroRegion := by
  apply IsSemialgebraic.union
  · simpa using IsSemialgebraic.polynomial_le determinantPolynomial
  · exact IsSemialgebraic.iUnion _ fun a => IsSemialgebraic.polynomial_le (qPolynomial a)

theorem semialgebraic_quadraticRegion (a : Label) : IsSemialgebraic (quadraticRegion a) := by
  apply IsSemialgebraic.inter
  · apply IsSemialgebraic.inter
    · simpa using IsSemialgebraic.ge_zero determinantPolynomial
    · exact IsSemialgebraic.iInter _ fun b => IsSemialgebraic.ge_zero (qPolynomial b)
  · exact IsSemialgebraic.iInter _ fun b => IsSemialgebraic.le (qPolynomial a) (qPolynomial b)

theorem f_eq_zero_on_zeroRegion {z : Point} (hz : z ∈ zeroRegion) : f z = 0 := by
  rcases hz with hd | hq
  · change (X z).det ≤ 0 at hd
    simp [f, not_lt_of_ge hd]
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hq
    have hh : h z ≤ 0 := le_trans (h_le_q z a) ha
    simp [f, not_lt_of_ge hh]

theorem h_eq_on_quadraticRegion {z : Point} {a : Label} (hz : z ∈ quadraticRegion a) :
    h z = q a z := by
  apply le_antisymm (h_le_q z a)
  apply (le_h_iff z (q a z)).mpr
  exact Set.mem_iInter.mp hz.2

theorem f_eq_on_quadraticRegion {z : Point} {a : Label} (hz : z ∈ quadraticRegion a) :
    f z = q a z := by
  have heq := h_eq_on_quadraticRegion hz
  have hnonneg : 0 ≤ h z := by
    rw [heq]
    exact Set.mem_iInter.mp hz.1.2 a
  by_cases hh : 0 < h z
  · have hd : 0 < (X z).det := lt_of_le_of_ne hz.1.1 (Ne.symm (determinant_X_ne_zero hh))
    rw [f, ite_eq_left ⟨hh, hd⟩, heq]
  · have hzero : h z = 0 := le_antisymm (le_of_not_gt hh) hnonneg
    have hqzero : q a z = 0 := heq.symm.trans hzero
    simp [f, hh, hqzero]

theorem region_covers_point (z : Point) : ∃ a, z ∈ region a := by
  classical
  by_cases hz : z ∈ zeroRegion
  · exact ⟨none, hz⟩
  · have hd : 0 ≤ (X z).det := by
      by_contra hd
      exact hz (Or.inl (le_of_lt (lt_of_not_ge hd)))
    have hq : ∀ b, 0 ≤ q b z := by
      intro b
      by_contra hb
      exact hz (Or.inr (Set.mem_iUnion.mpr ⟨b, le_of_lt (lt_of_not_ge hb)⟩))
    obtain ⟨a, ha⟩ := exists_h_eq_q z
    refine ⟨some a, ⟨⟨hd, Set.mem_iInter.mpr hq⟩, Set.mem_iInter.mpr ?_⟩⟩
    intro b
    change q a z ≤ q b z
    rw [← ha]
    exact h_le_q z b

theorem region_covers : ⋃ a, region a = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact region_covers_point z

theorem region_agrees (a : Option Label) (z : Point) (hz : z ∈ region a) :
    f z = eval z (labelPolynomial a) := by
  cases a with
  | none => simpa [labelPolynomial] using f_eq_zero_on_zeroRegion hz
  | some a => exact f_eq_on_quadraticRegion hz

noncomputable def polynomialCover : FiniteClosedPolynomialCover f where
  count := Fintype.card (Option Label)
  region i := region ((Fintype.equivFin (Option Label)).symm i)
  label i := labelPolynomial ((Fintype.equivFin (Option Label)).symm i)
  closed i := by
    cases (Fintype.equivFin (Option Label)).symm i with
    | none => exact isClosed_zeroRegion
    | some a => exact isClosed_quadraticRegion a
  semialgebraic i := by
    cases (Fintype.equivFin (Option Label)).symm i with
    | none => exact semialgebraic_zeroRegion
    | some a => exact semialgebraic_quadraticRegion a
  covers := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := region_covers_point z
    exact ⟨Fintype.equivFin (Option Label) a, by simpa using ha⟩
  agrees i z hz := region_agrees _ z hz

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem X_smul (t : ℝ) (z : Point) : X (t • z) = t • X z := rfl

theorem Y_smul (t : ℝ) (z : Point) : Y (t • z) = t • Y z := rfl

theorem product_smul (t : ℝ) (z : Point) :
    X (t • z) * Y (t • z) = t ^ 2 • (X z * Y z) := by
  rw [X_smul, Y_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

theorem q_smul (a : Label) (t : ℝ) (z : Point) : q a (t • z) = t ^ 2 * q a z := by
  rw [q_eq, q_eq, product_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem h_smul (t : ℝ) (z : Point) : h (t • z) = t ^ 2 * h z := by
  obtain ⟨a, ha⟩ := exists_h_eq_q z
  obtain ⟨b, hb⟩ := exists_h_eq_q (t • z)
  apply le_antisymm
  · calc
      h (t • z) ≤ q a (t • z) := h_le_q _ a
      _ = t ^ 2 * q a z := q_smul a t z
      _ = t ^ 2 * h z := by rw [ha]
  · calc
      t ^ 2 * h z ≤ t ^ 2 * q b z :=
        mul_le_mul_of_nonneg_left (h_le_q z b) (sq_nonneg t)
      _ = q b (t • z) := (q_smul b t z).symm
      _ = h (t • z) := hb.symm

theorem determinant_X_smul (t : ℝ) (z : Point) : (X (t • z)).det = t ^ 6 * (X z).det := by
  rw [X_smul, Matrix.det_smul]
  rfl

theorem f_positive_homogeneous (t : ℝ) (ht : 0 < t) (z : Point) :
    f (t • z) = t ^ 2 * f z := by
  have htwo : 0 < t ^ 2 := pow_pos ht 2
  have hsix : 0 < t ^ 6 := pow_pos ht 6
  have hpos : 0 < h (t • z) ↔ 0 < h z := by
    rw [h_smul]
    exact mul_pos_iff_of_pos_left htwo
  have dpos : 0 < (X (t • z)).det ↔ 0 < (X z).det := by
    rw [determinant_X_smul]
    exact mul_pos_iff_of_pos_left hsix
  simp only [f, hpos, dpos]
  split_ifs
  · exact h_smul t z
  · simp

theorem coordinate_count : Fintype.card Coord = 72 := by decide

theorem label_count : Fintype.card Label = 192 := by
  have hc (i : I) : Fintype.card {j : I // j ≠ i} = 5 := by
    simp [Fintype.card_subtype_compl, I]
  simp [Label, Fintype.card_sigma, hc, I]

theorem polynomialCover_count : polynomialCover.count = 193 := by
  change Fintype.card (Option Label) = 193
  rw [Fintype.card_option, label_count]

theorem labelPolynomial_homogeneous (a : Option Label) :
    (labelPolynomial a).IsHomogeneous 2 := by
  cases a with
  | none => exact MvPolynomial.isHomogeneous_zero _ _ _
  | some a => exact qPolynomial_homogeneous a

theorem polynomialCover_homogeneous (i : Fin polynomialCover.count) :
    (polynomialCover.label i).IsHomogeneous 2 :=
  labelPolynomial_homogeneous _

end PBCounterexample.Function
