import PBCounterexample.Quadratic8Data
import PBCounterexample.QuadraticSignPartition

/-! Ordinary total-degree bounds and a partition of the whole eight-dimensional
space by 137 quadratic polynomial sign tests. -/

namespace PBCounterexample.Quadratic8

open MvPolynomial

theorem cofactor1_homogeneous : cofactor1.IsHomogeneous 2 := by
  have hX (i : Fin 6) := MvPolynomial.isHomogeneous_X ℝ i
  exact ((hX 0).mul (((hX 4).neg).add ((hX 5).C_mul (1 / 2 : ℝ)))).add
    ((hX 1).mul ((hX 2).add (hX 3)))

theorem cofactor2_homogeneous : cofactor2.IsHomogeneous 2 := by
  exact ((MvPolynomial.isHomogeneous_X_pow 0 2).add
    (MvPolynomial.isHomogeneous_X_pow 1 2)).neg

theorem cofactor1_degree : cofactor1.totalDegree ≤ 2 := cofactor1_homogeneous.totalDegree_le

theorem cofactor2_degree : cofactor2.totalDegree ≤ 2 := cofactor2_homogeneous.totalDegree_le

theorem lift_degree_le (p : MvPolynomial (Fin 6) ℝ) :
    (lift p).totalDegree ≤ p.totalDegree := totalDegree_rename_le baseIndex p

theorem errorPolynomial_degree (k : Fin 2) : (errorPolynomial k).totalDegree ≤ 2 := by
  fin_cases k
  · apply (totalDegree_sub _ _).trans
    exact max_le (by simp) ((lift_degree_le cofactor1).trans cofactor1_degree)
  · apply (totalDegree_sub _ _).trans
    exact max_le (by simp) ((lift_degree_le cofactor2).trans cofactor2_degree)

theorem orientationPolynomial_homogeneous : orientationPolynomial.IsHomogeneous 2 := by
  have hX (i : Fin 8) := MvPolynomial.isHomogeneous_X ℝ i
  exact ((hX 2).mul (hX 6)).add (((hX 5).mul (hX 7)).C_mul (1 / 2 : ℝ))

theorem orientationPolynomial_degree : orientationPolynomial.totalDegree ≤ 2 :=
  orientationPolynomial_homogeneous.totalDegree_le

theorem base_labelPolynomial_degree (j : Fin 4) :
    (Gram6.labelPolynomial j).totalDegree ≤ 2 := by
  rw [← qPolynomial_baseLabel]
  exact (Gram6.qPolynomial_homogeneous (baseLabel j)).totalDegree_le

theorem labelPolynomial_degree (a : Label) : (labelPolynomial a).totalDegree ≤ 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le ((lift_degree_le _).trans (base_labelPolynomial_degree a.1))
  exact (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C, zero_add] using errorPolynomial_degree a.2.1)

noncomputable def labelEquiv : Label ≃ Fin 16 := Fintype.equivFinOfCardEq label_count

noncomputable def indexedLabelPolynomial (a : Fin 16) : Poly :=
  labelPolynomial (labelEquiv.symm a)

theorem indexedLabelPolynomial_degree (a : Fin 16) :
    (indexedLabelPolynomial a).totalDegree ≤ 2 := labelPolynomial_degree _

theorem indexedMinimum_eq (z : Coord) :
    PolynomialSelection.minimum indexedLabelPolynomial z = minimum z := by
  apply le_antisymm
  · apply (PolynomialSelection.le_minimum_iff labelPolynomial z _).mpr
    intro a
    simpa only [indexedLabelPolynomial, Equiv.symm_apply_apply] using
      PolynomialSelection.minimum_le indexedLabelPolynomial z (labelEquiv a)
  · apply (PolynomialSelection.le_minimum_iff indexedLabelPolynomial z _).mpr
    intro a
    exact PolynomialSelection.minimum_le labelPolynomial z (labelEquiv.symm a)

theorem indexed_f_eq (z : Coord) :
    PolynomialSelection.f indexedLabelPolynomial orientationPolynomial z = f z := by
  simp only [PolynomialSelection.f, indexedMinimum_eq, f, minimum]

noncomputable def indexedSignPartition : FinitePolynomialSignPartition
    (PolynomialSelection.f indexedLabelPolynomial orientationPolynomial) 2 2 :=
  PolynomialSelection.signPartition indexedLabelPolynomial orientationPolynomial
    indexedLabelPolynomial_degree orientationPolynomial_degree

/-- One label of total degree at most two for each entire sign realization
of the 137 tests, on the unrestricted domain `Fin 8 → ℝ`. -/
noncomputable def signPartition : FinitePolynomialSignPartition f 2 2 where
  count := indexedSignPartition.count
  test := indexedSignPartition.test
  test_degree := indexedSignPartition.test_degree
  label := indexedSignPartition.label
  label_degree := indexedSignPartition.label_degree
  agrees s z hz := by
    rw [← indexed_f_eq]
    exact indexedSignPartition.agrees s z hz

theorem signPartition_count : signPartition.count = 137 :=
  PolynomialSelection.signTestIndex_card_sixteen

theorem signPartition_test_degree (i : Fin signPartition.count) :
    (signPartition.test i).totalDegree ≤ 2 := signPartition.test_degree i

theorem signPartition_label_degree (s : Fin signPartition.count → SignType) :
    (signPartition.label s).totalDegree ≤ 2 := signPartition.label_degree s

theorem agrees_on_entire_sign_realization (s : Fin signPartition.count → SignType)
    (z : Coord) (hz : ∀ i, SignType.sign (eval z (signPartition.test i)) = s i) :
    f z = eval z (signPartition.label s) := signPartition.agrees s z hz

end PBCounterexample.Quadratic8
