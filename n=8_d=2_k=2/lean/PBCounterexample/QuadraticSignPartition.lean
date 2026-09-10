import PBCounterexample.PolynomialSelection
import Mathlib.Data.Sign.Basic

/-!
# Polynomial labels on entire realizations of finitely many polynomial signs

The regions here are exact ternary sign realizations in the whole coordinate
space. A single label agrees on every point of a realization, regardless of its
connected components. Degree means ordinary multivariate total degree.
-/

namespace PBCounterexample

open MvPolynomial

/-- A polynomial label for each entire ternary sign realization. Empty
realizations also receive a label, with a vacuous agreement condition. -/
structure FinitePolynomialSignPartition {σ : Type*} (f : (σ → ℝ) → ℝ)
    (partitionDegree pieceDegree : ℕ) where
  count : ℕ
  test : Fin count → MvPolynomial σ ℝ
  test_degree : ∀ i, (test i).totalDegree ≤ partitionDegree
  label : (Fin count → SignType) → MvPolynomial σ ℝ
  label_degree : ∀ s, (label s).totalDegree ≤ pieceDegree
  agrees : ∀ s z, (∀ i, SignType.sign (eval z (test i)) = s i) →
    f z = eval z (label s)

namespace FinitePolynomialSignPartition

variable {σ : Type*} {f : (σ → ℝ) → ℝ} {partitionDegree pieceDegree : ℕ}
variable (P : FinitePolynomialSignPartition f partitionDegree pieceDegree)

def realization (s : Fin P.count → SignType) : Set (σ → ℝ) :=
  {z | ∀ i, SignType.sign (eval z (P.test i)) = s i}

theorem realization_covers (z : σ → ℝ) : ∃ s, z ∈ P.realization s :=
  ⟨fun i => SignType.sign (eval z (P.test i)), fun _ => rfl⟩

theorem realization_disjoint {s t : Fin P.count → SignType} (hst : s ≠ t) :
    Disjoint (P.realization s) (P.realization t) := by
  rw [Set.disjoint_left]
  intro z hz hs
  exact hst (funext fun i => (hz i).symm.trans (hs i))

theorem agrees_on_entire_realization (s : Fin P.count → SignType) :
    ∀ z ∈ P.realization s, f z = eval z (P.label s) := P.agrees s

theorem semialgebraic_realization (s : Fin P.count → SignType) :
    IsSemialgebraic (P.realization s) := by
  have hi (i : Fin P.count) :
      IsSemialgebraic {z | SignType.sign (eval z (P.test i)) = s i} := by
    cases hs : s i with
    | zero =>
        simpa only [hs, SignType.zero_eq_zero, le_antisymm_iff,
          sign_nonpos_iff, sign_nonneg_iff, Set.ofPred_and] using
          (IsSemialgebraic.polynomial_le (P.test i)).inter
            (IsSemialgebraic.ge_zero (P.test i))
    | neg =>
        simpa only [hs, SignType.neg_eq_neg_one, sign_eq_neg_one_iff,
          Set.compl_ofPred, not_le] using (IsSemialgebraic.ge_zero (P.test i)).compl
    | pos =>
        simpa only [hs, SignType.pos_eq_one, sign_eq_one_iff,
          Set.compl_ofPred, not_le] using (IsSemialgebraic.polynomial_le (P.test i)).compl
  simpa only [realization, Set.ofPred_forall] using IsSemialgebraic.iInter _ hi

end FinitePolynomialSignPartition

namespace PolynomialSelection

variable {σ : Type*} {n : ℕ}
variable (Q : Fin n → MvPolynomial σ ℝ) (d : MvPolynomial σ ℝ)

/-- The orientation, the labels, and one difference for each unordered pair. -/
abbrev SignTestIndex (n : ℕ) :=
  Unit ⊕ (Fin n ⊕ {ij : Fin n × Fin n // ij.1 < ij.2})

noncomputable def signTest : SignTestIndex n → MvPolynomial σ ℝ
  | .inl _ => d
  | .inr (.inl a) => Q a
  | .inr (.inr ab) => Q ab.val.1 - Q ab.val.2

theorem signTest_degree {k : ℕ} (hQ : ∀ a, (Q a).totalDegree ≤ k)
    (hd : d.totalDegree ≤ k) (i : SignTestIndex n) :
    (signTest Q d i).totalDegree ≤ k := by
  rcases i with _ | (a | ab)
  · exact hd
  · exact hQ a
  · exact (totalDegree_sub _ _).trans (max_le (hQ _) (hQ _))

variable [Nonempty (Fin n)]

private theorem minimum_positive_iff (z : σ → ℝ) :
    0 < minimum Q z ↔ ∀ a, 0 < eval z (Q a) := by
  constructor
  · intro h a
    exact lt_of_lt_of_le h (minimum_le Q z a)
  · intro h
    obtain ⟨a, ha⟩ := exists_minimum_eq Q z
    rw [ha]
    exact h a

private theorem active_iff_of_same_signs {x y : σ → ℝ}
    (hs : ∀ i, SignType.sign (eval x (signTest Q d i)) =
      SignType.sign (eval y (signTest Q d i))) :
    (0 < minimum Q x ∧ 0 < eval x d) ↔
      (0 < minimum Q y ∧ 0 < eval y d) := by
  have hQ (a : Fin n) : (0 < eval x (Q a)) ↔ 0 < eval y (Q a) := by
    rw [← sign_eq_one_iff, ← sign_eq_one_iff]
    have h := hs (.inr (.inl a))
    change SignType.sign (eval x (Q a)) = SignType.sign (eval y (Q a)) at h
    rw [h]
  have hd : (0 < eval x d) ↔ 0 < eval y d := by
    rw [← sign_eq_one_iff, ← sign_eq_one_iff]
    have h := hs (.inl ())
    change SignType.sign (eval x d) = SignType.sign (eval y d) at h
    rw [h]
  rw [minimum_positive_iff, minimum_positive_iff]
  exact and_congr (forall_congr' hQ) hd

omit [Nonempty (Fin n)] in
private theorem comparison_iff_of_same_signs {x y : σ → ℝ}
    (hs : ∀ i, SignType.sign (eval x (signTest Q d i)) =
      SignType.sign (eval y (signTest Q d i))) (a b : Fin n) :
    (eval x (Q a) ≤ eval x (Q b)) ↔ eval y (Q a) ≤ eval y (Q b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := hs (.inr (.inr ⟨(a, b), hab⟩))
    change SignType.sign (eval x (Q a - Q b)) =
      SignType.sign (eval y (Q a - Q b)) at h
    have hh : (SignType.sign (eval x (Q a - Q b)) ≤ 0) ↔
        SignType.sign (eval y (Q a - Q b)) ≤ 0 := by rw [h]
    simpa only [map_sub, sign_nonpos_iff, sub_nonpos] using hh
  · subst b
    simp
  · have h := hs (.inr (.inr ⟨(b, a), hab⟩))
    change SignType.sign (eval x (Q b - Q a)) =
      SignType.sign (eval y (Q b - Q a)) at h
    have hh : (0 ≤ SignType.sign (eval x (Q b - Q a))) ↔
        0 ≤ SignType.sign (eval y (Q b - Q a)) := by rw [h]
    simpa only [map_sub, sign_nonneg_iff, sub_nonneg] using hh

theorem exists_label_for_same_signs (x : σ → ℝ) :
    ∃ a : Option (Fin n), ∀ y,
      (∀ i, SignType.sign (eval x (signTest Q d i)) =
        SignType.sign (eval y (signTest Q d i))) →
      f Q d y = eval y (label Q a) := by
  classical
  by_cases hx : 0 < minimum Q x ∧ 0 < eval x d
  · obtain ⟨a, ha⟩ := exists_minimum_eq Q x
    refine ⟨some a, ?_⟩
    intro y hs
    have hy := (active_iff_of_same_signs Q d hs).mp hx
    have hm : minimum Q y = eval y (Q a) := by
      apply le_antisymm (minimum_le Q y a)
      apply (le_minimum_iff Q y _).mpr
      intro b
      apply (comparison_iff_of_same_signs Q d hs a b).mp
      rw [← ha]
      exact minimum_le Q x b
    simpa only [f, ite_eq_left hy, label] using hm
  · refine ⟨none, ?_⟩
    intro y hs
    have hy : ¬ (0 < minimum Q y ∧ 0 < eval y d) :=
      fun hy => hx ((active_iff_of_same_signs Q d hs).mpr hy)
    simp only [f, ite_eq_right hy, label, map_zero]

theorem exists_label_for_sign_realization (s : SignTestIndex n → SignType) :
    ∃ a : Option (Fin n), ∀ z,
      (∀ i, SignType.sign (eval z (signTest Q d i)) = s i) →
      f Q d z = eval z (label Q a) := by
  classical
  by_cases h : ∃ x, ∀ i, SignType.sign (eval x (signTest Q d i)) = s i
  · obtain ⟨x, hx⟩ := h
    obtain ⟨a, ha⟩ := exists_label_for_same_signs Q d x
    refine ⟨a, ?_⟩
    intro z hz
    exact ha z (fun i => (hx i).trans (hz i).symm)
  · exact ⟨none, fun z hz => (h ⟨z, hz⟩).elim⟩

noncomputable def signPartition {k : ℕ} (hQ : ∀ a, (Q a).totalDegree ≤ k)
    (hd : d.totalDegree ≤ k) : FinitePolynomialSignPartition (f Q d) k k where
  count := Fintype.card (SignTestIndex n)
  test i := signTest Q d ((Fintype.equivFin (SignTestIndex n)).symm i)
  test_degree i := signTest_degree Q d hQ hd _
  label s := label Q (Classical.choose (exists_label_for_sign_realization Q d
    (fun i => s (Fintype.equivFin (SignTestIndex n) i))))
  label_degree s := by
    cases Classical.choose (exists_label_for_sign_realization Q d
      (fun i => s (Fintype.equivFin (SignTestIndex n) i))) with
    | none => simp [label]
    | some a => exact hQ a
  agrees s z hz := by
    apply Classical.choose_spec (exists_label_for_sign_realization Q d
      (fun i => s (Fintype.equivFin (SignTestIndex n) i))) z
    intro i
    simpa only [Equiv.symm_apply_apply] using hz (Fintype.equivFin (SignTestIndex n) i)

set_option maxRecDepth 20000 in
theorem signTestIndex_card_sixteen : Fintype.card (SignTestIndex 16) = 137 := by decide

end PolynomialSelection

end PBCounterexample
