import gram5_independent_contract_20260908
import PBCounterexample.Gram5Main

/-!
Binding of the independently expanded five-dimensional specification to the
implementation's final roots.  All mathematical data on the specification side
come from `Gram5IndependentContract`, whose imports contain no Gram5 module.

The final declarations below have no separation, path-existence, finite-family,
or nonrepresentation hypotheses.  They use the implementation's actual theorems,
not assumptions of the corresponding independent contract propositions.
-/

noncomputable section

open MvPolynomial Gram5IndependentContract

namespace PBCounterexample.Gram5IndependentBinding

theorem coordinate_type_eq : Gram5.Coord = (Fin 5 → ℝ) := rfl

theorem polynomial_type_eq :
    Gram5.Poly = MvPolynomial (Fin 5) ℝ := rfl

/-- The four expanded labels agree as polynomials, including all cubic terms. -/
theorem labels_eq (i : Fin 4) : Gram5.qPolynomial i = labels i := by
  fin_cases i <;>
    norm_num [Gram5.qPolynomial, Gram5.gramA, Gram5.gramB,
      Gram5.gramE, Gram5.gramF, Gram5.invariantA, Gram5.invariantB,
      labels, q1, q2, q3, q4,
      Gram5.a, Gram5.b, Gram5.c, Gram5.d, Gram5.e,
      Gram5IndependentContract.a, Gram5IndependentContract.b,
      Gram5IndependentContract.c, Gram5IndependentContract.d,
      Gram5IndependentContract.e] <;> ring

/-- This is the signed determinant, not its square or absolute value. -/
theorem determinant_eq : Gram5.determinantPolynomial = determinant := by
  exact Gram5.determinantPolynomial_eq

theorem determinant_eval_eq (z : Point) :
    eval z determinant = (Gram5.positiveMatrix z).det := by
  rw [← determinant_eq]
  exact Gram5.eval_determinantPolynomial z

theorem minimum_le_label (z : Point) (i : Fin 4) :
    minimum z ≤ eval z (labels i) := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The implementation's indexed infimum is exactly the prescribed four-label
minimum, with no determinant or additional polynomial included in it. -/
theorem minimum_eq (z : Point) : Gram5.minimum z = minimum z := by
  have hq (i : Fin 4) : Gram5.minimum z ≤ eval z (labels i) := by
    simpa only [Gram5.q, labels_eq] using Gram5.minimum_le z i
  apply le_antisymm
  · exact le_min (le_min (hq 0) (hq 1)) (le_min (hq 2) (hq 3))
  · apply (Gram5.le_minimum_iff z (minimum z)).mpr
    intro i
    simpa only [Gram5.q, labels_eq] using minimum_le_label z i

theorem implementation_f_eq_selected : Gram5.f = selected := by
  funext z
  change (if 0 < Gram5.minimum z ∧
    0 < eval z Gram5.determinantPolynomial then Gram5.minimum z else 0) = selected z
  simp only [minimum_eq, determinant_eq, selected]

/-- Equality of the prescribed closed regions before their numeric indexing. -/
theorem region_eq (i : Option (Fin 4)) :
    PolynomialSelection.region Gram5.qPolynomial Gram5.determinantPolynomial i =
      region i := by
  cases i with
  | none =>
      change PolynomialSelection.zeroRegion Gram5.qPolynomial
        Gram5.determinantPolynomial = zeroRegion
      simp only [PolynomialSelection.zeroRegion, zeroRegion,
        labels_eq, determinant_eq]
  | some i =>
      ext z
      simp only [PolynomialSelection.region, PolynomialSelection.polynomialRegion,
        region, activeRegion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
        labels_eq, determinant_eq, and_assoc]

theorem label_eq (i : Option (Fin 4)) :
    PolynomialSelection.label Gram5.qPolynomial i = label i := by
  cases i with
  | none => rfl
  | some i => exact labels_eq i

/-- An explicit bijective indexing of the actual implementation cover.
No numeric ordering of its pieces is assumed. -/
def coverIndex (i : Option (Fin 4)) : Fin Gram5.polynomialCover.count :=
  Fintype.equivFin (Option (Fin 4)) i

theorem cover_region_eq (i : Option (Fin 4)) :
    Gram5.polynomialCover.region (coverIndex i) = region i := by
  change PolynomialSelection.region Gram5.qPolynomial Gram5.determinantPolynomial
    ((Fintype.equivFin (Option (Fin 4))).symm
      (Fintype.equivFin (Option (Fin 4)) i)) = region i
  rw [Equiv.symm_apply_apply]
  exact region_eq i

theorem cover_label_eq (i : Option (Fin 4)) :
    Gram5.polynomialCover.label (coverIndex i) = label i := by
  change PolynomialSelection.label Gram5.qPolynomial
    ((Fintype.equivFin (Option (Fin 4))).symm
      (Fintype.equivFin (Option (Fin 4)) i)) = label i
  rw [Equiv.symm_apply_apply]
  exact label_eq i

/-- Closedness, semialgebraicity, coverage and compatibility are all transported
from the implementation's actual cover; separation is not assumed here. -/
theorem explicit_cover_claim : ExplicitCoverClaim := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [← cover_region_eq i]
    exact Gram5.polynomialCover.closed (coverIndex i)
  · intro i
    rw [← cover_region_eq i]
    exact Gram5.polynomialCover.semialgebraic (coverIndex i)
  · intro z
    have hz : z ∈ ⋃ j, Gram5.polynomialCover.region j := by
      rw [Gram5.polynomialCover.covers]
      exact Set.mem_univ z
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    let i : Option (Fin 4) := (Fintype.equivFin (Option (Fin 4))).symm j
    have hindex : coverIndex i = j := by
      exact (Fintype.equivFin (Option (Fin 4))).apply_symm_apply j
    refine ⟨i, ?_⟩
    rw [← cover_region_eq i, hindex]
    exact hj
  · intro i z hz
    have hz' : z ∈ Gram5.polynomialCover.region (coverIndex i) := by
      rw [cover_region_eq i]
      exact hz
    have ha := Gram5.polynomialCover.agrees (coverIndex i) z hz'
    simpa only [implementation_f_eq_selected, cover_label_eq] using ha

theorem explicit_piece_count : Fintype.card (Option (Fin 4)) = 5 := by
  simp

/-- This bound concerns the five piece labels only.  No auxiliary polynomial
leaf in the nonrepresentation claims below is degree-restricted. -/
theorem explicit_labels_totalDegree (i : Option (Fin 4)) :
    (label i).totalDegree ≤ 3 := by
  have h := Gram5.whole_space_counterexample.2.2.1 (coverIndex i)
  simpa only [cover_label_eq] using h

theorem whole_space_claim : WholeSpaceClaim := by
  refine ⟨?_, explicit_cover_claim, ?_⟩
  · simpa only [implementation_f_eq_selected] using
      Gram5.whole_space_counterexample.1
  · simpa only [implementation_f_eq_selected] using
      Gram5.whole_space_counterexample.2.2.2

/-- The quantified finite family consists of arbitrary real polynomials in all
five coordinates, and the witnesses are actual whole-space points. -/
theorem finite_threshold_pair_claim : FiniteThresholdPairClaim := by
  intro S
  simpa only [implementation_f_eq_selected] using
    Gram5.exists_finite_threshold_pair S

theorem no_finite_lattice_expression (expr : LatticeExpr (Fin 5)) :
    ¬ (∀ z : Point, expr.eval z = selected z) := by
  intro heq
  exact whole_space_claim.2.2 ⟨expr, heq⟩

/-- Literal finite nonempty maximum-of-minima syntax with arbitrary real
polynomial leaves; neither a leaf-degree nor a coefficient restriction occurs. -/
theorem no_finite_sup_inf_polynomials {ι κ : Type*}
    (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial (Fin 5) ℝ) :
    ¬ (∀ z : Fin 5 → ℝ, selected z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => eval z (p i j)))) := by
  simpa only [implementation_f_eq_selected] using
    Gram5.not_finite_sup_inf_polynomials S hS T hT p

/-- One closed statement of the independently specified whole-space conclusion. -/
theorem independent_expanded_counterexample :
    Continuous selected ∧ ExplicitCoverClaim ∧
      (∀ i : Option (Fin 4), (label i).totalDegree ≤ 3) ∧
      ¬ (∃ expr : LatticeExpr (Fin 5), ∀ z : Point, expr.eval z = selected z) := by
  exact ⟨whole_space_claim.1, explicit_cover_claim, explicit_labels_totalDegree,
    whole_space_claim.2.2⟩

end PBCounterexample.Gram5IndependentBinding
