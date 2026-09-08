import PBCounterexample.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite-leaf positive-threshold transfer

A one-sided implication for finitely many actual polynomial leaves transfers
to every binary minimum/maximum expression. No homogeneity or degree bound
is assumed.
-/

namespace PBCounterexample

variable {σ : Type*}

namespace LatticeExpr

theorem exists_finite_threshold_tests (e : LatticeExpr σ) :
    ∃ S : Finset (MvPolynomial σ ℝ), ∀ x y : σ → ℝ, ∀ r : ℝ,
      (∀ p ∈ S, r ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p) →
      r ≤ e.eval x → 0 < e.eval y := by
  classical
  induction e with
  | leaf p =>
    refine ⟨{p}, ?_⟩
    intro x y r hp hx
    exact hp p (Finset.mem_singleton_self p) hx
  | sup a b ha hb =>
    obtain ⟨S, hS⟩ := ha
    obtain ⟨T, hT⟩ := hb
    refine ⟨S ∪ T, ?_⟩
    intro x y r hp hx
    have hs : ∀ p ∈ S, r ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p :=
      fun p hmem => hp p (Finset.mem_union_left T hmem)
    have ht : ∀ p ∈ T, r ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p :=
      fun p hmem => hp p (Finset.mem_union_right S hmem)
    change r ≤ max (a.eval x) (b.eval x) at hx
    change 0 < max (a.eval y) (b.eval y)
    rcases le_max_iff.mp hx with hx | hx
    · exact lt_of_lt_of_le (hS x y r hs hx) (le_max_left _ _)
    · exact lt_of_lt_of_le (hT x y r ht hx) (le_max_right _ _)
  | inf a b ha hb =>
    obtain ⟨S, hS⟩ := ha
    obtain ⟨T, hT⟩ := hb
    refine ⟨S ∪ T, ?_⟩
    intro x y r hp hx
    have hs : ∀ p ∈ S, r ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p :=
      fun p hmem => hp p (Finset.mem_union_left T hmem)
    have ht : ∀ p ∈ T, r ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p :=
      fun p hmem => hp p (Finset.mem_union_right S hmem)
    change r ≤ min (a.eval x) (b.eval x) at hx
    change 0 < min (a.eval y) (b.eval y)
    exact lt_min (hS x y r hs (le_trans hx (min_le_left _ _)))
      (hT x y r ht (le_trans hx (min_le_right _ _)))

end LatticeExpr

/-- A finite-set threshold obstruction excludes every polynomial lattice
expression with arbitrary real polynomial leaves. -/
theorem not_isPolynomialLattice_of_finite_threshold_pairs
    (f : (σ → ℝ) → ℝ)
    (hpair : ∀ S : Finset (MvPolynomial σ ℝ),
      ∃ x y : σ → ℝ, 0 < f x ∧ f y = 0 ∧
        ∀ p ∈ S, f x ≤ MvPolynomial.eval x p → 0 < MvPolynomial.eval y p) :
    ¬ IsPolynomialLattice f := by
  rintro ⟨e, he⟩
  obtain ⟨S, hS⟩ := e.exists_finite_threshold_tests
  obtain ⟨x, y, _, hy, hp⟩ := hpair S
  have hpos : 0 < e.eval y := hS x y (f x) hp (le_of_eq (he x).symm)
  rw [he y, hy] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

end PBCounterexample
