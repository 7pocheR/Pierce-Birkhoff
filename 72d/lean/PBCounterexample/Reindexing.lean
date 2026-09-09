import PBCounterexample.Basic
import PBCounterexample.Semialgebraic
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Changes of coordinate indices
-/

namespace PBCounterexample

variable {σ τ : Type*}

namespace LatticeExpr

noncomputable def rename (r : σ → τ) : LatticeExpr σ → LatticeExpr τ
  | .leaf p => .leaf (MvPolynomial.rename r p)
  | .sup a b => .sup (rename r a) (rename r b)
  | .inf a b => .inf (rename r a) (rename r b)

theorem eval_rename (r : σ → τ) (e : LatticeExpr σ) (z : τ → ℝ) :
    (e.rename r).eval z = e.eval (fun i => z (r i)) := by
  induction e with
  | leaf p => simp [rename, eval, MvPolynomial.eval_rename, _root_.Function.comp_def]
  | sup a b ha hb => simp [rename, eval, ha, hb]
  | inf a b ha hb => simp [rename, eval, ha, hb]

end LatticeExpr

theorem IsPolynomialLattice.precomp_coordinates
    {f : (σ → ℝ) → ℝ} (hf : IsPolynomialLattice f) (r : σ → τ) :
    IsPolynomialLattice (fun z : τ → ℝ => f (fun i => z (r i))) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e.rename r, fun z => (e.eval_rename r z).trans (he _)⟩

theorem polynomial_lattice_precomp_equiv_iff
    (f : (σ → ℝ) → ℝ) (e : σ ≃ τ) :
    IsPolynomialLattice (fun z : τ → ℝ => f (fun i => z (e i))) ↔
      IsPolynomialLattice f := by
  refine ⟨?_, fun hf => hf.precomp_coordinates e⟩
  intro hf
  simpa only [Equiv.symm_apply_apply] using hf.precomp_coordinates e.symm

theorem IsSemialgebraic.preimage_coordinates
    {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) (r : σ → τ) :
    IsSemialgebraic ((fun z : τ → ℝ => fun i => z (r i)) ⁻¹' s) := by
  induction hs with
  | polynomial_le p =>
    simpa only [Set.preimage_ofPred_eq, MvPolynomial.eval_rename, _root_.Function.comp_def] using
      IsSemialgebraic.polynomial_le (MvPolynomial.rename r p)
  | compl hs ih => exact ih.compl
  | union hs ht ihs iht => exact ihs.union iht
  | inter hs ht ihs iht => exact ihs.inter iht

noncomputable def FiniteClosedPolynomialCover.precomp_coordinates
    {f : (σ → ℝ) → ℝ} (C : FiniteClosedPolynomialCover f) (r : σ → τ) :
    FiniteClosedPolynomialCover (fun z : τ → ℝ => f (fun i => z (r i))) where
  count := C.count
  region i := (fun z : τ → ℝ => fun j => z (r j)) ⁻¹' C.region i
  label i := MvPolynomial.rename r (C.label i)
  closed i := (C.closed i).preimage (by fun_prop)
  semialgebraic i := (C.semialgebraic i).preimage_coordinates r
  covers := by
    rw [← Set.preimage_iUnion, C.covers, Set.preimage_univ]
  agrees i z hz := by
    rw [MvPolynomial.eval_rename]
    exact C.agrees i _ hz

end PBCounterexample
