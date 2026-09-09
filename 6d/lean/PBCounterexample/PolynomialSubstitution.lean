import PBCounterexample.Basic
import PBCounterexample.Semialgebraic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Polynomial substitutions preserve lattice expressions and closed polynomial covers. -/

namespace PBCounterexample

variable {σ τ : Type*}

@[simp] theorem eval_polynomial_substitution
    (s : σ → MvPolynomial τ ℝ) (p : MvPolynomial σ ℝ) (z : τ → ℝ) :
    MvPolynomial.eval z (MvPolynomial.bind₁ s p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval z (s i)) p :=
  MvPolynomial.eval₂Hom_bind₁ _ _ _ _

namespace LatticeExpr

noncomputable def substitute (s : σ → MvPolynomial τ ℝ) : LatticeExpr σ → LatticeExpr τ
  | .leaf p => .leaf (MvPolynomial.bind₁ s p)
  | .sup a b => .sup (substitute s a) (substitute s b)
  | .inf a b => .inf (substitute s a) (substitute s b)

theorem eval_substitute (s : σ → MvPolynomial τ ℝ) (e : LatticeExpr σ) (z : τ → ℝ) :
    (e.substitute s).eval z = e.eval (fun i => MvPolynomial.eval z (s i)) := by
  induction e with
  | leaf p => simp [substitute, eval]
  | sup a b ha hb => simp [substitute, eval, ha, hb]
  | inf a b ha hb => simp [substitute, eval, ha, hb]

end LatticeExpr

theorem IsPolynomialLattice.precomp_polynomials
    {f : (σ → ℝ) → ℝ} (hf : IsPolynomialLattice f) (s : σ → MvPolynomial τ ℝ) :
    IsPolynomialLattice (fun z : τ → ℝ => f (fun i => MvPolynomial.eval z (s i))) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e.substitute s, fun z => (e.eval_substitute s z).trans (he _)⟩

theorem IsSemialgebraic.preimage_polynomials
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) (s : σ → MvPolynomial τ ℝ) :
    IsSemialgebraic ((fun z : τ → ℝ => fun i => MvPolynomial.eval z (s i)) ⁻¹' S) := by
  induction hS with
  | polynomial_le p =>
    simpa only [Set.preimage_ofPred_eq, eval_polynomial_substitution] using
      IsSemialgebraic.polynomial_le (MvPolynomial.bind₁ s p)
  | compl h ih => exact ih.compl
  | union h k ih ik => exact ih.union ik
  | inter h k ih ik => exact ih.inter ik

noncomputable def FiniteClosedPolynomialCover.precomp_polynomials
    {f : (σ → ℝ) → ℝ} (C : FiniteClosedPolynomialCover f) (s : σ → MvPolynomial τ ℝ) :
    FiniteClosedPolynomialCover
      (fun z : τ → ℝ => f (fun i => MvPolynomial.eval z (s i))) where
  count := C.count
  region i := (fun z : τ → ℝ => fun j => MvPolynomial.eval z (s j)) ⁻¹' C.region i
  label i := MvPolynomial.bind₁ s (C.label i)
  closed i := (C.closed i).preimage (continuous_pi fun j => MvPolynomial.continuous_eval (s j))
  semialgebraic i := (C.semialgebraic i).preimage_polynomials s
  covers := by rw [← Set.preimage_iUnion, C.covers, Set.preimage_univ]
  agrees i z hz := by
    rw [eval_polynomial_substitution]
    exact C.agrees i _ hz

theorem homogeneous_polynomial_substitution
    (s : σ → MvPolynomial τ ℝ) {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hs : ∀ i, (s i).IsHomogeneous 1) :
    (MvPolynomial.bind₁ s p).IsHomogeneous d := by
  rw [← MvPolynomial.aeval_eq_bind₁]
  simpa only [one_mul] using hp.aeval s hs

end PBCounterexample
