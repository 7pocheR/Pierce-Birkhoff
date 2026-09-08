import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-!
Polynomial lattice expressions use actual real multivariate polynomials and
only finitely many binary maximum and minimum operations.
-/

namespace PBCounterexample

inductive LatticeExpr (σ : Type*) where
  | leaf (p : MvPolynomial σ ℝ)
  | sup (a b : LatticeExpr σ)
  | inf (a b : LatticeExpr σ)

namespace LatticeExpr

noncomputable def eval {σ : Type*} : LatticeExpr σ → (σ → ℝ) → ℝ
  | .leaf p, z => MvPolynomial.eval z p
  | .sup a b, z => max (eval a z) (eval b z)
  | .inf a b, z => min (eval a z) (eval b z)

@[simp] theorem eval_leaf {σ : Type*} (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    (leaf p).eval z = MvPolynomial.eval z p := rfl

@[simp] theorem eval_sup {σ : Type*} (a b : LatticeExpr σ) (z : σ → ℝ) :
    (sup a b).eval z = max (a.eval z) (b.eval z) := rfl

@[simp] theorem eval_inf {σ : Type*} (a b : LatticeExpr σ) (z : σ → ℝ) :
    (inf a b).eval z = min (a.eval z) (b.eval z) := rfl

end LatticeExpr

def IsPolynomialLattice {σ : Type*} (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ e : LatticeExpr σ, ∀ z, e.eval z = f z

end PBCounterexample
