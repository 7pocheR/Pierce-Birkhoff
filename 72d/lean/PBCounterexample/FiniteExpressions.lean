import PBCounterexample.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite maxima and minima of polynomial lattice functions

Nonempty finite pointwise maxima and minima are represented by the same binary
lattice-expression syntax. In particular, the usual finite maximum of finite
minima of arbitrary real polynomials is a polynomial lattice function.
-/

namespace PBCounterexample

variable {σ ι κ : Type*}

theorem polynomial_isPolynomialLattice (p : MvPolynomial σ ℝ) :
    IsPolynomialLattice (fun z => MvPolynomial.eval z p) :=
  ⟨.leaf p, fun _ => rfl⟩

namespace IsPolynomialLattice

theorem max {f g : (σ → ℝ) → ℝ} (hf : IsPolynomialLattice f) (hg : IsPolynomialLattice g) :
    IsPolynomialLattice (fun z => max (f z) (g z)) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨.sup a b, fun z => by simp only [LatticeExpr.eval_sup, ha, hb]⟩

theorem min {f g : (σ → ℝ) → ℝ} (hf : IsPolynomialLattice f) (hg : IsPolynomialLattice g) :
    IsPolynomialLattice (fun z => min (f z) (g z)) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨.inf a b, fun z => by simp only [LatticeExpr.eval_inf, ha, hb]⟩

theorem finite_sup (S : Finset ι) (hS : S.Nonempty) (f : ι → (σ → ℝ) → ℝ)
    (hf : ∀ i ∈ S, IsPolynomialLattice (f i)) :
    IsPolynomialLattice (fun z => S.sup' hS (fun i => f i z)) := by
  have h : IsPolynomialLattice (S.sup' hS f) :=
    Finset.sup'_induction hS f (fun _ ha _ hb => ha.max hb) hf
  have heq : S.sup' hS f = (fun z => S.sup' hS (fun i => f i z)) :=
    funext (Finset.sup'_apply hS f)
  exact heq ▸ h

theorem finite_inf (S : Finset ι) (hS : S.Nonempty) (f : ι → (σ → ℝ) → ℝ)
    (hf : ∀ i ∈ S, IsPolynomialLattice (f i)) :
    IsPolynomialLattice (fun z => S.inf' hS (fun i => f i z)) := by
  have h : IsPolynomialLattice (S.inf' hS f) :=
    Finset.inf'_induction hS f (fun _ ha _ hb => ha.min hb) hf
  have heq : S.inf' hS f = (fun z => S.inf' hS (fun i => f i z)) :=
    funext (Finset.inf'_apply hS f)
  exact heq ▸ h

end IsPolynomialLattice

/-- Ordinary finite maxima of nonempty finite minima of arbitrary real
polynomials are represented by finite binary polynomial lattice expressions. -/
theorem finite_sup_inf_polynomials_isPolynomialLattice
    (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → MvPolynomial σ ℝ) :
    IsPolynomialLattice (fun z =>
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => MvPolynomial.eval z (p i j)))) := by
  apply IsPolynomialLattice.finite_sup
  intro i _
  apply IsPolynomialLattice.finite_inf
  intro j _
  exact polynomial_isPolynomialLattice (p i j)

end PBCounterexample
