import Mathlib

/-!
# Semialgebraic subsets of real coordinate spaces

A semialgebraic set is a finite Boolean combination of polynomial weak
inequalities. The definition applies to the full coordinate space.
-/

namespace PBCounterexample

open MvPolynomial

inductive IsSemialgebraic {σ : Type*} : Set (σ → ℝ) → Prop
  | polynomial_le (p : MvPolynomial σ ℝ) :
      IsSemialgebraic {z | eval z p ≤ 0}
  | compl {s} : IsSemialgebraic s → IsSemialgebraic sᶜ
  | union {s t} : IsSemialgebraic s → IsSemialgebraic t → IsSemialgebraic (s ∪ t)
  | inter {s t} : IsSemialgebraic s → IsSemialgebraic t → IsSemialgebraic (s ∩ t)

namespace IsSemialgebraic

variable {σ ι : Type*}

theorem univ : IsSemialgebraic (Set.univ : Set (σ → ℝ)) := by
  simpa using polynomial_le (0 : MvPolynomial σ ℝ)

theorem empty : IsSemialgebraic (∅ : Set (σ → ℝ)) := by
  simpa using (univ (σ := σ)).compl

theorem le (p q : MvPolynomial σ ℝ) :
    IsSemialgebraic {z | eval z p ≤ eval z q} := by
  simpa only [map_sub, sub_nonpos] using polynomial_le (p - q)

theorem ge_zero (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {z | 0 ≤ eval z p} := by
  simpa using le (0 : MvPolynomial σ ℝ) p

theorem finset_union (s : Finset ι) (S : ι → Set (σ → ℝ))
    (hS : ∀ i ∈ s, IsSemialgebraic (S i)) :
    IsSemialgebraic (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty (σ := σ))
  | @insert i s hi ih =>
      simpa only [Finset.set_biUnion_insert] using
        (hS i (Finset.mem_insert_self i s)).union
          (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

theorem finset_inter (s : Finset ι) (S : ι → Set (σ → ℝ))
    (hS : ∀ i ∈ s, IsSemialgebraic (S i)) :
    IsSemialgebraic (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (univ (σ := σ))
  | @insert i s hi ih =>
      simpa only [Finset.set_biInter_insert] using
        (hS i (Finset.mem_insert_self i s)).inter
          (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

theorem iUnion [Fintype ι] (S : ι → Set (σ → ℝ))
    (hS : ∀ i, IsSemialgebraic (S i)) : IsSemialgebraic (⋃ i, S i) := by
  simpa using finset_union Finset.univ S (fun i _ => hS i)

theorem iInter [Fintype ι] (S : ι → Set (σ → ℝ))
    (hS : ∀ i, IsSemialgebraic (S i)) : IsSemialgebraic (⋂ i, S i) := by
  simpa using finset_inter Finset.univ S (fun i _ => hS i)

end IsSemialgebraic

/-- A finite cover of the entire real coordinate space by closed semialgebraic
sets, with a polynomial agreeing with the function on each set. -/
structure FiniteClosedPolynomialCover {σ : Type*} (f : (σ → ℝ) → ℝ) where
  count : ℕ
  region : Fin count → Set (σ → ℝ)
  label : Fin count → MvPolynomial σ ℝ
  closed : ∀ i, IsClosed (region i)
  semialgebraic : ∀ i, IsSemialgebraic (region i)
  covers : ⋃ i, region i = Set.univ
  agrees : ∀ i z, z ∈ region i → f z = eval z (label i)

theorem FiniteClosedPolynomialCover.continuous {σ : Type*}
    {f : (σ → ℝ) → ℝ} (C : FiniteClosedPolynomialCover f) : Continuous f := by
  apply (locallyFinite_of_finite C.region).continuous C.covers C.closed
  intro i
  exact (MvPolynomial.continuous_eval (C.label i)).continuousOn.congr
    (fun z hz => C.agrees i z hz)

end PBCounterexample
