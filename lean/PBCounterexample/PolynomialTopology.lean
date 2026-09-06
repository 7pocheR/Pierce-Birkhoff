import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Basic

/-!
# Nonvanishing of real polynomials on open sets

A nonzero real polynomial in finitely many variables cannot vanish on a
nonempty open set. Consequently any finite family of nonzero polynomials has
a common nonvanishing point in each nonempty open set.
-/

namespace PBCounterexample

open MvPolynomial

variable {σ : Type*} [Finite σ]

theorem polynomial_eq_zero_of_vanishes_on_open
    {p : MvPolynomial σ ℝ} {s : Set (σ → ℝ)}
    (hs : IsOpen s) (hne : s.Nonempty)
    (hp : ∀ z ∈ s, eval z p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hs x hx
  apply MvPolynomial.funext_set u
    (fun i => infinite_of_mem_nhds (x i) ((hu i).1.mem_nhds (hu i).2))
  intro z hz
  simpa only [map_zero] using hp z (hsub hz)

theorem exists_eval_ne_zero_in_open
    {p : MvPolynomial σ ℝ} (hp : p ≠ 0)
    {s : Set (σ → ℝ)} (hs : IsOpen s) (hne : s.Nonempty) :
    ∃ z ∈ s, eval z p ≠ 0 := by
  classical
  by_contra h
  apply hp
  apply polynomial_eq_zero_of_vanishes_on_open hs hne
  intro z hz
  by_contra hzero
  exact h ⟨z, hz, hzero⟩

theorem exists_all_evals_ne_zero_in_open
    {ι : Type*} (S : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ S, p i ≠ 0)
    {s : Set (σ → ℝ)} (hs : IsOpen s) (hne : s.Nonempty) :
    ∃ z ∈ s, ∀ i ∈ S, eval z (p i) ≠ 0 := by
  classical
  have hprod : (∏ i ∈ S, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨z, hz, hval⟩ := exists_eval_ne_zero_in_open hprod hs hne
  refine ⟨z, hz, ?_⟩
  have heval : (∏ i ∈ S, eval z (p i)) ≠ 0 := by
    simpa only [map_prod] using hval
  exact Finset.prod_ne_zero_iff.mp heval

end PBCounterexample
