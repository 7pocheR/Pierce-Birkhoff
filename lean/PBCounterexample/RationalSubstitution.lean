import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Clearing a common denominator in polynomial substitution
-/

namespace PBCounterexample

open MvPolynomial

theorem polynomial_substitution_clear_denominator
    {σ τ : Type*} (p : MvPolynomial σ ℝ)
    (d : MvPolynomial τ ℝ) (n : σ → MvPolynomial τ ℝ) :
    ∃ q : MvPolynomial τ ℝ, ∃ k : ℕ,
      ∀ z : τ → ℝ, eval z d ≠ 0 →
        eval z q = (eval z d) ^ k * eval (fun i => eval z (n i) / eval z d) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨C c, 0, ?_⟩
    intro z _
    simp
  | add p r hp hr =>
    obtain ⟨q, k, hq⟩ := hp
    obtain ⟨s, l, hs⟩ := hr
    refine ⟨d ^ l * q + d ^ k * s, k + l, ?_⟩
    intro z hd
    simp only [map_add, map_mul, map_pow, hq z hd, hs z hd, pow_add]
    ring
  | mul_X p i hp =>
    obtain ⟨q, k, hq⟩ := hp
    refine ⟨q * n i, k + 1, ?_⟩
    intro z hd
    simp only [map_mul, eval_X, hq z hd, pow_succ]
    field_simp

end PBCounterexample
