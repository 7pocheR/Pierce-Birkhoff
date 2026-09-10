import PBCounterexample.Gram6Main
import PBCounterexample.PolynomialSubstitution
import Mathlib.Algebra.MvPolynomial.Rename

/-! The eight independent coordinates, sixteen quadratic labels, and exact polynomial pullback. -/

namespace PBCounterexample.Quadratic8

open MvPolynomial

abbrev Coord := Fin 8 → ℝ
abbrev Poly := MvPolynomial (Fin 8) ℝ
abbrev Label := Fin 4 × Fin 2 × Bool

def baseIndex (i : Fin 6) : Fin 8 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

def baseProjection (z : Coord) : Gram6.Coord := fun i => z (baseIndex i)

noncomputable def lift (p : MvPolynomial (Fin 6) ℝ) : Poly := rename baseIndex p

@[simp] theorem eval_lift (z : Coord) (p : MvPolynomial (Fin 6) ℝ) :
    eval z (lift p) = eval (baseProjection z) p := by
  rw [lift, MvPolynomial.eval_rename]
  rfl

noncomputable def cofactor1 : MvPolynomial (Fin 6) ℝ :=
  X 0 * (-X 4 + C (1 / 2) * X 5) + X 1 * (X 2 + X 3)

noncomputable def cofactor2 : MvPolynomial (Fin 6) ℝ := -((X 0)^2 + (X 1)^2)

@[simp] theorem eval_cofactor1 (w : Gram6.Coord) :
    eval w cofactor1 = w 0 * (-w 4 + w 5 / 2) + w 1 * (w 2 + w 3) := by
  simp only [cofactor1, map_add, map_mul, map_neg, eval_X, eval_C]
  ring

@[simp] theorem eval_cofactor2 (w : Gram6.Coord) :
    eval w cofactor2 = -((w 0)^2 + (w 1)^2) := by simp [cofactor2]

theorem determinant_cofactor_expansion (w : Gram6.Coord) :
    eval w Gram6.determinantPolynomial =
      w 2 * eval w cofactor1 + (w 5 / 2) * eval w cofactor2 := by
  rw [Gram6.eval_determinantPolynomial, eval_cofactor1, eval_cofactor2]
  norm_num [Gram6.aMatrix, Matrix.det_fin_three, Matrix.cons_val,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

noncomputable def errorPolynomial : Fin 2 → Poly := ![
  X 6 - lift cofactor1, X 7 - lift cofactor2]

noncomputable def orientationPolynomial : Poly :=
  X 2 * X 6 + C (1 / 2) * (X 5 * X 7)

@[simp] theorem eval_errorPolynomial_zero (z : Coord) :
    eval z (errorPolynomial 0) = z 6 - eval (baseProjection z) cofactor1 := by
  simp [errorPolynomial]

@[simp] theorem eval_errorPolynomial_one (z : Coord) :
    eval z (errorPolynomial 1) = z 7 - eval (baseProjection z) cofactor2 := by
  simp [errorPolynomial]

@[simp] theorem eval_orientationPolynomial (z : Coord) :
    eval z orientationPolynomial = z 2 * z 6 + (z 5 / 2) * z 7 := by
  simp only [orientationPolynomial, map_add, map_mul, eval_X, eval_C]
  ring

noncomputable def labelPolynomial (a : Label) : Poly :=
  lift (Gram6.labelPolynomial a.1) +
    C (if a.2.2 then 8 else -8) * errorPolynomial a.2.1

@[simp] theorem eval_labelPolynomial (z : Coord) (a : Label) :
    eval z (labelPolynomial a) = eval (baseProjection z) (Gram6.labelPolynomial a.1) +
      (if a.2.2 then 8 else -8) * eval z (errorPolynomial a.2.1) := by
  simp [labelPolynomial]

noncomputable def minimum (z : Coord) : ℝ := PolynomialSelection.minimum labelPolynomial z

noncomputable def f (z : Coord) : ℝ :=
  PolynomialSelection.f labelPolynomial orientationPolynomial z

theorem f_bounds (z : Coord) : 0 ≤ f z ∧ f z ≤ max (minimum z) 0 := by
  unfold f PolynomialSelection.f
  split_ifs with h
  · exact ⟨le_of_lt h.1, le_max_left _ _⟩
  · exact ⟨le_rfl, le_max_right _ _⟩

theorem label_count : Fintype.card Label = 16 := by decide

def baseLabel (j : Fin 4) : Gram6.Label :=
  ⟨Gram6.fourEdges j, by fin_cases j <;> decide⟩

theorem qPolynomial_baseLabel (j : Fin 4) :
    Gram6.qPolynomial (baseLabel j) = Gram6.labelPolynomial j :=
  Gram6.allQuadratics_fourEdges j

theorem base_minimum_le_labelPolynomial (w : Gram6.Coord) (j : Fin 4) :
    Gram6.minimum w ≤ eval w (Gram6.labelPolynomial j) := by
  rw [← qPolynomial_baseLabel]
  exact PolynomialSelection.minimum_le Gram6.qPolynomial w (baseLabel j)

theorem exists_base_minimum_eq (w : Gram6.Coord) :
    ∃ j : Fin 4, Gram6.minimum w = eval w (Gram6.labelPolynomial j) := by
  obtain ⟨a, ha⟩ := PolynomialSelection.exists_minimum_eq Gram6.qPolynomial w
  obtain ⟨j, hj⟩ := Gram6.fourEdges_covers a
  refine ⟨j, ?_⟩
  change PolynomialSelection.minimum Gram6.qPolynomial w = _
  rw [ha, ← Gram6.allQuadratics_fourEdges, hj]
  rfl

theorem minimum_le_labelPolynomial (z : Coord) (a : Label) :
    minimum z ≤ eval z (labelPolynomial a) :=
  PolynomialSelection.minimum_le labelPolynomial z a

theorem minimum_le_base_sub_abs_error (z : Coord) (k : Fin 2) :
    minimum z ≤ Gram6.minimum (baseProjection z) - 8 * |eval z (errorPolynomial k)| := by
  obtain ⟨j, hj⟩ := exists_base_minimum_eq (baseProjection z)
  have hp := minimum_le_labelPolynomial z (j, k, true)
  have hn := minimum_le_labelPolynomial z (j, k, false)
  simp only [eval_labelPolynomial, Bool.false_eq_true, ↓reduceIte] at hp hn
  rw [← hj] at hp hn
  rcases le_total 0 (eval z (errorPolynomial k)) with he | he
  · rw [abs_of_nonneg he]
    linarith
  · rw [abs_of_nonpos he]
    linarith

theorem minimum_eq (z : Coord) :
    minimum z = Gram6.minimum (baseProjection z) -
      8 * max |eval z (errorPolynomial 0)| |eval z (errorPolynomial 1)| := by
  apply le_antisymm
  · rcases le_total |eval z (errorPolynomial 0)| |eval z (errorPolynomial 1)| with he | he
    · rw [max_eq_right he]
      exact minimum_le_base_sub_abs_error z 1
    · rw [max_eq_left he]
      exact minimum_le_base_sub_abs_error z 0
  · apply (PolynomialSelection.le_minimum_iff labelPolynomial z _).mpr
    rintro ⟨j, k, b⟩
    have hq := base_minimum_le_labelPolynomial (baseProjection z) j
    have hk : |eval z (errorPolynomial k)| ≤
        max |eval z (errorPolynomial 0)| |eval z (errorPolynomial 1)| := by
      fin_cases k
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hp := le_abs_self (eval z (errorPolynomial k))
    have hn := neg_abs_le (eval z (errorPolynomial k))
    rw [eval_labelPolynomial]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem minimum_le_base_minimum (z : Coord) :
    minimum z ≤ Gram6.minimum (baseProjection z) := by
  have h := minimum_le_base_sub_abs_error z 0
  have he := abs_nonneg (eval z (errorPolynomial 0))
  linarith

theorem base_minimum_pos {z : Coord} (hz : 0 < minimum z) :
    0 < Gram6.minimum (baseProjection z) :=
  lt_of_lt_of_le hz (minimum_le_base_minimum z)

theorem abs_error_lt_of_minimum_pos {z : Coord} (hz : 0 < minimum z) (k : Fin 2) :
    |eval z (errorPolynomial k)| < Gram6.minimum (baseProjection z) / 8 := by
  have h := minimum_le_base_sub_abs_error z k
  linarith

noncomputable def graphPolynomial : Fin 8 → MvPolynomial (Fin 6) ℝ :=
  ![X 0, X 1, X 2, X 3, X 4, X 5, cofactor1, cofactor2]

noncomputable def graph (w : Gram6.Coord) : Coord := fun i => eval w (graphPolynomial i)

@[simp] theorem baseProjection_graph (w : Gram6.Coord) : baseProjection (graph w) = w := by
  funext i
  fin_cases i <;> simp [baseProjection, baseIndex, graph, graphPolynomial]

@[simp] theorem eval_errorPolynomial_graph (w : Gram6.Coord) (k : Fin 2) :
    eval (graph w) (errorPolynomial k) = 0 := by
  fin_cases k
  · change eval (graph w) (errorPolynomial 0) = 0
    rw [eval_errorPolynomial_zero, baseProjection_graph]
    simp [graph, graphPolynomial]
  · change eval (graph w) (errorPolynomial 1) = 0
    rw [eval_errorPolynomial_one, baseProjection_graph]
    simp [graph, graphPolynomial]

@[simp] theorem eval_orientationPolynomial_graph (w : Gram6.Coord) :
    eval (graph w) orientationPolynomial = eval w Gram6.determinantPolynomial := by
  rw [eval_orientationPolynomial, determinant_cofactor_expansion]
  simp [graph, graphPolynomial]

@[simp] theorem minimum_graph (w : Gram6.Coord) : minimum (graph w) = Gram6.minimum w := by
  simp only [minimum_eq, baseProjection_graph, eval_errorPolynomial_graph,
    abs_zero, max_self, mul_zero, sub_zero]

@[simp] theorem f_graph (w : Gram6.Coord) : f (graph w) = Gram6.f w := by
  change (if 0 < minimum (graph w) ∧ 0 < eval (graph w) orientationPolynomial then
      minimum (graph w) else 0) =
    (if 0 < Gram6.minimum w ∧ 0 < eval w Gram6.determinantPolynomial then
      Gram6.minimum w else 0)
  rw [minimum_graph, eval_orientationPolynomial_graph]

/-- The representing polynomial degrees are unrestricted. -/
theorem not_isPolynomialLattice : ¬ IsPolynomialLattice f := by
  intro hf
  have hp := hf.precomp_polynomials graphPolynomial
  apply Gram6.not_isPolynomialLattice
  change IsPolynomialLattice (fun w : Gram6.Coord => f (graph w)) at hp
  simpa only [f_graph] using hp

theorem not_finite_sup_inf_polynomials {ι κ : Type*}
    (S : Finset ι) (hS : S.Nonempty) (T : ι → Finset κ)
    (hT : ∀ i, (T i).Nonempty) (p : ι → κ → Poly) :
    ¬ (∀ z : Coord, f z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => eval z (p i j)))) := by
  intro heq
  apply not_isPolynomialLattice
  have hfun : f = (fun z =>
      S.sup' hS (fun i => (T i).inf' (hT i) (fun j => eval z (p i j)))) := funext heq
  rw [hfun]
  exact finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p

end PBCounterexample.Quadratic8
