import PBCounterexample.Gram6Coordinates

/-! The four quadratic labels and the continuous five-piece selection. -/

namespace PBCounterexample.Gram6

open Matrix MvPolynomial
open scoped BigOperators

noncomputable def scaledAMatrix (w : Coord) : Matrix Index Index ℝ :=
  fun i j => (if i = 2 then Real.sqrt 3 else 1) * aMatrix w i j

noncomputable def scaledAPolynomial : Matrix Index Index (MvPolynomial (Fin 6) ℝ) :=
  fun i j => C (if i = 2 then Real.sqrt 3 else 1) * aPolynomial i j

@[simp] theorem eval_scaledAPolynomial (w : Coord) :
    scaledAPolynomial.map (eval w) = scaledAMatrix w := by
  have ha (i j : Index) : eval w (aPolynomial i j) = aMatrix w i j :=
    congrFun (congrFun (eval_aPolynomial w) i) j
  ext i j
  simp [scaledAPolynomial, scaledAMatrix, ha]

theorem scaledAPolynomial_homogeneous (i j : Index) :
    (scaledAPolynomial i j).IsHomogeneous 1 :=
  (aPolynomial_homogeneous i j).C_mul _

theorem gramSelection_gram_eq (w : Coord) :
    GramSelection.gram scaledAPolynomial bPolynomial w = gramMatrix w := by
  have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h02 : (0 : Index) ≠ 2 := by decide
  have h12 : (1 : Index) ≠ 2 := by decide
  ext i j
  norm_num [GramSelection.gram, scaledAMatrix, gramMatrix,
    Matrix.mul_apply, Fin.sum_univ_succ, h02, h12]
  linear_combination (aMatrix w 2 i * aMatrix w 2 j) * h3

theorem scaledAMatrix_det (w : Coord) :
    (scaledAMatrix w).det = Real.sqrt 3 * (aMatrix w).det := by
  have h02 : (0 : Index) ≠ 2 := by decide
  have h12 : (1 : Index) ≠ 2 := by decide
  norm_num [scaledAMatrix, Matrix.det_fin_three, h02, h12]
  ring

abbrev Label := {a : GramSelection.Label // a.val ≠ (0, 2) ∧ a.val ≠ (2, 3)}

def edge01 : GramSelection.Label := ⟨(0, 1), by decide⟩
def edge02 : GramSelection.Label := ⟨(0, 2), by decide⟩
def edge03 : GramSelection.Label := ⟨(0, 3), by decide⟩
def edge12 : GramSelection.Label := ⟨(1, 2), by decide⟩
def edge13 : GramSelection.Label := ⟨(1, 3), by decide⟩
def edge23 : GramSelection.Label := ⟨(2, 3), by decide⟩

instance : Nonempty Label := ⟨⟨edge01, by decide⟩⟩

noncomputable def allQuadratics : GramSelection.Label → MvPolynomial (Fin 6) ℝ :=
  GramSelection.qPolynomial scaledAPolynomial bPolynomial

def fourEdges : Fin 4 → GramSelection.Label := ![edge01, edge03, edge12, edge13]

noncomputable def labelPolynomial : Fin 4 → MvPolynomial (Fin 6) ℝ := ![
  C (-10) * gramPolynomial 0 1 + C 2 * gramPolynomial 2 2 + C 2 * gramPolynomial 1 2,
  C 4 * gramPolynomial 0 0 + C 2 * gramPolynomial 0 1 -
    C 2 * gramPolynomial 2 2 - C 2 * gramPolynomial 1 2,
  C (-4) * gramPolynomial 0 0 + C 2 * gramPolynomial 0 1 +
    C 6 * gramPolynomial 2 2 - C 10 * gramPolynomial 1 2,
  C (-4) * gramPolynomial 0 0 + C 2 * gramPolynomial 0 1 +
    C 2 * gramPolynomial 2 2 + C 2 * gramPolynomial 1 2]

theorem allQuadratics_fourEdges (i : Fin 4) :
    allQuadratics (fourEdges i) = labelPolynomial i := by
  apply MvPolynomial.funext
  intro w
  have hs01 := (gramMatrix_symmetric w).apply 0 1
  have hs02 := (gramMatrix_symmetric w).apply 0 2
  have hs12 := (gramMatrix_symmetric w).apply 1 2
  have hg := gram_relation w
  have hz := gram_entry02 w
  simp only [allQuadratics, GramSelection.eval_qPolynomial, GramSelection.laplacian,
    gramSelection_gram_eq]
  fin_cases i <;>
    norm_num [fourEdges, labelPolynomial, edge01, edge03, edge12, edge13,
      GramSelection.simplex, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    linarith

theorem fourEdges_covers : ∀ a : Label, ∃ i : Fin 4, fourEdges i = a.val := by decide

noncomputable def qPolynomial (a : Label) : MvPolynomial (Fin 6) ℝ := allQuadratics a.val

noncomputable def minimum (w : Coord) : ℝ := PolynomialSelection.minimum qPolynomial w

noncomputable def f (w : Coord) : ℝ := PolynomialSelection.f qPolynomial determinantPolynomial w

theorem eval_allQuadratics_relation02 (w : Coord) :
    eval w (allQuadratics edge02) = 2 * eval w (allQuadratics edge01) +
      6 * eval w (allQuadratics edge03) + 5 * eval w (allQuadratics edge13) := by
  have hs01 := (gramMatrix_symmetric w).apply 0 1
  have hs02 := (gramMatrix_symmetric w).apply 0 2
  have hs12 := (gramMatrix_symmetric w).apply 1 2
  have hg := gram_relation w
  have hz := gram_entry02 w
  simp only [allQuadratics, GramSelection.eval_qPolynomial, GramSelection.laplacian,
    gramSelection_gram_eq]
  norm_num [GramSelection.simplex, edge01, edge02, edge03, edge13,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val]
  linarith

theorem eval_allQuadratics_relation23 (w : Coord) :
    eval w (allQuadratics edge23) = eval w (allQuadratics edge01) +
      2 * eval w (allQuadratics edge03) + 2 * eval w (allQuadratics edge13) := by
  have hs01 := (gramMatrix_symmetric w).apply 0 1
  have hs02 := (gramMatrix_symmetric w).apply 0 2
  have hs12 := (gramMatrix_symmetric w).apply 1 2
  have hg := gram_relation w
  simp only [allQuadratics, GramSelection.eval_qPolynomial, GramSelection.laplacian,
    gramSelection_gram_eq]
  norm_num [GramSelection.simplex, edge01, edge03, edge13, edge23,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val]
  linarith

theorem allQuadratics_positive {w : Coord} (hw : 0 < minimum w)
    (a : GramSelection.Label) : 0 < eval w (allQuadratics a) := by
  have hp (b : Label) : 0 < eval w (qPolynomial b) :=
    lt_of_lt_of_le hw (PolynomialSelection.minimum_le qPolynomial w b)
  have h01 : 0 < eval w (allQuadratics edge01) := hp ⟨edge01, by decide⟩
  have h03 : 0 < eval w (allQuadratics edge03) := hp ⟨edge03, by decide⟩
  have h13 : 0 < eval w (allQuadratics edge13) := hp ⟨edge13, by decide⟩
  by_cases h02 : a.val = (0, 2)
  · have he : a = edge02 := Subtype.ext h02
    rw [he, eval_allQuadratics_relation02]
    linarith
  · by_cases h23 : a.val = (2, 3)
    · have he : a = edge23 := Subtype.ext h23
      rw [he, eval_allQuadratics_relation23]
      linarith
    · exact hp ⟨a, h02, h23⟩

theorem allMinimum_positive {w : Coord} (hw : 0 < minimum w) :
    0 < GramSelection.minimum scaledAPolynomial bPolynomial w := by
  obtain ⟨a, ha⟩ := PolynomialSelection.exists_minimum_eq allQuadratics w
  change 0 < PolynomialSelection.minimum allQuadratics w
  rw [ha]
  exact allQuadratics_positive hw a

theorem determinant_ne_zero {w : Coord} (hw : 0 < minimum w) :
    eval w determinantPolynomial ≠ 0 := by
  have h := GramSelection.determinant_ne_zero scaledAPolynomial bPolynomial
    (allMinimum_positive hw)
  rw [eval_scaledAPolynomial, scaledAMatrix_det] at h
  rw [eval_determinantPolynomial]
  intro hd
  exact h (by rw [hd, mul_zero])

noncomputable def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover qPolynomial determinantPolynomial
    (fun _ hw => determinant_ne_zero hw)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem label_count : Fintype.card Label = 4 := by decide

theorem polynomialCover_count : polynomialCover.count = 5 := by
  change Fintype.card (Option Label) = 5
  rw [Fintype.card_option, label_count]

theorem qPolynomial_homogeneous (a : Label) : (qPolynomial a).IsHomogeneous 2 :=
  GramSelection.qPolynomial_homogeneous scaledAPolynomial bPolynomial
    scaledAPolynomial_homogeneous bPolynomial_homogeneous a.val

theorem polynomialCover_homogeneous (i : Fin polynomialCover.count) :
    (polynomialCover.label i).IsHomogeneous 2 :=
  PolynomialSelection.polynomialCover_homogeneous _ _ _ qPolynomial_homogeneous i

theorem f_positive_homogeneous (t : ℝ) (ht : 0 < t) (w : Coord) :
    f (t • w) = t^2 * f w := by
  apply PolynomialSelection.f_positive_homogeneous _ _ qPolynomial_homogeneous ?_ t ht w
  intro s hs z
  have hscale : aPolynomial.map (eval (s • z)) = s • aPolynomial.map (eval z) := by
    ext i j
    change eval (fun k => s * z k) (aPolynomial i j) = s * eval z (aPolynomial i j)
    simpa only [pow_one] using Radial.eval_homogeneous_scale (aPolynomial_homogeneous i j) z s
  change 0 < eval (s • z) aPolynomial.det ↔ 0 < eval z aPolynomial.det
  rw [(eval (s • z)).map_det aPolynomial, (eval z).map_det aPolynomial]
  change 0 < (aPolynomial.map (eval (s • z))).det ↔
    0 < (aPolynomial.map (eval z)).det
  rw [hscale, Matrix.det_smul]
  exact mul_pos_iff_of_pos_left (pow_pos hs _)

end PBCounterexample.Gram6
