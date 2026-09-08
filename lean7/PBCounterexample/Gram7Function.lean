import PBCounterexample.Gram7Coordinates

/-! The five quadratic labels and the whole-space six-piece selection. -/

namespace PBCounterexample.Gram7

open Matrix MvPolynomial
open scoped BigOperators

abbrev Label := {a : GramSelection.Label // a.val ≠ (2, 3)}

def edge01 : GramSelection.Label := ⟨(0, 1), by decide⟩
def edge03 : GramSelection.Label := ⟨(0, 3), by decide⟩
def edge13 : GramSelection.Label := ⟨(1, 3), by decide⟩
def edge23 : GramSelection.Label := ⟨(2, 3), by decide⟩

instance : Nonempty Label := ⟨⟨edge01, by decide⟩⟩

noncomputable def gramMatrix (z : Coord) : Matrix Index Index ℝ :=
  (aMatrix z)ᵀ * aMatrix z - (bMatrix z)ᵀ * bMatrix z

noncomputable def allQuadratics : GramSelection.Label → MvPolynomial (Fin 7) ℝ :=
  GramSelection.qPolynomial aPolynomial bPolynomial

noncomputable def qPolynomial (a : Label) : MvPolynomial (Fin 7) ℝ := allQuadratics a.val

noncomputable def determinantPolynomial : MvPolynomial (Fin 7) ℝ :=
  GramSelection.determinantPolynomial aPolynomial

noncomputable def minimum (z : Coord) : ℝ := PolynomialSelection.minimum qPolynomial z

noncomputable def f (z : Coord) : ℝ := PolynomialSelection.f qPolynomial determinantPolynomial z

theorem gramSelection_gram_eq (z : Coord) :
    GramSelection.gram aPolynomial bPolynomial z = gramMatrix z := by
  simp [GramSelection.gram, gramMatrix]

theorem gram_relation (z : Coord) :
    gramMatrix z 0 0 + gramMatrix z 1 1 - gramMatrix z 2 2 = 0 := by
  norm_num [gramMatrix, aMatrix, bMatrix, ambientA, ambientB, aIndex, bIndex,
    ambient, basis, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val]
  ring

theorem gramMatrix_symm (z : Coord) : (gramMatrix z).IsSymm := by
  change (gramMatrix z)ᵀ = gramMatrix z
  simp [gramMatrix, Matrix.transpose_mul]

theorem eval_allQuadratics_relation (z : Coord) :
    eval z (allQuadratics edge23) = eval z (allQuadratics edge01) +
      2 * eval z (allQuadratics edge03) + 2 * eval z (allQuadratics edge13) := by
  have hs01 := (gramMatrix_symm z).apply 0 1
  have hs02 := (gramMatrix_symm z).apply 0 2
  have hs12 := (gramMatrix_symm z).apply 1 2
  have hg := gram_relation z
  simp only [allQuadratics, GramSelection.eval_qPolynomial, GramSelection.laplacian,
    gramSelection_gram_eq]
  norm_num [GramSelection.simplex, edge01, edge03, edge13, edge23,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val]
  linarith

theorem allQuadratics_positive {z : Coord} (hz : 0 < minimum z)
    (a : GramSelection.Label) : 0 < eval z (allQuadratics a) := by
  have hp (b : Label) : 0 < eval z (qPolynomial b) :=
    lt_of_lt_of_le hz (PolynomialSelection.minimum_le qPolynomial z b)
  by_cases ha : a.val = (2, 3)
  · have he : a = edge23 := Subtype.ext ha
    rw [he, eval_allQuadratics_relation]
    have h01 := hp ⟨edge01, by decide⟩
    have h03 := hp ⟨edge03, by decide⟩
    have h13 := hp ⟨edge13, by decide⟩
    change 0 < eval z (allQuadratics edge01) at h01
    change 0 < eval z (allQuadratics edge03) at h03
    change 0 < eval z (allQuadratics edge13) at h13
    linarith
  · exact hp ⟨a, ha⟩

theorem allMinimum_positive {z : Coord} (hz : 0 < minimum z) :
    0 < GramSelection.minimum aPolynomial bPolynomial z := by
  obtain ⟨a, ha⟩ := PolynomialSelection.exists_minimum_eq allQuadratics z
  change 0 < PolynomialSelection.minimum allQuadratics z
  rw [ha]
  exact allQuadratics_positive hz a

theorem determinant_ne_zero {z : Coord} (hz : 0 < minimum z) :
    eval z determinantPolynomial ≠ 0 := by
  have h := GramSelection.determinant_ne_zero aPolynomial bPolynomial (allMinimum_positive hz)
  simpa [determinantPolynomial] using h

noncomputable def polynomialCover : FiniteClosedPolynomialCover f :=
  PolynomialSelection.polynomialCover qPolynomial determinantPolynomial
    (fun _ hz => determinant_ne_zero hz)

theorem continuous_f : Continuous f := polynomialCover.continuous

theorem label_count : Fintype.card Label = 5 := by decide

theorem polynomialCover_count : polynomialCover.count = 6 := by
  change Fintype.card (Option Label) = 6
  rw [Fintype.card_option, label_count]

theorem qPolynomial_homogeneous (a : Label) : (qPolynomial a).IsHomogeneous 2 :=
  GramSelection.qPolynomial_homogeneous aPolynomial bPolynomial
    aPolynomial_homogeneous bPolynomial_homogeneous a.val

theorem polynomialCover_homogeneous (i : Fin polynomialCover.count) :
    (polynomialCover.label i).IsHomogeneous 2 :=
  PolynomialSelection.polynomialCover_homogeneous _ _ _ qPolynomial_homogeneous i

theorem f_positive_homogeneous (t : ℝ) (ht : 0 < t) (z : Coord) :
    f (t • z) = t^2 * f z := by
  apply PolynomialSelection.f_positive_homogeneous _ _ qPolynomial_homogeneous ?_ t ht z
  intro s hs w
  have hscale : aPolynomial.map (eval (s • w)) = s • aPolynomial.map (eval w) := by
    ext i j
    change eval (fun k => s * w k) (aPolynomial i j) = s * eval w (aPolynomial i j)
    simpa only [pow_one] using Radial.eval_homogeneous_scale (aPolynomial_homogeneous i j) w s
  change 0 < eval (s • w) (GramSelection.determinantPolynomial aPolynomial) ↔
    0 < eval w (GramSelection.determinantPolynomial aPolynomial)
  rw [GramSelection.eval_determinantPolynomial, GramSelection.eval_determinantPolynomial,
    hscale, Matrix.det_smul]
  exact mul_pos_iff_of_pos_left (pow_pos hs _)

end PBCounterexample.Gram7
