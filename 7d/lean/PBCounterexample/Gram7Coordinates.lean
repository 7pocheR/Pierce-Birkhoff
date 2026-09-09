import PBCounterexample.GramSelection

/-!
# Seven coordinates for a nonsymmetric Gram section

The negative coordinates of the quadratic form `Q₀₀ + Q₁₁ - Q₂₂` give
an explicit rational linear identification with a subspace of matrix pairs.
-/

namespace PBCounterexample.Gram7

open Matrix MvPolynomial
open scoped BigOperators

abbrev Coord := Fin 7 → ℝ
abbrev Ambient := Fin 15 → ℝ
abbrev Index := Fin 3
abbrev Row := Fin 2

noncomputable def basis : Matrix (Fin 15) (Fin 7) ℝ := !![
  -1/3, -1/3, -1/3, 2/3, 1/3, 0, -1/3;
  19/45, -1/9, -13/90, -4/9, 11/18, 1/10, -4/9;
  1, 0, 0, 0, 0, 0, 0;
  163/315, -7/9, 59/630, 8/63, -37/126, 1/210, 8/63;
  -1/3, -1/3, -1/3, -1/3, 1/3, 0, 2/3;
  0, 1, 0, 0, 0, 0, 0;
  -46/105, -1/3, 11/105, -3/7, -5/21, -38/105, -3/7;
  -23/63, -2/9, 37/63, -5/63, 5/63, 10/21, -5/63;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  2/35, 0, 31/70, 1/7, 5/14, 17/70, 1/7;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1;
  -2/35, 0, -31/70, -1/7, -5/14, 53/70, -1/7]

def constraintsMatrix : Matrix (Fin 8) (Fin 15) ℝ := !![
  3, 0, 1, 0, 0, 1, 0, 0, 1, -2, 0, 0, -1, 1, 0;
  0, 0, -326, 630, 0, 490, 0, 0, -59, -80, -3, 0, 185, -80, 0;
  0, 0, 46, 0, 0, 35, 105, 0, -11, 45, 38, 0, 25, 45, 0;
  0, 90, -38, 0, 0, 10, 0, 0, 13, 40, -9, 0, -55, 40, 0;
  0, 0, 1, 0, 3, 1, 0, 0, 1, 1, 0, 0, -1, -2, 0;
  0, 0, 23, 0, 0, 14, 0, 63, -37, 5, -30, 0, -5, 5, 0;
  0, 0, -4, 0, 0, 0, 0, 0, -31, -10, -17, 70, -25, -10, 0;
  0, 0, 4, 0, 0, 0, 0, 0, 31, 10, -53, 0, 25, 10, 70]

def negativeIndex : Fin 7 → Fin 15 := ![2, 5, 8, 9, 12, 10, 13]

noncomputable def ambient (z : Coord) : Ambient := basis *ᵥ z

noncomputable def coordinates (a : Ambient) : Coord := fun i => a (negativeIndex i)

noncomputable def constraints (a : Ambient) : Fin 8 → ℝ := constraintsMatrix *ᵥ a

def aIndex (i j : Index) : Fin 15 := ⟨3 * i.val + j.val, by omega⟩

def bIndex (i : Row) (j : Index) : Fin 15 := ⟨9 + 3 * i.val + j.val, by omega⟩

noncomputable def ambientA (a : Ambient) : Matrix Index Index ℝ := fun i j => a (aIndex i j)

noncomputable def ambientB (a : Ambient) : Matrix Row Index ℝ := fun i j => a (bIndex i j)

noncomputable def aMatrix (z : Coord) : Matrix Index Index ℝ := ambientA (ambient z)

noncomputable def bMatrix (z : Coord) : Matrix Row Index ℝ := ambientB (ambient z)

theorem ambient_add (z w : Coord) : ambient (z + w) = ambient z + ambient w :=
  Matrix.mulVec_add _ _ _

theorem ambient_smul (r : ℝ) (z : Coord) : ambient (r • z) = r • ambient z :=
  Matrix.mulVec_smul _ _ _

theorem coordinates_ambient (z : Coord) : coordinates (ambient z) = z := by
  ext i
  fin_cases i <;> simp [coordinates, negativeIndex, ambient, basis,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem constraintsMatrix_basis : constraintsMatrix * basis = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constraintsMatrix, basis, Matrix.mul_apply, Fin.sum_univ_succ]

theorem constraints_ambient (z : Coord) : constraints (ambient z) = 0 := by
  rw [constraints, ambient, Matrix.mulVec_mulVec, constraintsMatrix_basis, Matrix.zero_mulVec]

theorem ambient_coordinates_of_constraints (a : Ambient) (ha : constraints a = 0) :
    ambient (coordinates a) = a := by
  have h0 := congrFun ha (⟨0, by decide⟩ : Fin 8)
  have h1 := congrFun ha (⟨1, by decide⟩ : Fin 8)
  have h2 := congrFun ha (⟨2, by decide⟩ : Fin 8)
  have h3 := congrFun ha (⟨3, by decide⟩ : Fin 8)
  have h4 := congrFun ha (⟨4, by decide⟩ : Fin 8)
  have h5 := congrFun ha (⟨5, by decide⟩ : Fin 8)
  have h6 := congrFun ha (⟨6, by decide⟩ : Fin 8)
  have h7 := congrFun ha (⟨7, by decide⟩ : Fin 8)
  norm_num [constraints, constraintsMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.cons_val, Fin.succ] at h0 h1 h2 h3 h4 h5 h6 h7
  ext i
  fin_cases i <;>
    norm_num [ambient, coordinates, negativeIndex, basis, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val, Fin.succ] <;> linarith!

theorem constraints_iff_exists_coordinates (a : Ambient) :
    constraints a = 0 ↔ ∃ z : Coord, ambient z = a := by
  constructor
  · intro h
    exact ⟨coordinates a, ambient_coordinates_of_constraints a h⟩
  · rintro ⟨z, rfl⟩
    exact constraints_ambient z

noncomputable def ambientPolynomial (i : Fin 15) : MvPolynomial (Fin 7) ℝ :=
  ∑ k : Fin 7, C (basis i k) * X k

noncomputable def aPolynomial : Matrix Index Index (MvPolynomial (Fin 7) ℝ) :=
  fun i j => ambientPolynomial (aIndex i j)

noncomputable def bPolynomial : Matrix Row Index (MvPolynomial (Fin 7) ℝ) :=
  fun i j => ambientPolynomial (bIndex i j)

@[simp] theorem eval_ambientPolynomial (z : Coord) (i : Fin 15) :
    eval z (ambientPolynomial i) = ambient z i := by
  simp [ambientPolynomial, ambient, Matrix.mulVec, dotProduct]

@[simp] theorem eval_aPolynomial (z : Coord) : aPolynomial.map (eval z) = aMatrix z := by
  ext i j
  exact eval_ambientPolynomial z (aIndex i j)

@[simp] theorem eval_bPolynomial (z : Coord) : bPolynomial.map (eval z) = bMatrix z := by
  ext i j
  exact eval_ambientPolynomial z (bIndex i j)

theorem ambientPolynomial_homogeneous (i : Fin 15) : (ambientPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (MvPolynomial.isHomogeneous_X ℝ k).C_mul (basis i k)

theorem aPolynomial_homogeneous (i j : Index) : (aPolynomial i j).IsHomogeneous 1 :=
  ambientPolynomial_homogeneous _

theorem bPolynomial_homogeneous (i : Row) (j : Index) : (bPolynomial i j).IsHomogeneous 1 :=
  ambientPolynomial_homogeneous _

end PBCounterexample.Gram7
