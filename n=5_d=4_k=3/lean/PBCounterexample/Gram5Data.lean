import Mathlib

/-! Explicit polynomials for a function on all five real coordinates. -/

namespace PBCounterexample.Gram5

open Matrix MvPolynomial
open scoped BigOperators

abbrev Coord := Fin 5 → ℝ
abbrev Poly := MvPolynomial (Fin 5) ℝ
abbrev Index := Fin 3
abbrev Label := Fin 4

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def a : Poly := X 0
def b : Poly := X 1
def c : Poly := X 2
def d : Poly := X 3
def e : Poly := X 4

def xPolynomial : Poly := a - 6*c + e
def yPolynomial : Poly := 4*(d-b)
def zPolynomial : Poly := a + 2*c + e
def uPolynomial : Poly := 2*(e-a)
def vPolynomial : Poly := 4*(d+b)
def rPolynomial : Poly := 2*b + 4*d + 2*a^2
def halfRPolynomial : Poly := b + 2*d + a^2
def halfUPolynomial : Poly := e-a
def halfVPolynomial : Poly := 2*(d+b)

theorem twice_halfRPolynomial : 2*halfRPolynomial = rPolynomial := by
  simp only [halfRPolynomial, rPolynomial]
  ring

theorem twice_halfUPolynomial : 2*halfUPolynomial = uPolynomial := rfl

theorem twice_halfVPolynomial : 2*halfVPolynomial = vPolynomial := by
  simp only [halfVPolynomial, vPolynomial]
  ring

def positivePolynomial : Matrix Index Index Poly :=
  !![xPolynomial, -vPolynomial + halfRPolynomial, -yPolynomial;
     yPolynomial, zPolynomial + uPolynomial, xPolynomial;
     zPolynomial, halfRPolynomial, 0]

def negativePolynomial : Matrix (Fin 2) Index Poly :=
  !![uPolynomial, -halfVPolynomial + rPolynomial, -halfVPolynomial;
     vPolynomial, 2*zPolynomial + halfUPolynomial, halfUPolynomial]

def columnPolynomial : Matrix (Fin 5) Index Poly :=
  !![xPolynomial, -vPolynomial + halfRPolynomial, -yPolynomial;
     yPolynomial, zPolynomial + uPolynomial, xPolynomial;
     zPolynomial, halfRPolynomial, 0;
     uPolynomial, -halfVPolynomial + rPolynomial, -halfVPolynomial;
     vPolynomial, 2*zPolynomial + halfUPolynomial, halfUPolynomial]

def signaturePolynomial : Matrix (Fin 5) (Fin 5) Poly :=
  Matrix.diagonal ![1, 1, 3, -1, -1]

def gramPolynomial : Matrix Index Index Poly :=
  columnPolynomialᵀ * signaturePolynomial * columnPolynomial

def determinantPolynomial : Poly := positivePolynomial.det

def invariantA : Poly := a*e - 4*b*d + 3*c^2
def invariantB : Poly := 2*c*d - 3*b*e + a^3
def invariantW : Poly := 3*d^2 - 4*c*e + a^2*b
def leadingG : Poly := b^2 - a*c
def leadingDeterminant : Poly := -a^2*d + 3*a*b*c - 2*b^3

def gramA : Poly := 16*invariantA
def gramB : Poly := 8*invariantB
def gramE : Poly := 4*a*e - 12*a*c - 12*c*e + 36*c^2 +
  12*d^2 - 40*b*d + 12*b^2
def gramF : Poly := 4*a*e + 12*a*c - 20*c*e - 12*c^2 +
  12*d^2 - 12*b^2 + 8*b*d + 8*a^2*b

def qPolynomial : Label → Poly :=
  ![-10*gramB + 2*gramE + 2*gramF,
    4*gramA + 2*gramB - 2*gramE - 2*gramF,
    -4*gramA + 2*gramB + 6*gramE - 10*gramF,
    -4*gramA + 2*gramB + 2*gramE + 2*gramF]

def positiveMatrix (z : Coord) : Matrix Index Index ℝ :=
  positivePolynomial.map (eval z)

def negativeMatrix (z : Coord) : Matrix (Fin 2) Index ℝ :=
  negativePolynomial.map (eval z)

def gramMatrix (z : Coord) : Matrix Index Index ℝ :=
  gramPolynomial.map (eval z)

def q (i : Label) (z : Coord) : ℝ := eval z (qPolynomial i)
def determinant (z : Coord) : ℝ := eval z determinantPolynomial

theorem gramPolynomial_eq :
    gramPolynomial = !![gramA, gramB, 0;
      gramB, gramE-gramA, gramF; 0, gramF, gramE] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramPolynomial, columnPolynomial, signaturePolynomial,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, xPolynomial, yPolynomial, zPolynomial,
      uPolynomial, vPolynomial, rPolynomial, halfRPolynomial,
      halfUPolynomial, halfVPolynomial, gramA, gramB, gramE,
      gramF, invariantA, invariantB] <;> ring

theorem invariantW_identity :
    2*gramE - gramA + 2*gramF = 16*invariantW := by
  simp only [gramE, gramA, gramF, invariantA, invariantW]
  ring

theorem determinantPolynomial_eq :
    determinantPolynomial = 8*((a+2*c+e)*
      (d*(-a+4*c+e)+2*b*(c-e)) -
      (b+2*d+a^2)*(-a*c-c*e+6*c^2+2*d^2-4*b*d+2*b^2)) := by
  norm_num [determinantPolynomial, positivePolynomial, Matrix.det_fin_three,
    xPolynomial, yPolynomial, zPolynomial, uPolynomial, vPolynomial,
    rPolynomial, halfRPolynomial]
  ring

@[simp] theorem eval_determinantPolynomial (z : Coord) :
    eval z determinantPolynomial = (positiveMatrix z).det :=
  (eval z).map_det positivePolynomial

/-- The exact six-edge simplex identity in scalar quadratic-form form. -/
theorem quadratic_simplex_identity (z : Coord) (v : Index → ℝ) :
    16*(v ⬝ᵥ (gramMatrix z *ᵥ v)) =
      q 0 z * (v 0-v 1)^2 +
      (2*q 0 z+6*q 1 z+5*q 3 z)*(v 0-v 2)^2 +
      q 1 z*(2*v 0+v 1+v 2)^2 +
      q 2 z*(v 1-v 2)^2 +
      q 3 z*(v 0+2*v 1+v 2)^2 +
      (q 0 z+2*q 1 z+2*q 3 z)*(v 0+v 1+2*v 2)^2 := by
  norm_num [gramMatrix, gramPolynomial_eq, q, qPolynomial,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The displayed signature is used without identifying Gram and column
kernels on a weakly positive boundary. -/
theorem quadratic_gram_identity (z : Coord) (v : Index → ℝ) :
    v ⬝ᵥ (gramMatrix z *ᵥ v) =
      ((positiveMatrix z *ᵥ v) 0)^2 +
      ((positiveMatrix z *ᵥ v) 1)^2 +
      3*((positiveMatrix z *ᵥ v) 2)^2 -
      ((negativeMatrix z *ᵥ v) 0)^2 -
      ((negativeMatrix z *ᵥ v) 1)^2 := by
  norm_num [gramMatrix, gramPolynomial, columnPolynomial,
    signaturePolynomial, positiveMatrix, positivePolynomial,
    negativeMatrix, negativePolynomial, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

def originalCoordinates (v : Coord) : Coord :=
  ![eval v xPolynomial, eval v yPolynomial, eval v zPolynomial,
    eval v uPolynomial, eval v vPolynomial]

def inverseCoordinates (v : Coord) : Coord :=
  ![(v 0+3*v 2-2*v 3)/8, (v 4-v 1)/8, (v 2-v 0)/8,
    (v 4+v 1)/8, (v 0+3*v 2+2*v 3)/8]

theorem inverse_originalCoordinates (v : Coord) :
    inverseCoordinates (originalCoordinates v) = v := by
  ext i
  fin_cases i <;>
    norm_num [inverseCoordinates, originalCoordinates, xPolynomial,
      yPolynomial, zPolynomial, uPolynomial, vPolynomial, a, b, c, d, e] <;>
    ring_nf <;> rfl

theorem original_inverseCoordinates (v : Coord) :
    originalCoordinates (inverseCoordinates v) = v := by
  ext i
  fin_cases i <;>
    norm_num [inverseCoordinates, originalCoordinates, xPolynomial,
      yPolynomial, zPolynomial, uPolynomial, vPolynomial, a, b, c, d, e] <;>
    ring_nf <;> rfl

end

end PBCounterexample.Gram5
