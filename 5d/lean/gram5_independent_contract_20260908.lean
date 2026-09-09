import PBCounterexample.Basic
import PBCounterexample.FiniteExpressions
import PBCounterexample.Semialgebraic

/-!
Independent semantic expectations for the five-dimensional construction.

This module imports no dimension-specific implementation.  Definitions ending
in "Claim" are propositions to be proved by a later independent binding module;
defining them is not a proof that they hold.  The algebraic helper theorems below
do not prove the counterexample.  This source has not been compiled locally.
-/

noncomputable section

open PBCounterexample MvPolynomial
open scoped BigOperators

namespace Gram5IndependentContract

abbrev Point := Fin 5 → ℝ
abbrev Poly := MvPolynomial (Fin 5) ℝ

def a : Poly := X 0
def b : Poly := X 1
def c : Poly := X 2
def d : Poly := X 3
def e : Poly := X 4

-- These are expanded independently, not aliases for an implementation's labels.
def q1 : Poly :=
  16*a*e - 64*b*d + 48*c^2 - 160*c*d + 240*b*e
    + 48*d^2 - 64*c*e - 80*a^3 + 16*a^2*b

def q2 : Poly :=
  48*a*e - 192*b*d + 144*c^2 + 32*c*d - 48*b*e
    - 48*d^2 + 64*c*e + 16*a^3 - 16*a^2*b

def q3 : Poly :=
  192*b^2 - 192*a*c - 80*a*e - 64*b*d + 144*c^2
    + 32*c*d - 48*b*e - 48*d^2 + 128*c*e + 16*a^3 - 80*a^2*b

def q4 : Poly :=
  -48*a*e + 192*b*d - 144*c^2 + 32*c*d - 48*b*e
    + 48*d^2 - 64*c*e + 16*a^3 + 16*a^2*b

def labels : Fin 4 → Poly := ![q1, q2, q3, q4]

def determinant : Poly :=
  8*((a+2*c+e)*(d*(-a+4*c+e)+2*b*(c-e))
    -(b+2*d+a^2)*(-a*c-c*e+6*c^2+2*d^2-4*b*d+2*b^2))

def minimum (z : Point) : ℝ :=
  min (min (eval z q1) (eval z q2)) (min (eval z q3) (eval z q4))

def selected (z : Point) : ℝ :=
  if 0 < minimum z ∧ 0 < eval z determinant then minimum z else 0

def zeroRegion : Set Point :=
  {z | eval z determinant ≤ 0} ∪ ⋃ i : Fin 4, {z | eval z (labels i) ≤ 0}

def activeRegion (i : Fin 4) : Set Point :=
  {z | 0 ≤ eval z determinant ∧ (∀ j, 0 ≤ eval z (labels j)) ∧
    (∀ j, eval z (labels i) ≤ eval z (labels j))}

def region : Option (Fin 4) → Set Point
  | none => zeroRegion
  | some i => activeRegion i

def label : Option (Fin 4) → Poly
  | none => 0
  | some i => labels i

/-- Exactly five prescribed closed pieces on the entire coordinate space. -/
def ExplicitCoverClaim : Prop :=
  (∀ i, IsClosed (region i)) ∧
  (∀ i, IsSemialgebraic (region i)) ∧
  (∀ z : Point, ∃ i, z ∈ region i) ∧
  (∀ i z, z ∈ region i → selected z = eval z (label i))

/-- The final semantic target, with no external parameters or hypotheses. -/
def WholeSpaceClaim : Prop :=
  Continuous selected ∧ ExplicitCoverClaim ∧ ¬ IsPolynomialLattice selected

def testA : Poly := a*e - 4*b*d + 3*c^2
def testB : Poly := 2*c*d - 3*b*e + a^3
def testW : Poly := 3*d^2 - 4*c*e + a^2*b
def testg : Poly := b^2 - a*c
def testG : Poly := -a^2*d + 3*a*b*c - 2*b^3

theorem q1_exact :
    q1 = 16*testA - 80*testB + 16*testW := by
  unfold q1 testA testB testW
  ring

theorem q2_exact :
    q2 = 48*testA + 16*testB - 16*testW := by
  unfold q2 testA testB testW
  ring

theorem q4_exact :
    q4 = -48*testA + 16*testB + 16*testW := by
  unfold q4 testA testB testW
  ring

theorem q3_exact :
    q3 = 192*testg + 16*(-5*a*e-4*b*d+9*c^2)
      + 16*testB + 16*(-3*d^2+8*c*e-5*a^2*b) := by
  unfold q3 testg testB
  ring

def weight : Fin 5 → ℕ := ![5, 6, 7, 8, 9]
def scale (lam : ℝ) (z : Point) : Point := fun i => lam^(weight i)*z i
def one : Point := fun _ => 1
def n : Point := ![0, 2, 3, 3, 2]
def j : Point := ![0, 0, 1, 2, 2]

def monomialWeight (m : Fin 5 →₀ ℕ) : ℕ := ∑ i : Fin 5, weight i * m i

def OfWeight (w : ℕ) (p : Poly) : Prop :=
  ∀ m, p.coeff m ≠ 0 → monomialWeight m = w

def component (w : ℕ) (p : Poly) : Poly :=
  p.support.sum fun m => if monomialWeight m = w then monomial m (p.coeff m) else 0

def linearAtOne (p : Poly) (v : Point) : ℝ :=
  p.support.sum fun m => p.coeff m * ∑ i : Fin 5, (m i : ℝ) * v i

def Exceptional (w : ℕ) (p : Poly) : Prop :=
  p = 0 ∨ (w = 14 ∧ ∃ t : ℝ, p = C t * testA) ∨
    (w = 15 ∧ ∃ t : ℝ, p = C t * testB) ∨
    (w = 16 ∧ ∃ t : ℝ, p = C t * testW)

def CompleteKernelClaim : Prop :=
  ∀ w, w ≤ 16 → ∀ p : Poly, OfWeight w p →
    ((eval one p = 0 ∧ linearAtOne p n = 0) ↔ Exceptional w p)

def WeightedDecompositionClaim : Prop :=
  ∀ p : Poly,
    p = ∑ w ∈ p.support.image monomialWeight, component w p

def WeightedEvaluationClaim : Prop :=
  ∀ w p, OfWeight w p → ∀ lam z, eval (scale lam z) p = lam^w * eval z p

def A2 (v : Point) : ℝ := -4*v 1*v 3 + 3*(v 2)^2
def B2 (v : Point) : ℝ := 2*v 2*v 3 - 3*v 1*v 4
def W2 (v : Point) : ℝ := 3*(v 3)^2 - 4*v 2*v 4
def F2 (v : Point) : ℝ := W2 v - B2 v + A2 v
def linearA (v : Point) : ℝ := v 0 - 4*v 1 + 6*v 2 - 4*v 3 + v 4
def linearB (v : Point) : ℝ := 3*v 0 - 3*v 1 + 2*v 2 + 2*v 3 - 3*v 4

def orientation : Bool → ℝ
  | false => -1
  | true => 1

def radicand (lam : ℝ) : ℝ := 3 - 3*lam/8 + lam^2
def rootFactor (lam : ℝ) : ℝ := Real.sqrt (radicand lam / 3)
def initialDirection (delta : ℝ) (side : Bool) (lam : ℝ) : Point :=
  fun i => n i + orientation side * delta * rootFactor lam * j i

def correction (u : Fin 3 → ℝ) : Point :=
  ![0, 0, u 2, u 0 + 2*u 2, u 1 + 2*u 2]

def residual (delta : ℝ) (side : Bool) (epsilon lam : ℝ)
    (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let v := initialDirection delta side lam + correction u
  ![linearA (correction u) + epsilon*(A2 v-lam^2*delta^2),
    linearB (correction u) + epsilon*(B2 v-(3*lam/8)*delta^2),
    F2 v-delta^2*radicand lam]

def expectedJacobian (delta : ℝ) (side : Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-4, 1, 0], ![2, -3, 0],
    ![4+10*orientation side*delta, -6-4*orientation side*delta,
      6*orientation side*delta]]

def rectangle (epsilonRadius lambdaRadius : ℝ) : Set (ℝ × ℝ) :=
  {t | |t.1| < epsilonRadius ∧ |t.2| < lambdaRadius}

/-- This records actual jointly differentiable solutions on a shared rectangle.
No postulated solver or formal power series populates this structure. -/
structure CorrectedPathData (delta : ℝ) where
  epsilonRadius : ℝ
  lambdaRadius : ℝ
  epsilonRadius_pos : 0 < epsilonRadius
  lambdaRadius_pos : 0 < lambdaRadius
  z : Bool → (ℝ × ℝ) → (Fin 3 → ℝ)
  smooth : ∀ side, ContDiffOn ℝ 1 (z side) (rectangle epsilonRadius lambdaRadius)
  zero_at_epsilon_zero :
    ∀ side lam, |lam| < lambdaRadius → z side (0, lam) = 0
  residual_zero :
    ∀ side epsilon lam, |epsilon| < epsilonRadius → |lam| < lambdaRadius →
      residual delta side epsilon lam (z side (epsilon, lam)) = 0

def ActualIFTClaim : Prop :=
  ∀ delta : ℝ, 0 < delta → Nonempty (CorrectedPathData delta)

def normalizedPoint {delta : ℝ} (data : CorrectedPathData delta)
    (side : Bool) (epsilon lam : ℝ) : Point :=
  one + epsilon •
    (initialDirection delta side lam + correction (data.z side (epsilon, lam)))

def actualPoint {delta : ℝ} (data : CorrectedPathData delta)
    (side : Bool) (epsilon lam : ℝ) : Point :=
  scale lam (normalizedPoint data side epsilon lam)

def FixedEpsilonContinuityClaim : Prop :=
  ∀ delta (data : CorrectedPathData delta) epsilon,
    |epsilon| < data.epsilonRadius → ∀ side,
      ContinuousAt (normalizedPoint data side epsilon) 0

def ExactTargetClaim : Prop :=
  ∀ delta (data : CorrectedPathData delta) side epsilon lam,
    |epsilon| < data.epsilonRadius → |lam| < data.lambdaRadius →
    let v := normalizedPoint data side epsilon lam
    eval v testA = lam^2*epsilon^2*delta^2 ∧
    eval v testB = (3*lam/8)*epsilon^2*delta^2 ∧
    eval v testW = 3*epsilon^2*delta^2

/-- The order is finite family, delta/data, fixed epsilon, then all small lambda. -/
def WeightedFiniteCollectionClaim : Prop :=
  ∀ S : Finset Poly, ∃ delta : ℝ, 0 < delta ∧ delta < 1/2 ∧
    ∃ data : CorrectedPathData delta, ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < data.epsilonRadius ∧
      ∃ lambdaBound : ℝ, 0 < lambdaBound ∧ lambdaBound ≤ data.lambdaRadius ∧
        ∀ lam : ℝ, 0 < lam → lam < lambdaBound →
          let plus := actualPoint data true epsilon lam
          let minus := actualPoint data false epsilon lam
          selected plus = 6*lam^16*epsilon^2*delta^2 ∧ selected minus = 0 ∧
          ∀ p ∈ S, selected plus ≤ eval plus p → 0 < eval minus p

def FiniteThresholdPairClaim : Prop :=
  ∀ S : Finset Poly, ∃ plus minus : Point,
    0 < selected plus ∧ selected minus = 0 ∧
    ∀ p ∈ S, selected plus ≤ eval plus p → 0 < eval minus p

def mixedCoefficient (alpha beta gamma : ℝ) : ℝ := alpha + 3*beta/8 + 3*gamma

theorem mixed_weight_identity (alpha beta gamma lam epsilon delta : ℝ) :
    alpha*lam^14*(lam^2*epsilon^2*delta^2)
      + beta*lam^15*((3*lam/8)*epsilon^2*delta^2)
      + gamma*lam^16*(3*epsilon^2*delta^2)
      = lam^16*epsilon^2*delta^2*mixedCoefficient alpha beta gamma := by
  unfold mixedCoefficient
  ring

theorem first_zero_combination : mixedCoefficient (-3) 8 0 = 0 := by
  norm_num [mixedCoefficient]

theorem second_zero_combination : mixedCoefficient (-3) 0 1 = 0 := by
  norm_num [mixedCoefficient]

/-- A generic transport lemma, not an assumption-free proof of WholeSpaceClaim. -/
theorem no_finite_sup_inf_of_no_lattice
    (h : ¬ IsPolynomialLattice selected)
    {ι κ : Type*} (S : Finset ι) (hS : S.Nonempty)
    (T : ι → Finset κ) (hT : ∀ i, (T i).Nonempty)
    (p : ι → κ → Poly) :
    ¬ (∀ z : Point, selected z =
      S.sup' hS (fun i => (T i).inf' (hT i) (fun k => eval z (p i k)))) := by
  intro heq
  apply h
  obtain ⟨expr, hexpr⟩ :=
    finite_sup_inf_polynomials_isPolynomialLattice S hS T hT p
  exact ⟨expr, fun z => (hexpr z).trans (heq z).symm⟩

end Gram5IndependentContract
