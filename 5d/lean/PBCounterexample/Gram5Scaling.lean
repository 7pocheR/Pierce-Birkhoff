import PBCounterexample.Gram5Paths
import PBCounterexample.Gram5Differential
import PBCounterexample.Gram5Selection

/-! Exact weighted label identities and the determinant's normalized limit. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def labelRemainder14 : Poly := -80*a*e-64*b*d+144*c^2
def labelRemainder16 : Poly := 128*c*e-48*d^2-80*a^2*b
def determinantTerm20 : Poly := 4*a*c*d-2*a*b*e-2*b*c^2
def determinantTerm22 : Poly := a^3*c-2*a^2*b^2-4*c^2*d-b*c*e+6*b*d^2
def determinantTerm24 : Poly := 8*c*d*e-2*b*e^2-4*d^3-6*a^2*c^2+4*a^2*b*d
def determinantTerm26 : Poly := d*e^2+a^2*c*e-2*a^2*d^2

theorem weightedScale_eq (t : ℝ) (v : Coord) :
    weightedScale t v = ![t^5*v 0, t^6*v 1, t^7*v 2, t^8*v 3, t^9*v 4] := by
  funext i
  fin_cases i <;> rfl

theorem q_zero_weightedScale (t : ℝ) (v : Coord) :
    q 0 (weightedScale t v) =
      16*t^14*eval v invariantA - 80*t^15*eval v invariantB +
        16*t^16*eval v invariantW := by
  rw [weightedScale_eq]
  norm_num [q, qPolynomial, gramA, gramB, gramE, gramF,
    invariantA, invariantB, invariantW, a, b, c, d, e]
  ring

theorem q_one_weightedScale (t : ℝ) (v : Coord) :
    q 1 (weightedScale t v) =
      48*t^14*eval v invariantA + 16*t^15*eval v invariantB -
        16*t^16*eval v invariantW := by
  rw [weightedScale_eq]
  norm_num [q, qPolynomial, gramA, gramB, gramE, gramF,
    invariantA, invariantB, invariantW, a, b, c, d, e]
  ring

theorem q_three_weightedScale (t : ℝ) (v : Coord) :
    q 3 (weightedScale t v) =
      -48*t^14*eval v invariantA + 16*t^15*eval v invariantB +
        16*t^16*eval v invariantW := by
  rw [weightedScale_eq]
  norm_num [q, qPolynomial, gramA, gramB, gramE, gramF,
    invariantA, invariantB, invariantW, a, b, c, d, e]
  ring

theorem q_two_weightedScale (t : ℝ) (v : Coord) :
    q 2 (weightedScale t v) = t^12 *
      (192*eval v leadingG + t^2*eval v labelRemainder14 +
        16*t^3*eval v invariantB + t^4*eval v labelRemainder16) := by
  rw [weightedScale_eq]
  norm_num [q, qPolynomial, gramA, gramB, gramE, gramF, leadingG,
    invariantA, invariantB, labelRemainder14, labelRemainder16, a, b, c, d, e]
  ring

theorem determinant_weightedScale (t : ℝ) (v : Coord) :
    determinant (weightedScale t v) = 8*t^18 *
      (eval v leadingDeterminant + t^2*eval v determinantTerm20 +
        t^4*eval v determinantTerm22 + t^6*eval v determinantTerm24 +
        t^8*eval v determinantTerm26) := by
  rw [weightedScale_eq]
  norm_num [determinant, determinantPolynomial_eq, leadingDeterminant,
    determinantTerm20, determinantTerm22, determinantTerm24, determinantTerm26,
    a, b, c, d, e]
  ring

theorem tendsto_q_two_div {v : ℝ → Coord} {v₀ : Coord}
    (hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 v₀)) :
    Tendsto (fun t : ℝ => q 2 (weightedScale t (v t))/t^12)
      (𝓝[>] 0) (𝓝 (192*eval v₀ leadingG)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have he (P : Poly) : Tendsto (fun t : ℝ => eval (v t) P)
      (𝓝[>] 0) (𝓝 (eval v₀ P)) :=
    (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp hv
  have hlim := (((he leadingG).const_mul 192).add
    ((ht.pow 2).mul (he labelRemainder14))).add
    (((ht.pow 3).const_mul 16).mul (he invariantB))
  have hlim' := hlim.add ((ht.pow 4).mul (he labelRemainder16))
  have hlim'' : Tendsto (fun t : ℝ =>
      192*eval (v t) leadingG + t^2*eval (v t) labelRemainder14 +
        16*t^3*eval (v t) invariantB + t^4*eval (v t) labelRemainder16)
      (𝓝[>] 0) (𝓝 (192*eval v₀ leadingG)) := by simpa using hlim'
  apply (tendsto_congr' ?_).2 hlim''
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  rw [q_two_weightedScale]
  field_simp [ne_of_gt htpos] <;> ring

theorem tendsto_determinant_div {v : ℝ → Coord} {v₀ : Coord}
    (hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 v₀)) :
    Tendsto (fun t : ℝ => determinant (weightedScale t (v t))/t^18)
      (𝓝[>] 0) (𝓝 (8*eval v₀ leadingDeterminant)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have he (P : Poly) : Tendsto (fun t : ℝ => eval (v t) P)
      (𝓝[>] 0) (𝓝 (eval v₀ P)) :=
    (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp hv
  have hlim := ((((he leadingDeterminant).add
    ((ht.pow 2).mul (he determinantTerm20))).add
    ((ht.pow 4).mul (he determinantTerm22))).add
    ((ht.pow 6).mul (he determinantTerm24))).add
    ((ht.pow 8).mul (he determinantTerm26))
  have hlim' : Tendsto (fun t : ℝ => 8*
      (eval (v t) leadingDeterminant + t^2*eval (v t) determinantTerm20 +
        t^4*eval (v t) determinantTerm22 + t^6*eval (v t) determinantTerm24 +
        t^8*eval (v t) determinantTerm26))
      (𝓝[>] 0) (𝓝 (8*eval v₀ leadingDeterminant)) := by
    simpa using hlim.const_mul 8
  apply (tendsto_congr' ?_).2 hlim'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  rw [determinant_weightedScale]
  field_simp [ne_of_gt htpos] <;> ring

namespace CorrectionFamily

variable {δ σ : ℝ} (F : CorrectionFamily δ σ)

theorem matched_q_zero (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    q 0 (F.scaledPoint ε t) = 34*t^16*ε^2*δ^2 := by
  rw [scaledPoint, q_zero_weightedScale,
    F.matchedA ε t hε ht, F.matchedB ε t hε ht, F.matchedW ε t hε ht]
  ring

theorem matched_q_one (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    q 1 (F.scaledPoint ε t) = 6*t^16*ε^2*δ^2 := by
  rw [scaledPoint, q_one_weightedScale,
    F.matchedA ε t hε ht, F.matchedB ε t hε ht, F.matchedW ε t hε ht]
  ring

theorem matched_q_three (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    q 3 (F.scaledPoint ε t) = 6*t^16*ε^2*δ^2 := by
  rw [scaledPoint, q_three_weightedScale,
    F.matchedA ε t hε ht, F.matchedB ε t hε ht, F.matchedW ε t hε ht]
  ring

theorem tendsto_leadingG_div :
    Tendsto (fun ε : ℝ => eval (F.point ε 0) leadingG/ε)
      (𝓝[>] 0) (𝓝 (1-σ*δ)) := by
  simpa only [differential_leadingG_normal_sign] using
    F.tendsto_eval_point_div leadingG eval_base_leadingG

theorem tendsto_leadingDeterminant_div :
    Tendsto (fun ε : ℝ => eval (F.point ε 0) leadingDeterminant/ε)
      (𝓝[>] 0) (𝓝 (σ*δ)) := by
  simpa only [differential_leadingDeterminant_normal_sign] using
    F.tendsto_eval_point_div leadingDeterminant eval_base_leadingDeterminant

end CorrectionFamily

end

end PBCounterexample.Gram5
