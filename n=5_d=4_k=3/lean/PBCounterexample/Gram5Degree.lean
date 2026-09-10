import PBCounterexample.Gram5LowWeights
import PBCounterexample.Gram5Scaling

/-! The four actual polynomial labels have ordinary total degree at most three. -/

namespace PBCounterexample.Gram5

open MvPolynomial

noncomputable section

private theorem degree_three_of_weighted {P : Poly} {m : ℕ}
    (hP : P.IsWeightedHomogeneous weights m) (hm : m ≤ 16) : P.totalDegree ≤ 3 :=
  low_weight_totalDegree P (fun u hu => (hP (mem_support_iff.mp hu)).le.trans hm)

private theorem degree_three_add {P Q : Poly}
    (hP : P.totalDegree ≤ 3) (hQ : Q.totalDegree ≤ 3) : (P+Q).totalDegree ≤ 3 :=
  (totalDegree_add P Q).trans (max_le hP hQ)

private theorem degree_three_sub {P Q : Poly}
    (hP : P.totalDegree ≤ 3) (hQ : Q.totalDegree ≤ 3) : (P-Q).totalDegree ≤ 3 :=
  (totalDegree_sub P Q).trans (max_le hP hQ)

private theorem degree_three_C_mul {P : Poly}
    (hP : P.totalDegree ≤ 3) (r : ℝ) : (C r*P).totalDegree ≤ 3 := by
  exact (totalDegree_mul _ _).trans (by simpa using hP)

theorem labelRemainder14_weighted :
    labelRemainder14.IsWeightedHomogeneous weights 14 := by
  have h0 : (-80*a*e).IsWeightedHomogeneous weights 14 := by
    simpa only [map_neg, map_ofNat] using (a_weighted.C_mul (-80)).mul e_weighted
  have h1 : (64*b*d).IsWeightedHomogeneous weights 14 := by
    simpa only [map_ofNat] using (b_weighted.C_mul 64).mul d_weighted
  have h2 : (144*c^2).IsWeightedHomogeneous weights 14 := by
    simpa [map_ofNat, nsmul_eq_mul] using (c_weighted.pow 2).C_mul 144
  exact (h0.sub h1).add h2

theorem labelRemainder16_weighted :
    labelRemainder16.IsWeightedHomogeneous weights 16 := by
  have h0 : (128*c*e).IsWeightedHomogeneous weights 16 := by
    simpa only [map_ofNat] using (c_weighted.C_mul 128).mul e_weighted
  have h1 : (48*d^2).IsWeightedHomogeneous weights 16 := by
    simpa [map_ofNat, nsmul_eq_mul] using (d_weighted.pow 2).C_mul 48
  have h2 : (80*a^2*b).IsWeightedHomogeneous weights 16 := by
    simpa [map_ofNat, nsmul_eq_mul] using
      ((a_weighted.pow 2).C_mul 80).mul b_weighted
  exact (h0.sub h1).sub h2

theorem qPolynomial_totalDegree (i : Label) : (qPolynomial i).totalDegree ≤ 3 := by
  have hA := degree_three_of_weighted invariantA_weighted (by norm_num)
  have hB := degree_three_of_weighted invariantB_weighted (by norm_num)
  have hW := degree_three_of_weighted invariantW_weighted (by norm_num)
  have hg := degree_three_of_weighted leadingG_weighted (by norm_num)
  have h14 := degree_three_of_weighted labelRemainder14_weighted (by norm_num)
  have h16 := degree_three_of_weighted labelRemainder16_weighted (by norm_num)
  have heq : qPolynomial =
      ![C 16*invariantA-C 80*invariantB+C 16*invariantW,
        C 48*invariantA+C 16*invariantB-C 16*invariantW,
        C 192*leadingG+labelRemainder14+C 16*invariantB+labelRemainder16,
        C (-48)*invariantA+C 16*invariantB+C 16*invariantW] := by
    funext j
    fin_cases j <;>
      norm_num [qPolynomial, gramA, gramB, gramE, gramF, invariantA, invariantB,
        invariantW, leadingG, labelRemainder14, labelRemainder16, map_ofNat, map_neg] <;> ring
  rw [heq]
  fin_cases i
  · exact degree_three_add
      (degree_three_sub (degree_three_C_mul hA 16) (degree_three_C_mul hB 80))
      (degree_three_C_mul hW 16)
  · exact degree_three_sub
      (degree_three_add (degree_three_C_mul hA 48) (degree_three_C_mul hB 16))
      (degree_three_C_mul hW 16)
  · exact degree_three_add
      (degree_three_add (degree_three_add (degree_three_C_mul hg 192) h14)
        (degree_three_C_mul hB 16)) h16
  · exact degree_three_add
      (degree_three_add (degree_three_C_mul hA (-48)) (degree_three_C_mul hB 16))
      (degree_three_C_mul hW 16)

theorem polynomialCover_totalDegree (i : Fin polynomialCover.count) :
    (polynomialCover.label i).totalDegree ≤ 3 := by
  rcases polynomialCover_label i with h | ⟨j, h⟩
  · simp [h]
  · rw [h]
    exact qPolynomial_totalDegree j

end

end PBCounterexample.Gram5
