import PBCounterexample.Gram5WeightedKernel
import PBCounterexample.Gram5Paths

/-! Removal of exactly matched components from arbitrary polynomial leaves. -/

namespace PBCounterexample.Gram5

open MvPolynomial

noncomputable section

def component (P : Poly) (n : ℕ) : Poly := weightedHomogeneousComponent weights n P

theorem component_weighted (P : Poly) (n : ℕ) :
    (component P n).IsWeightedHomogeneous weights n :=
  weightedHomogeneousComponent_isWeightedHomogeneous (w := weights) n P

private theorem exceptional_fourteen (P : Poly) (h : IsExceptional 14 P) :
    ∃ r : ℝ, P = C r*invariantA := by
  rcases h with h | ⟨_, r, hr⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨0, by simpa only [map_zero, zero_mul] using h⟩
  · exact ⟨r, hr⟩
  · norm_num at h
  · norm_num at h

private theorem exceptional_fifteen (P : Poly) (h : IsExceptional 15 P) :
    ∃ r : ℝ, P = C r*invariantB := by
  rcases h with h | ⟨h, _⟩ | ⟨_, r, hr⟩ | ⟨h, _⟩
  · exact ⟨0, by simpa only [map_zero, zero_mul] using h⟩
  · norm_num at h
  · exact ⟨r, hr⟩
  · norm_num at h

private theorem exceptional_sixteen (P : Poly) (h : IsExceptional 16 P) :
    ∃ r : ℝ, P = C r*invariantW := by
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, r, hr⟩
  · exact ⟨0, by simpa only [map_zero, zero_mul] using h⟩
  · norm_num at h
  · norm_num at h
  · exact ⟨r, hr⟩

structure LeafDecomposition (P : Poly) where
  remainder : Poly
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  equality : P = remainder + C alpha*invariantA + C beta*invariantB + C gamma*invariantW
  clean : ∀ n : ℕ, IsExceptional n (component remainder n) → component remainder n = 0

theorem exists_leafDecomposition (P : Poly) : Nonempty (LeafDecomposition P) := by
  classical
  have hchoose14 : ∃ α : ℝ,
      (IsExceptional 14 (component P 14) → component P 14 = C α*invariantA) ∧
      (¬ IsExceptional 14 (component P 14) → α = 0) := by
    by_cases h : IsExceptional 14 (component P 14)
    · obtain ⟨r, hr⟩ := exceptional_fourteen _ h
      exact ⟨r, fun _ => hr, fun hnot => False.elim (hnot h)⟩
    · exact ⟨0, fun hyes => False.elim (h hyes), fun _ => rfl⟩
  have hchoose15 : ∃ β : ℝ,
      (IsExceptional 15 (component P 15) → component P 15 = C β*invariantB) ∧
      (¬ IsExceptional 15 (component P 15) → β = 0) := by
    by_cases h : IsExceptional 15 (component P 15)
    · obtain ⟨r, hr⟩ := exceptional_fifteen _ h
      exact ⟨r, fun _ => hr, fun hnot => False.elim (hnot h)⟩
    · exact ⟨0, fun hyes => False.elim (h hyes), fun _ => rfl⟩
  have hchoose16 : ∃ γ : ℝ,
      (IsExceptional 16 (component P 16) → component P 16 = C γ*invariantW) ∧
      (¬ IsExceptional 16 (component P 16) → γ = 0) := by
    by_cases h : IsExceptional 16 (component P 16)
    · obtain ⟨r, hr⟩ := exceptional_sixteen _ h
      exact ⟨r, fun _ => hr, fun hnot => False.elim (hnot h)⟩
    · exact ⟨0, fun hyes => False.elim (h hyes), fun _ => rfl⟩
  obtain ⟨α, hα, hα0⟩ := hchoose14
  obtain ⟨β, hβ, hβ0⟩ := hchoose15
  obtain ⟨γ, hγ, hγ0⟩ := hchoose16
  let R := P-C α*invariantA-C β*invariantB-C γ*invariantW
  have hcomp (n : ℕ) : component R n = component P n -
      (if n = 14 then C α*invariantA else 0) -
      (if n = 15 then C β*invariantB else 0) -
      (if n = 16 then C γ*invariantW else 0) := by
    simp only [R, component, map_sub,
      weightedHomogeneousComponent_of_mem (invariantA_weighted.C_mul α),
      weightedHomogeneousComponent_of_mem (invariantB_weighted.C_mul β),
      weightedHomogeneousComponent_of_mem (invariantW_weighted.C_mul γ)]
  have hclean (n : ℕ) : IsExceptional n (component R n) → component R n = 0 := by
    by_cases h14 : n = 14
    · subst n
      by_cases h : IsExceptional 14 (component P 14)
      · intro _
        simpa [hα h] using hcomp 14
      · have hsame : component R 14 = component P 14 := by simpa [hα0 h] using hcomp 14
        intro hr
        exact False.elim (h (hsame ▸ hr))
    by_cases h15 : n = 15
    · subst n
      by_cases h : IsExceptional 15 (component P 15)
      · intro _
        simpa [hβ h] using hcomp 15
      · have hsame : component R 15 = component P 15 := by simpa [hβ0 h] using hcomp 15
        intro hr
        exact False.elim (h (hsame ▸ hr))
    by_cases h16 : n = 16
    · subst n
      by_cases h : IsExceptional 16 (component P 16)
      · intro _
        simpa [hγ h] using hcomp 16
      · have hsame : component R 16 = component P 16 := by simpa [hγ0 h] using hcomp 16
        intro hr
        exact False.elim (h (hsame ▸ hr))
    intro hr
    rcases hr with hr | ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩
    · exact hr
    · exact False.elim (h14 hr)
    · exact False.elim (h15 hr)
    · exact False.elim (h16 hr)
  refine ⟨⟨R, α, β, γ, ?_, hclean⟩⟩
  dsimp [R]
  ring

namespace LeafDecomposition

variable {P : Poly} (L : LeafDecomposition P)

def commonCoefficient : ℝ := L.alpha + 3*L.beta/8 + 3*L.gamma

theorem eval_scaled {δ σ : ℝ} (F : CorrectionFamily δ σ)
    (ε t : ℝ) (hε : |ε| < F.radius) (ht : |t| < F.radius) :
    eval (F.scaledPoint ε t) P = eval (F.scaledPoint ε t) L.remainder +
      t^16*L.commonCoefficient*ε^2*δ^2 := by
  have hA := WeightedPolynomial.eval_scale_of_weightedHomogeneous invariantA_weighted
    (F.point ε t) t
  have hB := WeightedPolynomial.eval_scale_of_weightedHomogeneous invariantB_weighted
    (F.point ε t) t
  have hW := WeightedPolynomial.eval_scale_of_weightedHomogeneous invariantW_weighted
    (F.point ε t) t
  change eval (F.scaledPoint ε t) invariantA = t^14*eval (F.point ε t) invariantA at hA
  change eval (F.scaledPoint ε t) invariantB = t^15*eval (F.point ε t) invariantB at hB
  change eval (F.scaledPoint ε t) invariantW = t^16*eval (F.point ε t) invariantW at hW
  conv_lhs => rw [L.equality]
  simp only [map_add, map_mul, eval_C, hA, hB, hW,
    F.matchedA ε t hε ht, F.matchedB ε t hε ht, F.matchedW ε t hε ht,
    commonCoefficient]
  ring

theorem first_component_value_or_derivative (m : ℕ) (hm : m ≤ 16)
    (hne : component L.remainder m ≠ 0) :
    eval basePoint (component L.remainder m) ≠ 0 ∨
      differential (component L.remainder m) normalDirection ≠ 0 := by
  apply value_or_derivative_ne_zero_of_notExceptional _ m (component_weighted _ _) hm
  exact fun h => hne (L.clean m h)

end LeafDecomposition

end

end PBCounterexample.Gram5
