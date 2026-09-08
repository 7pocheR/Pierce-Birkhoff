import PBCounterexample.Gram5LeafLimits
import PBCounterexample.LatticeThreshold

/-! One simultaneous pair of real points for every finite family of polynomial leaves. -/

namespace PBCounterexample.Gram5

open MvPolynomial Filter
open scoped Topology

noncomputable section

/-- A single fixed positive epsilon and actual correction families work for
every sufficiently small positive scaling parameter. -/
theorem exists_finite_threshold_paths (S : Finset Poly) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      ∃ (Fplus : CorrectionFamily δ 1) (Fminus : CorrectionFamily δ (-1)),
        ∃ ε : ℝ, 0 < ε ∧ |ε| < Fplus.radius ∧ |ε| < Fminus.radius ∧
          ∀ᶠ t : ℝ in 𝓝[>] 0,
            f (Fplus.scaledPoint ε t) = 6*t^16*ε^2*δ^2 ∧
            f (Fminus.scaledPoint ε t) = 0 ∧
            ∀ P ∈ S, f (Fplus.scaledPoint ε t) ≤ eval (Fplus.scaledPoint ε t) P →
              0 < eval (Fminus.scaledPoint ε t) P := by
  classical
  let L : (P : Poly) → LeafDecomposition P :=
    fun P => Classical.choice (exists_leafDecomposition P)
  let tests : Finset Poly := S.biUnion fun P =>
    Finset.univ.image (fun m : Fin 17 => component (L P).remainder m)
  obtain ⟨δ, hδ, hδsmall, htestsδ⟩ := exists_delta_finite_tests tests
  obtain ⟨Fplus⟩ := exists_correctionFamily δ 1 hδ (by norm_num)
  obtain ⟨Fminus⟩ := exists_correctionFamily δ (-1) hδ (by norm_num)
  have hepsilon (P : Poly) (hP : P ∈ S) (m : Fin 17) :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        component (L P).remainder m ≠ 0 →
          SameStrictSign ((L P).effectiveValue Fplus m ε)
            ((L P).effectiveValue Fminus m ε) := by
    by_cases hzero : component (L P).remainder m = 0
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hzero)
    have hm : (m : ℕ) ≤ 16 := Nat.le_of_lt_succ m.isLt
    have hnonzero := (L P).first_component_value_or_derivative m hm hzero
    have hmem : component (L P).remainder m ∈ tests := by
      exact Finset.mem_biUnion.mpr ⟨P, hP,
        Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩⟩
    have hcondition : eval basePoint (component (L P).remainder m) ≠ 0 ∨
        SameStrictSign
          (differential (component (L P).remainder m)
            (normalDirection + δ • signDirection))
          (differential (component (L P).remainder m)
            (normalDirection + (-δ) • signDirection)) := by
      rcases hnonzero with hvalue | hderiv
      · exact Or.inl hvalue
      · exact Or.inr (htestsδ _ hmem hderiv)
    have hh := eventually_sameStrictSign_shifted Fplus Fminus
      (component (L P).remainder m)
      (if (m : ℕ) = 16 then (L P).commonCoefficient else 0) hcondition
    filter_upwards [hh] with ε hε
    intro _
    by_cases hm16 : (m : ℕ) = 16
    · simpa [LeafDecomposition.effectiveValue, CorrectionFamily.shiftedTest, hm16] using hε
    · simpa [LeafDecomposition.effectiveValue, CorrectionFamily.shiftedTest, hm16] using hε
  have hepsilonAll : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ P ∈ S, ∀ m : Fin 17,
      component (L P).remainder m ≠ 0 →
        SameStrictSign ((L P).effectiveValue Fplus m ε)
          ((L P).effectiveValue Fminus m ε) :=
    (eventually_all_finset S).mpr fun P hP =>
      eventually_all.mpr (hepsilon P hP)
  have hchooseε : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ |ε| < Fplus.radius ∧ |ε| < Fminus.radius ∧
      0 < eval (Fplus.point ε 0) leadingG ∧
      0 < eval (Fplus.point ε 0) leadingDeterminant ∧
      eval (Fminus.point ε 0) leadingDeterminant < 0 ∧
      ∀ P ∈ S, ∀ m : Fin 17, component (L P).remainder m ≠ 0 →
        SameStrictSign ((L P).effectiveValue Fplus m ε)
          ((L P).effectiveValue Fminus m ε) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_abs_lt_radius Fplus.radius_pos,
      eventually_abs_lt_radius Fminus.radius_pos,
      Fplus.eventually_leadingG_pos (by linarith : (1 : ℝ)*δ < 1),
      Fplus.eventually_leadingDeterminant_pos (by simpa using hδ),
      Fminus.eventually_leadingDeterminant_neg (by linarith : (-1 : ℝ)*δ < 0),
      hepsilonAll] with ε hε hp hm hg hGplus hGminus hleaves
    exact ⟨hε, hp, hm, hg, hGplus, hGminus, hleaves⟩
  obtain ⟨ε, hε0, hεp, hεm, hg, hGplus, hGminus, hεtests⟩ := hchooseε.exists
  have hleaf (P : Poly) (hP : P ∈ S) : ∀ᶠ t : ℝ in 𝓝[>] 0,
      6*t^16*ε^2*δ^2 ≤ eval (Fplus.scaledPoint ε t) P →
        0 < eval (Fminus.scaledPoint ε t) P := by
    rcases (L P).first_component_or_zero with ⟨m, hm, hne, hbelow⟩ | hthrough
    · have hsign := hεtests P hP ⟨m, Nat.lt_succ_of_le hm⟩ hne
      exact (L P).eventually_transfer_first Fplus Fminus ε hεp hεm m hm hbelow hsign
    · exact (L P).eventually_transfer_zero Fplus Fminus ε hε0 hδ hεp hεm hthrough
  have hall : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ P ∈ S,
      6*t^16*ε^2*δ^2 ≤ eval (Fplus.scaledPoint ε t) P →
        0 < eval (Fminus.scaledPoint ε t) P :=
    (eventually_all_finset S).mpr hleaf
  have hfinal : ∀ᶠ t : ℝ in 𝓝[>] 0,
      f (Fplus.scaledPoint ε t) = 6*t^16*ε^2*δ^2 ∧
      f (Fminus.scaledPoint ε t) = 0 ∧
      ∀ P ∈ S, f (Fplus.scaledPoint ε t) ≤ eval (Fplus.scaledPoint ε t) P →
        0 < eval (Fminus.scaledPoint ε t) P := by
    filter_upwards [hall,
      Fplus.eventually_f_positive_height ε hε0 hδ hεp hg hGplus,
      Fminus.eventually_f_zero ε hεm hGminus] with t ht hp hm
    refine ⟨hp.1, hm, ?_⟩
    intro P hP hlarge
    exact ht P hP (hp.1 ▸ hlarge)
  exact ⟨δ, hδ, hδsmall, Fplus, Fminus, ε, hε0, hεp, hεm, hfinal⟩

theorem exists_finite_threshold_pair (S : Finset Poly) :
    ∃ x y : Coord, 0 < f x ∧ f y = 0 ∧
      ∀ P ∈ S, f x ≤ eval x P → 0 < eval y P := by
  obtain ⟨δ, hδ, _, Fplus, Fminus, ε, hε, _, _, hh⟩ := exists_finite_threshold_paths S
  have hall := hh.and (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htpos⟩ := hall.exists
  change 0 < t at htpos
  refine ⟨Fplus.scaledPoint ε t, Fminus.scaledPoint ε t, ?_, ht.2.1, ht.2.2⟩
  rw [ht.1]
  positivity

theorem not_isPolynomialLattice : ¬ IsPolynomialLattice f :=
  not_isPolynomialLattice_of_finite_threshold_pairs f exists_finite_threshold_pair

end

end PBCounterexample.Gram5
