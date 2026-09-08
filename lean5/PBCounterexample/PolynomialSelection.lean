import PBCounterexample.Semialgebraic
import PBCounterexample.RadialPolynomial

/-!
# A finite polynomial minimum selected by a polynomial inequality

When strict positivity of the minimum implies that the selecting polynomial
is nonzero, the selection admits a finite closed polynomial cover.
-/

namespace PBCounterexample.PolynomialSelection

open MvPolynomial

variable {σ α : Type*} [Fintype α] [Nonempty α]
variable (Q : α → MvPolynomial σ ℝ) (d : MvPolynomial σ ℝ)

noncomputable def minimum (z : σ → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a => eval z (Q a))

noncomputable def f (z : σ → ℝ) : ℝ :=
  if 0 < minimum Q z ∧ 0 < eval z d then minimum Q z else 0

theorem minimum_le (z : σ → ℝ) (a : α) : minimum Q z ≤ eval z (Q a) :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem le_minimum_iff (z : σ → ℝ) (r : ℝ) :
    r ≤ minimum Q z ↔ ∀ a, r ≤ eval z (Q a) := by
  simp [minimum]

theorem exists_minimum_eq (z : σ → ℝ) :
    ∃ a, minimum Q z = eval z (Q a) := by
  simpa [minimum] using
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun a => eval z (Q a))

theorem continuous_minimum : Continuous (minimum Q) :=
  Continuous.finset_inf'_apply _ (fun a _ => MvPolynomial.continuous_eval (Q a))

noncomputable def zeroRegion : Set (σ → ℝ) :=
  {z | eval z d ≤ 0} ∪ ⋃ a : α, {z | eval z (Q a) ≤ 0}

noncomputable def polynomialRegion (a : α) : Set (σ → ℝ) :=
  {z | 0 ≤ eval z d} ∩ (⋂ b : α, {z | 0 ≤ eval z (Q b)}) ∩
    (⋂ b : α, {z | eval z (Q a) ≤ eval z (Q b)})

noncomputable def region : Option α → Set (σ → ℝ)
  | none => zeroRegion Q d
  | some a => polynomialRegion Q d a

noncomputable def label : Option α → MvPolynomial σ ℝ
  | none => 0
  | some a => Q a

theorem isClosed_zeroRegion : IsClosed (zeroRegion Q d) :=
  (isClosed_le (MvPolynomial.continuous_eval d) continuous_const).union
    (isClosed_iUnion_of_finite fun a =>
      isClosed_le (MvPolynomial.continuous_eval (Q a)) continuous_const)

theorem isClosed_polynomialRegion (a : α) : IsClosed (polynomialRegion Q d a) :=
  ((isClosed_le continuous_const (MvPolynomial.continuous_eval d)).inter
    (isClosed_iInter fun b =>
      isClosed_le continuous_const (MvPolynomial.continuous_eval (Q b)))).inter
    (isClosed_iInter fun b => isClosed_le
      (MvPolynomial.continuous_eval (Q a)) (MvPolynomial.continuous_eval (Q b)))

theorem semialgebraic_zeroRegion : IsSemialgebraic (zeroRegion Q d) :=
  (IsSemialgebraic.polynomial_le d).union
    (IsSemialgebraic.iUnion _ fun a => IsSemialgebraic.polynomial_le (Q a))

theorem semialgebraic_polynomialRegion (a : α) :
    IsSemialgebraic (polynomialRegion Q d a) :=
  ((IsSemialgebraic.ge_zero d).inter
    (IsSemialgebraic.iInter _ fun b => IsSemialgebraic.ge_zero (Q b))).inter
    (IsSemialgebraic.iInter _ fun b => IsSemialgebraic.le (Q a) (Q b))

theorem f_zero {z : σ → ℝ} (hz : z ∈ zeroRegion Q d) : f Q d z = 0 := by
  rcases hz with hd | hq
  · change eval z d ≤ 0 at hd
    simp [f, not_lt_of_ge hd]
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hq
    have hh : minimum Q z ≤ 0 := le_trans (minimum_le Q z a) ha
    simp [f, not_lt_of_ge hh]

theorem minimum_eq_on_region {z : σ → ℝ} {a : α}
    (hz : z ∈ polynomialRegion Q d a) : minimum Q z = eval z (Q a) := by
  apply le_antisymm (minimum_le Q z a)
  exact (le_minimum_iff Q z _).mpr (Set.mem_iInter.mp hz.2)

theorem f_eq_on_region (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0)
    {z : σ → ℝ} {a : α}
    (hz : z ∈ polynomialRegion Q d a) : f Q d z = eval z (Q a) := by
  have heq := minimum_eq_on_region Q d hz
  have hnonneg : 0 ≤ minimum Q z := by
    rw [heq]
    exact Set.mem_iInter.mp hz.1.2 a
  by_cases hh : 0 < minimum Q z
  · have hd : 0 < eval z d := lt_of_le_of_ne hz.1.1 (Ne.symm (hseparate z hh))
    rw [f, ite_eq_left ⟨hh, hd⟩, heq]
  · have hzero : minimum Q z = 0 := le_antisymm (le_of_not_gt hh) hnonneg
    have hqzero : eval z (Q a) = 0 := heq.symm.trans hzero
    simp [f, hh, hqzero]

theorem region_covers_point (z : σ → ℝ) : ∃ a, z ∈ region Q d a := by
  classical
  by_cases hz : z ∈ zeroRegion Q d
  · exact ⟨none, hz⟩
  · have hd : 0 ≤ eval z d := by
      by_contra hd
      exact hz (Or.inl (le_of_lt (lt_of_not_ge hd)))
    have hq : ∀ b, 0 ≤ eval z (Q b) := by
      intro b
      by_contra hb
      exact hz (Or.inr (Set.mem_iUnion.mpr ⟨b, le_of_lt (lt_of_not_ge hb)⟩))
    obtain ⟨a, ha⟩ := exists_minimum_eq Q z
    refine ⟨some a, ⟨⟨hd, Set.mem_iInter.mpr hq⟩, Set.mem_iInter.mpr ?_⟩⟩
    intro b
    change eval z (Q a) ≤ eval z (Q b)
    rw [← ha]
    exact minimum_le Q z b

theorem region_agrees (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0)
    (a : Option α) (z : σ → ℝ) (hz : z ∈ region Q d a) :
    f Q d z = eval z (label Q a) := by
  cases a with
  | none => simpa [label] using f_zero Q d hz
  | some a => exact f_eq_on_region Q d hseparate hz

noncomputable def polynomialCover
    (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0) :
    FiniteClosedPolynomialCover (f Q d) where
  count := Fintype.card (Option α)
  region i := region Q d ((Fintype.equivFin (Option α)).symm i)
  label i := label Q ((Fintype.equivFin (Option α)).symm i)
  closed i := by
    cases (Fintype.equivFin (Option α)).symm i with
    | none => exact isClosed_zeroRegion Q d
    | some a => exact isClosed_polynomialRegion Q d a
  semialgebraic i := by
    cases (Fintype.equivFin (Option α)).symm i with
    | none => exact semialgebraic_zeroRegion Q d
    | some a => exact semialgebraic_polynomialRegion Q d a
  covers := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := region_covers_point Q d z
    exact ⟨Fintype.equivFin (Option α) a, by simpa using ha⟩
  agrees i z hz := region_agrees Q d hseparate _ z hz

theorem continuous_f (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0) :
    Continuous (f Q d) :=
  (polynomialCover Q d hseparate).continuous

theorem polynomialCover_count
    (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0) :
    (polynomialCover Q d hseparate).count = Fintype.card α + 1 :=
  Fintype.card_option

theorem polynomialCover_homogeneous
    (hseparate : ∀ z, 0 < minimum Q z → eval z d ≠ 0)
    {k : ℕ} (hQ : ∀ a, (Q a).IsHomogeneous k)
    (i : Fin (polynomialCover Q d hseparate).count) :
    ((polynomialCover Q d hseparate).label i).IsHomogeneous k := by
  change (label Q _).IsHomogeneous k
  cases (Fintype.equivFin (Option α)).symm i with
  | none => exact MvPolynomial.isHomogeneous_zero _ _ _
  | some a => exact hQ a

theorem minimum_smul (hQ : ∀ a, (Q a).IsHomogeneous 2) (t : ℝ) (z : σ → ℝ) :
    minimum Q (t • z) = t ^ 2 * minimum Q z := by
  have hscale (a : α) : eval (t • z) (Q a) = t ^ 2 * eval z (Q a) := by
    exact Radial.eval_homogeneous_scale (hQ a) z t
  obtain ⟨a, ha⟩ := exists_minimum_eq Q z
  obtain ⟨b, hb⟩ := exists_minimum_eq Q (t • z)
  apply le_antisymm
  · calc
      minimum Q (t • z) ≤ eval (t • z) (Q a) := minimum_le Q _ a
      _ = t ^ 2 * eval z (Q a) := hscale a
      _ = t ^ 2 * minimum Q z := by rw [ha]
  · calc
      t ^ 2 * minimum Q z ≤ t ^ 2 * eval z (Q b) :=
        mul_le_mul_of_nonneg_left (minimum_le Q z b) (sq_nonneg t)
      _ = eval (t • z) (Q b) := (hscale b).symm
      _ = minimum Q (t • z) := hb.symm

theorem f_positive_homogeneous (hQ : ∀ a, (Q a).IsHomogeneous 2)
    (hd : ∀ t : ℝ, 0 < t → ∀ z : σ → ℝ,
      (0 < eval (t • z) d ↔ 0 < eval z d))
    (t : ℝ) (ht : 0 < t) (z : σ → ℝ) :
    f Q d (t • z) = t ^ 2 * f Q d z := by
  have hpos : 0 < minimum Q (t • z) ↔ 0 < minimum Q z := by
    rw [minimum_smul Q hQ]
    exact mul_pos_iff_of_pos_left (pow_pos ht 2)
  simp only [f, hpos, hd t ht z]
  split_ifs
  · exact minimum_smul Q hQ t z
  · simp

end PBCounterexample.PolynomialSelection
