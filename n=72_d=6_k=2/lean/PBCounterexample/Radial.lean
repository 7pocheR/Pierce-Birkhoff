import PBCounterexample.Basic
import PBCounterexample.RadialPolynomial

/-!
# The finite sign condition imposed by positive quadratic homogeneity

The polynomial leaves are unrestricted. The sign tests are their homogeneous
components of degrees one and two. Limits are taken after clamping normalized
leaves to a compact real interval; sign is applied only after taking those
limits.
-/

namespace PBCounterexample

open Filter Topology

noncomputable section

variable {σ : Type*}

namespace LatticeExpr

def evalWith (v : MvPolynomial σ ℝ → ℝ) : LatticeExpr σ → ℝ
  | .leaf p => v p
  | .sup a b => max (evalWith v a) (evalWith v b)
  | .inf a b => min (evalWith v a) (evalWith v b)

theorem evalWith_eval (e : LatticeExpr σ) (z : σ → ℝ) :
    e.evalWith (fun p => MvPolynomial.eval z p) = e.eval z := by
  induction e <;> simp_all [evalWith, eval]

theorem map_evalWith (e : LatticeExpr σ) (v : MvPolynomial σ ℝ → ℝ)
    (f : ℝ → ℝ) (hf : Monotone f) :
    f (e.evalWith v) = e.evalWith (fun p => f (v p)) := by
  induction e <;> simp_all [evalWith, hf.map_max, hf.map_min]

def leaves : LatticeExpr σ → Finset (MvPolynomial σ ℝ)
  | .leaf p => {p}
  | .sup a b => by classical exact a.leaves ∪ b.leaves
  | .inf a b => by classical exact a.leaves ∪ b.leaves

theorem evalWith_congr (e : LatticeExpr σ) (v w : MvPolynomial σ ℝ → ℝ)
    (h : ∀ p ∈ e.leaves, v p = w p) : e.evalWith v = e.evalWith w := by
  classical
  induction e with
  | leaf p => exact h p (Finset.mem_singleton_self p)
  | sup a b ha hb =>
    have h₁ : ∀ p ∈ a.leaves, v p = w p := fun p hp => h p (Finset.mem_union_left _ hp)
    have h₂ : ∀ p ∈ b.leaves, v p = w p := fun p hp => h p (Finset.mem_union_right _ hp)
    simp only [evalWith, ha h₁, hb h₂]
  | inf a b ha hb =>
    have h₁ : ∀ p ∈ a.leaves, v p = w p := fun p hp => h p (Finset.mem_union_left _ hp)
    have h₂ : ∀ p ∈ b.leaves, v p = w p := fun p hp => h p (Finset.mem_union_right _ hp)
    simp only [evalWith, ha h₁, hb h₂]

theorem tendsto_evalWith (e : LatticeExpr σ) {ι : Type*} {F : Filter ι}
    (v : ι → MvPolynomial σ ℝ → ℝ) (w : MvPolynomial σ ℝ → ℝ)
    (h : ∀ p, Tendsto (fun t => v t p) F (𝓝 (w p))) :
    Tendsto (fun t => e.evalWith (v t)) F (𝓝 (e.evalWith w)) := by
  induction e with
  | leaf p => exact h p
  | sup a b ha hb => exact ha.max hb
  | inf a b ha hb => exact ha.min hb

def lowDegreeTests (e : LatticeExpr σ) : Finset (MvPolynomial σ ℝ) := by
  classical
  exact e.leaves.biUnion (fun p =>
    {MvPolynomial.homogeneousComponent 1 p, MvPolynomial.homogeneousComponent 2 p})

theorem lowDegreeTests_degree (e : LatticeExpr σ) :
    ∀ p ∈ e.lowDegreeTests, p.totalDegree ≤ 2 := by
  classical
  intro p hp
  obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.1 hp
  rcases Finset.mem_insert.1 hp with rfl | hp
  · exact (MvPolynomial.homogeneousComponent_isHomogeneous 1 q).totalDegree_le.trans (by omega)
  · have : p = MvPolynomial.homogeneousComponent 2 q := Finset.mem_singleton.1 hp
    subst p
    exact (MvPolynomial.homogeneousComponent_isHomogeneous 2 q).totalDegree_le

theorem normalized_clip (e : LatticeExpr σ) (z : σ → ℝ) (t : ℝ) :
    e.evalWith (fun p => Radial.clip (MvPolynomial.eval (fun i => t * z i) p / t ^ 2)) =
      Radial.clip (e.eval (fun i => t * z i) / t ^ 2) := by
  have hmono : Monotone (fun x : ℝ => Radial.clip (x / t ^ 2)) := by
    intro x y hxy
    exact Radial.monotone_clip (div_le_div_of_nonneg_right hxy (sq_nonneg t))
  exact (e.map_evalWith (fun p => MvPolynomial.eval (fun i => t * z i) p)
    (fun x => Radial.clip (x / t ^ 2)) hmono).symm.trans
      (congrArg (fun x => Radial.clip (x / t ^ 2)) (e.evalWith_eval _))

theorem clipped_homogeneous_eval (e : LatticeExpr σ)
    (g : (σ → ℝ) → ℝ)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (fun i => t * z i) = t ^ 2 * g z)
    (he : ∀ z, e.eval z = g z) (z : σ → ℝ) :
    Radial.clip (g z) = e.evalWith (fun p => Radial.leafLimit p z) := by
  have hlim := e.tendsto_evalWith
    (fun t p => Radial.clip (MvPolynomial.eval (fun i => t * z i) p / t ^ 2))
    (fun p => Radial.leafLimit p z) (fun p => Radial.tendsto_clip_mvPolynomial p z)
  have hconst : Tendsto
      (fun t : ℝ => e.evalWith
        (fun p => Radial.clip (MvPolynomial.eval (fun i => t * z i) p / t ^ 2)))
      (𝓝[>] 0) (𝓝 (Radial.clip (g z))) := by
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [e.normalized_clip, he, hg t ht]
    congr 1
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  exact tendsto_nhds_unique hconst hlim

theorem sign_eq_of_lowDegreeTests (e : LatticeExpr σ)
    (g : (σ → ℝ) → ℝ)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (fun i => t * z i) = t ^ 2 * g z)
    (he : ∀ z, e.eval z = g z) (z w : σ → ℝ)
    (hs : ∀ p ∈ e.lowDegreeTests,
      Real.sign (MvPolynomial.eval z p) = Real.sign (MvPolynomial.eval w p)) :
    Real.sign (g z) = Real.sign (g w) := by
  classical
  have hleaf : ∀ p ∈ e.leaves,
      Real.sign (Radial.leafLimit p z) = Real.sign (Radial.leafLimit p w) := by
    intro p hp
    apply Radial.sign_limitingValue_congr
    · exact hs _ (Finset.mem_biUnion.2 ⟨p, hp, by simp⟩)
    · exact hs _ (Finset.mem_biUnion.2 ⟨p, hp, by simp⟩)
  calc
    Real.sign (g z) = Real.sign (Radial.clip (g z)) := (Radial.sign_clip _).symm
    _ = Real.sign (e.evalWith (fun p => Radial.leafLimit p z)) :=
      congrArg Real.sign (e.clipped_homogeneous_eval g hg he z)
    _ = e.evalWith (fun p => Real.sign (Radial.leafLimit p z)) :=
      e.map_evalWith _ _ Radial.monotone_realSign
    _ = e.evalWith (fun p => Real.sign (Radial.leafLimit p w)) :=
      e.evalWith_congr _ _ hleaf
    _ = Real.sign (e.evalWith (fun p => Radial.leafLimit p w)) :=
      (e.map_evalWith _ _ Radial.monotone_realSign).symm
    _ = Real.sign (Radial.clip (g w)) :=
      congrArg Real.sign (e.clipped_homogeneous_eval g hg he w).symm
    _ = Real.sign (g w) := Radial.sign_clip _

end LatticeExpr

/-- Every positive-quadratically homogeneous polynomial lattice function has
its sign determined by finitely many polynomials of total degree at most two. -/
theorem homogeneous_lattice_finite_sign_condition (g : (σ → ℝ) → ℝ)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (fun i => t * z i) = t ^ 2 * g z)
    (hrep : IsPolynomialLattice g) :
    ∃ S : Finset (MvPolynomial σ ℝ),
      (∀ p ∈ S, p.totalDegree ≤ 2) ∧
      ∀ z w, (∀ p ∈ S,
        Real.sign (MvPolynomial.eval z p) = Real.sign (MvPolynomial.eval w p)) →
        Real.sign (g z) = Real.sign (g w) := by
  obtain ⟨e, he⟩ := hrep
  exact ⟨e.lowDegreeTests, e.lowDegreeTests_degree, e.sign_eq_of_lowDegreeTests g hg he⟩

end

end PBCounterexample
