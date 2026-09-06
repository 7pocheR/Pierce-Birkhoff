import Mathlib
import PBCounterexample.OrbitAlgebra
import PBCounterexample.OrbitNormalization

namespace PBCounterexample.OrbitGeometry

open Matrix Filter Topology

abbrev I := Fin 6
abbrev Mat := Matrix I I ℝ
abbrev Pair := Mat × Mat

def D : Mat := diagonal ![1, 1, 0, 0, 0, 0]
def E : Mat := diagonal ![0, 0, 1, 1, 0, 0]

def action (U V : Matˣ) (z : Pair) : Pair :=
  (↑U * z.1 * ↑(V⁻¹), ↑V * z.2 * ↑(U⁻¹))

def orbit : Set Pair := {z | ∃ U V : Matˣ, z = action U V (D, E)}

theorem D_mul_E : D * E = 0 := by
  unfold D E
  rw [diagonal_mul_diagonal]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem E_mul_D : E * D = 0 := by
  unfold D E
  rw [diagonal_mul_diagonal]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem orbit_products_zero (z : Pair) (hz : z ∈ orbit) : z.1 * z.2 = 0 ∧ z.2 * z.1 = 0 := by
  rcases hz with ⟨U, V, rfl⟩
  constructor
  · change ((↑U : Mat) * D * (↑(V⁻¹) : Mat)) * ((↑V : Mat) * E * (↑(U⁻¹) : Mat)) = 0
    calc
      _ = (↑U : Mat) * (D * ((↑(V⁻¹) : Mat) * (↑V : Mat)) * E) * (↑(U⁻¹) : Mat) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by simp [D_mul_E]
  · change ((↑V : Mat) * E * (↑(U⁻¹) : Mat)) * ((↑U : Mat) * D * (↑(V⁻¹) : Mat)) = 0
    calc
      _ = (↑V : Mat) * (E * ((↑(U⁻¹) : Mat) * (↑U : Mat)) * D) * (↑(V⁻¹) : Mat) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by simp [E_mul_D]

@[simp] theorem action_one (z : Pair) : action 1 1 z = z := by
  rcases z with ⟨X, Y⟩
  simp [action]

theorem action_mul (U V A B : Matˣ) (z : Pair) :
    action U V (action A B z) = action (U * A) (V * B) z := by
  simp [action, Matrix.mul_assoc]

theorem action_mem_orbit (U V : Matˣ) {z : Pair} (hz : z ∈ orbit) :
    action U V z ∈ orbit := by
  rcases hz with ⟨A, B, rfl⟩
  exact ⟨U * A, V * B, action_mul U V A B (D, E)⟩

theorem continuous_action (U V : Matˣ) : Continuous (action U V) := by
  unfold action
  fun_prop

theorem action_mem_closure (U V : Matˣ) {z : Pair} (hz : z ∈ closure orbit) :
    action U V z ∈ closure orbit := by
  have h := mem_closure_image (continuous_action U V).continuousAt hz
  exact closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact action_mem_orbit U V hw) h

def normalizedPath (t : ℝ) : Pair :=
  (diagonal ![1, t, 0, 0, 0, 0], diagonal ![0, 0, 1, t, 0, 0])

noncomputable def scalingUnit (t : ℝ) (ht : t ≠ 0) : Matˣ where
  val := diagonal ![1, t, 1, t⁻¹, 1, 1]
  inv := diagonal ![1, t⁻¹, 1, t, 1, 1]
  val_inv := by
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht]
  inv_val := by
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht]

theorem normalizedPath_mem_orbit (t : ℝ) (ht : t ≠ 0) : normalizedPath t ∈ orbit := by
  refine ⟨scalingUnit t ht, 1, ?_⟩
  apply Prod.ext
  · change diagonal ![1, t, 0, 0, 0, 0] =
      diagonal ![1, t, 1, t⁻¹, 1, 1] * D * 1
    rw [Matrix.mul_one]
    unfold D
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · change diagonal ![0, 0, 1, t, 0, 0] =
      1 * E * diagonal ![1, t⁻¹, 1, t, 1, 1]
    rw [Matrix.one_mul]
    unfold E
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem continuous_normalizedPath : Continuous normalizedPath := by
  unfold normalizedPath
  fun_prop

theorem normalizedPath_zero_mem_closure : normalizedPath 0 ∈ closure orbit := by
  have hlim : Tendsto normalizedPath (𝓝[≠] (0 : ℝ)) (𝓝 (normalizedPath 0)) :=
    continuous_normalizedPath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact normalizedPath_mem_orbit t (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht)

theorem normalizedPath_zero : normalizedPath 0 =
    (vecMulVec (Pi.single 0 1) (Pi.single 0 1),
      vecMulVec (Pi.single 2 1) (Pi.single 2 1)) := by
  apply Prod.ext <;> apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp +decide [normalizedPath, Matrix.diagonal, vecMulVec, Pi.single_apply]

theorem rankOne_pair_mem_closure (u v s t : I → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (htu : t ⬝ᵥ u = 0) (hvs : v ⬝ᵥ s = 0) :
    (vecMulVec u v, vecMulVec s t) ∈ closure orbit := by
  obtain ⟨U, hU, hUi⟩ := OrbitNormalization.exists_unit_with_column_and_inverse_row
    (0 : I) 2 (by decide) u t hu ht htu
  obtain ⟨V, hV, hVi⟩ := OrbitNormalization.exists_unit_with_column_and_inverse_row
    (2 : I) 0 (by decide) s v hs hv hvs
  have h := action_mem_closure U V normalizedPath_zero_mem_closure
  rw [normalizedPath_zero] at h
  simpa only [action, mul_vecMulVec, vecMulVec_mul, hU, hUi, hV, hVi] using h

theorem bilinear_orbit_classification
    (B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hB : ∀ z ∈ orbit, B z.1 z.2 = 0) :
    ∃ L M : Mat →ₗ[ℝ] ℝ, ∀ X Y : Mat, B X Y = L (Y * X) + M (X * Y) := by
  have hcont : Continuous (fun z : Pair => B z.1 z.2) := by
    have heq : (fun z : Pair => B z.1 z.2) =
        fun z : Pair => ∑ i, ∑ j, ∑ k, ∑ l,
          B (OrbitAlgebra.unit i j) (OrbitAlgebra.unit k l) * z.1 i j * z.2 k l := by
      funext z
      exact OrbitAlgebra.bilinear_eval_expansion B z.1 z.2
    rw [heq]
    fun_prop
  have hcl : ∀ z ∈ closure orbit, B z.1 z.2 = 0 := by
    exact closure_minimal hB (isClosed_eq hcont continuous_const)
  have hrank : ∀ u v s t : I → ℝ,
      OrbitAlgebra.diagonalSum (OrbitAlgebra.outer u t) = 0 →
      OrbitAlgebra.diagonalSum (OrbitAlgebra.outer s v) = 0 →
      B (OrbitAlgebra.outer u v) (OrbitAlgebra.outer s t) = 0 := by
    intro u v s t hut hsv
    by_cases hu : u = 0
    · subst u; simp only [OrbitAlgebra.outer_eq_vecMulVec, zero_vecMulVec, map_zero,
        LinearMap.zero_apply]
    by_cases hv : v = 0
    · subst v; simp only [OrbitAlgebra.outer_eq_vecMulVec, vecMulVec_zero, map_zero,
        LinearMap.zero_apply]
    by_cases hs : s = 0
    · subst s; simp only [OrbitAlgebra.outer_eq_vecMulVec, zero_vecMulVec, map_zero]
    by_cases ht : t = 0
    · subst t; simp only [OrbitAlgebra.outer_eq_vecMulVec, vecMulVec_zero, map_zero]
    have htu : t ⬝ᵥ u = 0 := by
      rw [dotProduct_comm]
      exact hut
    have hvs : v ⬝ᵥ s = 0 := by
      rw [dotProduct_comm]
      exact hsv
    exact hcl _ (rankOne_pair_mem_closure u v s t hu hv hs ht htu hvs)
  obtain ⟨L, M, hLM⟩ := OrbitAlgebra.bilinear_products_decomposition (0 : I) B hrank
  refine ⟨L, M, ?_⟩
  intro X Y
  have hm (A C : Mat) : OrbitAlgebra.matrixMul A C = (A * C : Mat) := by
    apply Matrix.ext
    intro i j
    rfl
  simpa only [hm] using hLM X Y

noncomputable def independentScalingUnit (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Matˣ where
  val := diagonal ![a, a, b⁻¹, b⁻¹, 1, 1]
  inv := diagonal ![a⁻¹, a⁻¹, b, b, 1, 1]
  val_inv := by
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha, hb]
  inv_val := by
    rw [diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha, hb]

theorem independentScalingUnit_mul_D (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (↑(independentScalingUnit a b ha hb) : Mat) * D = a • D := by
  change diagonal ![a, a, b⁻¹, b⁻¹, 1, 1] * D = a • D
  unfold D
  rw [diagonal_mul_diagonal]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem E_mul_independentScalingUnit_inv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    E * (↑((independentScalingUnit a b ha hb)⁻¹) : Mat) = b • E := by
  change E * diagonal ![a⁻¹, a⁻¹, b, b, 1, 1] = b • E
  unfold E
  rw [diagonal_mul_diagonal]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem action_independentScaling (U V : Matˣ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    action (U * independentScalingUnit a b ha hb) V (D, E) =
      (a • (action U V (D, E)).1, b • (action U V (D, E)).2) := by
  let S := independentScalingUnit a b ha hb
  apply Prod.ext
  · change ((↑U : Mat) * ↑S) * D * (↑(V⁻¹) : Mat) =
      a • ((↑U : Mat) * D * (↑(V⁻¹) : Mat))
    rw [Matrix.mul_assoc (↑U : Mat) (↑S : Mat) D, independentScalingUnit_mul_D]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  · change (↑V : Mat) * E * (↑((U * S)⁻¹) : Mat) =
      b • ((↑V : Mat) * E * (↑(U⁻¹) : Mat))
    simp only [_root_.mul_inv_rev, Units.val_mul]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (↑V : Mat) E (↑(S⁻¹) : Mat),
      E_mul_independentScalingUnit_inv]
    simp [Matrix.mul_smul, Matrix.smul_mul]

theorem independent_scaling_mem_orbit {z : Pair} (hz : z ∈ orbit)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a • z.1, b • z.2) ∈ orbit := by
  rcases hz with ⟨U, V, rfl⟩
  exact ⟨U * independentScalingUnit a b ha hb, V,
    (action_independentScaling U V a b ha hb).symm⟩

theorem bihomogeneous_components_vanish (c : ℝ) (Lx Ly : Mat →ₗ[ℝ] ℝ)
    (Qx Qy B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (h : ∀ z ∈ orbit,
      c + Lx z.1 + Ly z.2 + Qx z.1 z.1 + Qy z.2 z.2 + B z.1 z.2 = 0)
    (z : Pair) (hz : z ∈ orbit) :
    c = 0 ∧ Lx z.1 = 0 ∧ Ly z.2 = 0 ∧ Qx z.1 z.1 = 0 ∧
      Qy z.2 z.2 = 0 ∧ B z.1 z.2 = 0 := by
  have hscale (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :=
    h _ (independent_scaling_mem_orbit hz a b ha hb)
  have h1 := hscale 1 1 (by norm_num) (by norm_num)
  have h2 := hscale (-1) 1 (by norm_num) (by norm_num)
  have h3 := hscale 1 (-1) (by norm_num) (by norm_num)
  have h4 := hscale (-1) (-1) (by norm_num) (by norm_num)
  have h5 := hscale 2 1 (by norm_num) (by norm_num)
  have h6 := hscale 1 2 (by norm_num) (by norm_num)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end PBCounterexample.OrbitGeometry
