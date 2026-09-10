import PBCounterexample.SymmetricAlgebra
import PBCounterexample.OrbitNormalization
import PBCounterexample.MatrixProjection

/-! The congruence orbit of orthogonal symmetric matrices of ranks two and two. -/

namespace PBCounterexample.SymmetricGeometry

open Matrix Filter Topology
open PBCounterexample.SymmetricAlgebra

abbrev I := Fin 5
abbrev Mat := Matrix I I ℝ
abbrev Pair := Mat × Mat

def D : Mat := diagonal ![1, 1, 0, 0, 0]
def E : Mat := diagonal ![0, 0, 1, 1, 0]

def action (U : Matˣ) (z : Pair) : Pair :=
  ((U : Mat) * z.1 * (U : Mat)ᵀ,
    (↑(U⁻¹) : Mat)ᵀ * z.2 * (↑(U⁻¹) : Mat))

def orbit : Set Pair := {z | ∃ U : Matˣ, z = action U (D, E)}

theorem D_mul_E : D * E = 0 := by
  unfold D E
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem E_mul_D : E * D = 0 := by
  unfold D E
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem congruence_isSymm (U X : Mat) (hX : X.IsSymm) : (U * X * Uᵀ).IsSymm := by
  change (U * X * Uᵀ)ᵀ = U * X * Uᵀ
  simp only [transpose_mul, transpose_transpose, hX.eq, Matrix.mul_assoc]

theorem orbit_symmetric (z : Pair) (hz : z ∈ orbit) : z.1.IsSymm ∧ z.2.IsSymm := by
  rcases hz with ⟨U, rfl⟩
  constructor
  · exact congruence_isSymm _ _ (isSymm_diagonal _)
  · simpa only [action, transpose_transpose] using
      congruence_isSymm (↑(U⁻¹) : Mat)ᵀ E (isSymm_diagonal _)

theorem orbit_products_zero (z : Pair) (hz : z ∈ orbit) : z.1 * z.2 = 0 ∧ z.2 * z.1 = 0 := by
  rcases hz with ⟨U, rfl⟩
  constructor
  · change ((U : Mat) * D * (U : Mat)ᵀ) *
      ((↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat)) = 0
    calc
      _ = (U : Mat) * (D * ((U : Mat)ᵀ * (↑(U⁻¹) : Mat)ᵀ) * E) *
          (↑(U⁻¹) : Mat) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [← transpose_mul]; simp [D_mul_E]
  · change ((↑(U⁻¹) : Mat)ᵀ * E * (↑(U⁻¹) : Mat)) *
      ((U : Mat) * D * (U : Mat)ᵀ) = 0
    calc
      _ = (↑(U⁻¹) : Mat)ᵀ * (E * ((↑(U⁻¹) : Mat) * (U : Mat)) * D) *
          (U : Mat)ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by simp [E_mul_D]

@[simp] theorem action_one (z : Pair) : action 1 z = z := by
  rcases z with ⟨X, Y⟩
  simp [action]

theorem action_mul (U V : Matˣ) (z : Pair) :
    action U (action V z) = action (U * V) z := by
  simp [action, transpose_mul, Matrix.mul_assoc]

theorem action_mem_orbit (U : Matˣ) {z : Pair} (hz : z ∈ orbit) : action U z ∈ orbit := by
  rcases hz with ⟨V, rfl⟩
  exact ⟨U * V, action_mul U V (D, E)⟩

theorem continuous_action (U : Matˣ) : Continuous (action U) := by
  unfold action
  fun_prop

theorem action_mem_closure (U : Matˣ) {z : Pair} (hz : z ∈ closure orbit) :
    action U z ∈ closure orbit := by
  have h := mem_closure_image (continuous_action U).continuousAt hz
  exact closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact action_mem_orbit U hw) h

def normalizedPath (t : ℝ) : Pair :=
  (diagonal ![1, t ^ 2, 0, 0, 0], diagonal ![0, 0, 1, t ^ 2, 0])

noncomputable def scalingUnit (t : ℝ) (ht : t ≠ 0) : Matˣ where
  val := diagonal ![1, t, 1, t⁻¹, 1]
  inv := diagonal ![1, t⁻¹, 1, t, 1]
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht]

theorem normalizedPath_mem_orbit (t : ℝ) (ht : t ≠ 0) : normalizedPath t ∈ orbit := by
  refine ⟨scalingUnit t ht, ?_⟩
  apply Prod.ext
  · change diagonal ![1, t ^ 2, 0, 0, 0] =
      diagonal ![1, t, 1, t⁻¹, 1] * D * (diagonal ![1, t, 1, t⁻¹, 1])ᵀ
    simp only [D, diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pow_two]
  · change diagonal ![0, 0, 1, t ^ 2, 0] =
      (diagonal ![1, t⁻¹, 1, t, 1])ᵀ * E * diagonal ![1, t⁻¹, 1, t, 1]
    simp only [E, diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pow_two]

theorem continuous_normalizedPath : Continuous normalizedPath := by
  unfold normalizedPath
  fun_prop

theorem normalizedPath_zero_mem_closure : normalizedPath 0 ∈ closure orbit := by
  have hlim : Tendsto normalizedPath (𝓝[≠] (0 : ℝ)) (𝓝 (normalizedPath 0)) :=
    continuous_normalizedPath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact normalizedPath_mem_orbit t
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht)

theorem normalizedPath_zero : normalizedPath 0 =
    (rankOne (Pi.single (0 : I) 1), rankOne (Pi.single (2 : I) 1)) := by
  apply Prod.ext <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp +decide [normalizedPath, rankOne, Matrix.diagonal, vecMulVec, Pi.single_apply]

theorem action_rankOne (U : Matˣ) (u v : I → ℝ) :
    action U (rankOne u, rankOne v) =
      (rankOne ((U : Mat) *ᵥ u), rankOne (v ᵥ* (↑(U⁻¹) : Mat))) := by
  simp only [action, rankOne, mul_vecMulVec, vecMulVec_mul,
    vecMul_transpose, mulVec_transpose]

theorem rankOne_pair_mem_closure (u v : I → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ⬝ᵥ v = 0) :
    (rankOne u, rankOne v) ∈ closure orbit := by
  obtain ⟨U, hU, hUi⟩ := OrbitNormalization.exists_unit_with_column_and_inverse_row
    (0 : I) 2 (by decide) u v hu hv (by simpa only [dotProduct_comm] using huv)
  have h := action_mem_closure U normalizedPath_zero_mem_closure
  rw [normalizedPath_zero, action_rankOne, hU, hUi] at h
  exact h

theorem bilinear_rankOne_vanish
    (B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hB : ∀ z ∈ orbit, B z.1 z.2 = 0)
    (u v : I → ℝ) (huv : u ⬝ᵥ v = 0) : B (rankOne u) (rankOne v) = 0 := by
  by_cases hu : u = 0
  · subst u
    simp [rankOne]
  by_cases hv : v = 0
  · subst v
    simp [rankOne]
  have hcont : Continuous (fun z : Pair => B z.1 z.2) := by
    have heq : (fun z : Pair => B z.1 z.2) =
        fun z : Pair => ∑ i, ∑ j, ∑ k, ∑ l,
          B (OrbitAlgebra.unit i j) (OrbitAlgebra.unit k l) * z.1 i j * z.2 k l := by
      funext z
      exact OrbitAlgebra.bilinear_eval_expansion B z.1 z.2
    rw [heq]
    fun_prop
  have hcl : ∀ z ∈ closure orbit, B z.1 z.2 = 0 :=
    closure_minimal hB (isClosed_eq hcont continuous_const)
  exact hcl _ (rankOne_pair_mem_closure u v hu hv huv)

noncomputable def independentScalingUnit (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Matˣ where
  val := diagonal ![a, a, b⁻¹, b⁻¹, 1]
  inv := diagonal ![a⁻¹, a⁻¹, b, b, 1]
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha, hb]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha, hb]

theorem independentScaling_action (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    action (independentScalingUnit a b ha hb) (D, E) = (a ^ 2 • D, b ^ 2 • E) := by
  apply Prod.ext
  · change diagonal ![a, a, b⁻¹, b⁻¹, 1] * D *
      (diagonal ![a, a, b⁻¹, b⁻¹, 1])ᵀ = a ^ 2 • D
    simp only [D, diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pow_two]
  · change (diagonal ![a⁻¹, a⁻¹, b, b, 1])ᵀ * E *
      diagonal ![a⁻¹, a⁻¹, b, b, 1] = b ^ 2 • E
    simp only [E, diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, pow_two]

theorem action_independentScaling (U : Matˣ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    action (U * independentScalingUnit a b ha hb) (D, E) =
      (a ^ 2 • (action U (D, E)).1, b ^ 2 • (action U (D, E)).2) := by
  rw [← action_mul, independentScaling_action]
  simp only [action, Matrix.mul_smul, Matrix.smul_mul]

theorem independent_scaling_mem_orbit {z : Pair} (hz : z ∈ orbit)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a ^ 2 • z.1, b ^ 2 • z.2) ∈ orbit := by
  rcases hz with ⟨U, rfl⟩
  exact ⟨U * independentScalingUnit a b ha hb,
    (action_independentScaling U a b ha hb).symm⟩

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
  have h2 := hscale 2 1 (by norm_num) (by norm_num)
  have h3 := hscale 3 1 (by norm_num) (by norm_num)
  have h4 := hscale 1 2 (by norm_num) (by norm_num)
  have h5 := hscale 1 3 (by norm_num) (by norm_num)
  have h6 := hscale 2 2 (by norm_num) (by norm_num)
  norm_num only [map_smul, LinearMap.smul_apply, smul_eq_mul, one_pow, one_mul,
    OfNat.ofNat, Nat.cast_ofNat] at h1 h2 h3 h4 h5 h6
  constructor
  · nlinarith [h1, h2, h3, h4, h5, h6]
  constructor
  · nlinarith [h1, h2, h3, h4, h5, h6]
  constructor
  · nlinarith [h1, h2, h3, h4, h5, h6]
  constructor
  · nlinarith [h1, h2, h3, h4, h5, h6]
  constructor <;> nlinarith [h1, h2, h3, h4, h5, h6]

theorem continuous_vanish_on_all_congruences (P : Mat) (F : Mat → ℝ)
    (hF : Continuous F) (hvan : ∀ U : Matˣ, F ((U : Mat) * P * (U : Mat)ᵀ) = 0) :
    ∀ A : Mat, F (A * P * Aᵀ) = 0 := by
  intro A
  exact MatrixProjection.denseRange_units.induction_on A
    (isClosed_eq (by fun_prop) continuous_const) hvan

def firstColumns (u v : I → ℝ) : Mat := fun i j =>
  if j = 0 then u i else if j = 1 then v i else 0

def secondColumns (u v : I → ℝ) : Mat := fun i j =>
  if j = 2 then u i else if j = 3 then v i else 0

set_option maxRecDepth 10000 in
theorem firstColumns_congruence_D (u v : I → ℝ) :
    firstColumns u v * D * (firstColumns u v)ᵀ = rankOne u + rankOne v := by
  ext i j
  change (∑ k : I, (firstColumns u v * diagonal ![1, 1, 0, 0, 0] : Mat) i k *
    firstColumns u v j k) = u i * u j + v i * v j
  simp only [Matrix.mul_diagonal]
  simp +decide [firstColumns, Fin.sum_univ_succ]

set_option maxRecDepth 10000 in
theorem secondColumns_congruence_E (u v : I → ℝ) :
    secondColumns u v * E * (secondColumns u v)ᵀ = rankOne u + rankOne v := by
  ext i j
  change (∑ k : I, (secondColumns u v * diagonal ![0, 0, 1, 1, 0] : Mat) i k *
    secondColumns u v j k) = u i * u j + v i * v j
  simp only [Matrix.mul_diagonal]
  simp +decide [secondColumns, Fin.sum_univ_succ]

theorem linear_D_vanish (L : Mat →ₗ[ℝ] ℝ)
    (hL : ∀ U : Matˣ, L ((U : Mat) * D * (U : Mat)ᵀ) = 0)
    (X : Mat) (hX : X.IsSymm) : L X = 0 := by
  have hall := continuous_vanish_on_all_congruences D L
    L.continuous_of_finiteDimensional hL
  apply linear_vanish_of_rankOne L _ X hX
  intro u
  simpa [firstColumns_congruence_D, rankOne] using hall (firstColumns u 0)

theorem linear_E_vanish (L : Mat →ₗ[ℝ] ℝ)
    (hL : ∀ U : Matˣ, L ((U : Mat) * E * (U : Mat)ᵀ) = 0)
    (X : Mat) (hX : X.IsSymm) : L X = 0 := by
  have hall := continuous_vanish_on_all_congruences E L
    L.continuous_of_finiteDimensional hL
  apply linear_vanish_of_rankOne L _ X hX
  intro u
  simpa [secondColumns_congruence_E, rankOne] using hall (secondColumns u 0)

theorem quadratic_D_vanish (Q : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hsym : ∀ X Y, Q X Y = Q Y X)
    (hQ : ∀ U : Matˣ,
      Q ((U : Mat) * D * (U : Mat)ᵀ) ((U : Mat) * D * (U : Mat)ᵀ) = 0)
    (X Y : Mat) (hX : X.IsSymm) (hY : Y.IsSymm) : Q X Y = 0 := by
  have hall := continuous_vanish_on_all_congruences D (fun X => Q X X)
    (MatrixProjection.continuous_quadratic Q) hQ
  exact quadratic_vanish_of_rankTwo Q hsym
    (fun u v => by simpa only [firstColumns_congruence_D] using hall (firstColumns u v))
    X Y hX hY

theorem quadratic_E_vanish (Q : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hsym : ∀ X Y, Q X Y = Q Y X)
    (hQ : ∀ U : Matˣ,
      Q ((U : Mat) * E * (U : Mat)ᵀ) ((U : Mat) * E * (U : Mat)ᵀ) = 0)
    (X Y : Mat) (hX : X.IsSymm) (hY : Y.IsSymm) : Q X Y = 0 := by
  have hall := continuous_vanish_on_all_congruences E (fun X => Q X X)
    (MatrixProjection.continuous_quadratic Q) hQ
  exact quadratic_vanish_of_rankTwo Q hsym
    (fun u v => by simpa only [secondColumns_congruence_E] using hall (secondColumns u v))
    X Y hX hY

noncomputable def transposeUnit (U : Matˣ) : Matˣ where
  val := (U : Mat)ᵀ
  inv := (↑(U⁻¹) : Mat)ᵀ
  val_inv := by rw [← transpose_mul]; simp
  inv_val := by rw [← transpose_mul]; simp

theorem inverseTranspose_action_snd (U : Matˣ) :
    (action ((transposeUnit U)⁻¹) (D, E)).2 = (U : Mat) * E * (U : Mat)ᵀ := by
  simp only [action, inv_inv]
  change ((U : Mat)ᵀ)ᵀ * E * (U : Mat)ᵀ = (U : Mat) * E * (U : Mat)ᵀ
  rw [transpose_transpose]

theorem bilinear_orbit_classification
    (B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hB : ∀ z ∈ orbit, B z.1 z.2 = 0) :
    ∃ L : Mat →ₗ[ℝ] ℝ, ∀ X Y : Mat,
      X.IsSymm → Y.IsSymm → B X Y = L (X * Y) :=
  bilinear_product_classification B (fun u v huv => bilinear_rankOne_vanish B hB u v huv)

/-- A polynomial expression of degree at most two vanishing on the orbit,
written in its constant, linear, pure quadratic, and bilinear components,
restricts to a linear functional of the product on symmetric matrix pairs. -/
theorem decomposed_orbit_classification (c : ℝ) (Lx Ly : Mat →ₗ[ℝ] ℝ)
    (Qx Qy B : Mat →ₗ[ℝ] Mat →ₗ[ℝ] ℝ)
    (hsx : ∀ X Y, Qx X Y = Qx Y X) (hsy : ∀ X Y, Qy X Y = Qy Y X)
    (h : ∀ z ∈ orbit,
      c + Lx z.1 + Ly z.2 + Qx z.1 z.1 + Qy z.2 z.2 + B z.1 z.2 = 0) :
    ∃ L : Mat →ₗ[ℝ] ℝ, ∀ X Y : Mat, X.IsSymm → Y.IsSymm →
      c + Lx X + Ly Y + Qx X X + Qy Y Y + B X Y = L (X * Y) := by
  have hcomponents (z : Pair) (hz : z ∈ orbit) :=
    bihomogeneous_components_vanish c Lx Ly Qx Qy B h z hz
  have hbase : (D, E) ∈ orbit := ⟨1, (action_one (D, E)).symm⟩
  have hc : c = 0 := (hcomponents (D, E) hbase).1
  have hLx (X : Mat) (hX : X.IsSymm) : Lx X = 0 := by
    apply linear_D_vanish Lx _ X hX
    intro U
    exact (hcomponents (action U (D, E)) ⟨U, rfl⟩).2.1
  have hLy (Y : Mat) (hY : Y.IsSymm) : Ly Y = 0 := by
    apply linear_E_vanish Ly _ Y hY
    intro U
    have hU := (hcomponents (action ((transposeUnit U)⁻¹) (D, E))
      ⟨(transposeUnit U)⁻¹, rfl⟩).2.2.1
    simpa only [inverseTranspose_action_snd] using hU
  have hQx (X : Mat) (hX : X.IsSymm) : Qx X X = 0 := by
    apply quadratic_D_vanish Qx hsx _ X X hX hX
    intro U
    exact (hcomponents (action U (D, E)) ⟨U, rfl⟩).2.2.2.1
  have hQy (Y : Mat) (hY : Y.IsSymm) : Qy Y Y = 0 := by
    apply quadratic_E_vanish Qy hsy _ Y Y hY hY
    intro U
    have hU := (hcomponents (action ((transposeUnit U)⁻¹) (D, E))
      ⟨(transposeUnit U)⁻¹, rfl⟩).2.2.2.2.1
    simpa only [inverseTranspose_action_snd] using hU
  obtain ⟨L, hL⟩ := bilinear_orbit_classification B
    (fun z hz => (hcomponents z hz).2.2.2.2.2)
  refine ⟨L, ?_⟩
  intro X Y hX hY
  simpa only [hc, hLx X hX, hLy Y hY, hQx X hX, hQy Y hY, zero_add] using
    hL X Y hX hY

def pathBase (η t : ℝ) : Pair :=
  (diagonal ![1, 1, t ^ 2, t ^ 2, η * t],
    diagonal ![t ^ 2, t ^ 2, 1, 1, η * t])

def path (U : Matˣ) (η t : ℝ) : Pair := action U (pathBase η t)

theorem path_zero (U : Matˣ) (η : ℝ) : path U η 0 = action U (D, E) := by
  simp [path, pathBase, D, E]

theorem continuous_path (U : Matˣ) (η : ℝ) : Continuous (path U η) := by
  unfold path pathBase
  apply (continuous_action U).comp
  fun_prop

theorem path_symmetric (U : Matˣ) (η t : ℝ) :
    (path U η t).1.IsSymm ∧ (path U η t).2.IsSymm := by
  constructor
  · exact congruence_isSymm _ _ (isSymm_diagonal _)
  · simpa only [path, pathBase, action, transpose_transpose] using
      congruence_isSymm (↑(U⁻¹) : Mat)ᵀ
        (diagonal ![t ^ 2, t ^ 2, 1, 1, η * t]) (isSymm_diagonal _)

theorem pathBase_products (η t : ℝ) (hη : η ^ 2 = 1) :
    (pathBase η t).1 * (pathBase η t).2 = t ^ 2 • (1 : Mat) ∧
      (pathBase η t).2 * (pathBase η t).1 = t ^ 2 • (1 : Mat) := by
  have hηt : η * t * (η * t) = t ^ 2 := by
    calc
      _ = η ^ 2 * t ^ 2 := by ring
      _ = t ^ 2 := by rw [hη, one_mul]
  constructor <;> change diagonal _ * diagonal _ = _ <;>
    rw [diagonal_mul_diagonal] <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [pathBase, Matrix.diagonal, hηt]

theorem action_first_product (U : Matˣ) (z : Pair) :
    (action U z).1 * (action U z).2 = (U : Mat) * (z.1 * z.2) * (↑(U⁻¹) : Mat) := by
  change ((U : Mat) * z.1 * (U : Mat)ᵀ) *
    ((↑(U⁻¹) : Mat)ᵀ * z.2 * (↑(U⁻¹) : Mat)) = _
  calc
    _ = (U : Mat) * (z.1 * ((U : Mat)ᵀ * (↑(U⁻¹) : Mat)ᵀ) * z.2) *
        (↑(U⁻¹) : Mat) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← transpose_mul]; simp

theorem action_second_product (U : Matˣ) (z : Pair) :
    (action U z).2 * (action U z).1 =
      (↑(U⁻¹) : Mat)ᵀ * (z.2 * z.1) * (U : Mat)ᵀ := by
  change ((↑(U⁻¹) : Mat)ᵀ * z.2 * (↑(U⁻¹) : Mat)) *
    ((U : Mat) * z.1 * (U : Mat)ᵀ) = _
  calc
    _ = (↑(U⁻¹) : Mat)ᵀ * (z.2 * ((↑(U⁻¹) : Mat) * (U : Mat)) * z.1) *
        (U : Mat)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by simp

theorem path_products (U : Matˣ) (η t : ℝ) (hη : η ^ 2 = 1) :
    (path U η t).1 * (path U η t).2 = t ^ 2 • (1 : Mat) ∧
      (path U η t).2 * (path U η t).1 = t ^ 2 • (1 : Mat) := by
  obtain ⟨hxy, hyx⟩ := pathBase_products η t hη
  constructor
  · rw [path, action_first_product, hxy]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  · rw [path, action_second_product, hyx]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [← transpose_mul]
    simp

theorem pathBase_first_det (η t : ℝ) : (pathBase η t).1.det = η * t ^ 5 := by
  change (diagonal ![1, 1, t ^ 2, t ^ 2, η * t] : Mat).det = _
  rw [det_diagonal]
  norm_num [Fin.prod_univ_succ]
  ring

theorem path_first_det (U : Matˣ) (η t : ℝ) :
    (path U η t).1.det = (U : Mat).det ^ 2 * η * t ^ 5 := by
  change ((U : Mat) * (pathBase η t).1 * (U : Mat)ᵀ).det = _
  rw [det_mul, det_mul, det_transpose, pathBase_first_det]
  ring

theorem unit_det_ne_zero (U : Matˣ) : (U : Mat).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp U.isUnit)

theorem path_first_det_pos (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    0 < (path U 1 t).1.det := by
  rw [path_first_det]
  exact mul_pos (mul_pos (sq_pos_of_ne_zero (unit_det_ne_zero U)) zero_lt_one) (pow_pos ht _)

theorem path_first_det_neg (U : Matˣ) (t : ℝ) (ht : 0 < t) :
    (path U (-1) t).1.det < 0 := by
  rw [path_first_det]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (unit_det_ne_zero U)) (by norm_num)) (pow_pos ht _)

end PBCounterexample.SymmetricGeometry
