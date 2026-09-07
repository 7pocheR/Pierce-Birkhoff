import PBCounterexample.OrbitAlgebra

/-! Linear and quadratic forms restricted to real symmetric matrices. -/

namespace PBCounterexample.SymmetricAlgebra

open Matrix
open PBCounterexample.OrbitAlgebra

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

variable {n : Type*} [Fintype n] [DecidableEq n]

def rankOne (u : n → ℝ) : Matrix n n ℝ := vecMulVec u u

def symmUnit (i j : n) : Matrix n n ℝ := unit i j + unit j i

theorem rankOne_isSymm (u : n → ℝ) : (rankOne u).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact mul_comm _ _

theorem symmUnit_comm (i j : n) : symmUnit i j = symmUnit j i := add_comm _ _

theorem symmUnit_isSymm (i j : n) : (symmUnit i j).IsSymm := by
  apply Matrix.IsSymm.ext
  intro r c
  simp only [symmUnit, unit, Matrix.add_apply]
  split_ifs <;> simp_all

theorem rankOne_vectorUnit (i : n) : rankOne (vectorUnit i) = unit i i :=
  outer_vectorUnit i i

theorem unit_diag_isSymm (i : n) : (unit i i : Matrix n n ℝ).IsSymm := by
  rw [← rankOne_vectorUnit]
  exact rankOne_isSymm _

theorem rankOne_add (u v : n → ℝ) :
    rankOne (u + v) = rankOne u + (vecMulVec u v + vecMulVec v u) + rankOne v := by
  ext i j
  simp only [rankOne, vecMulVec_apply, Pi.add_apply, Matrix.add_apply]
  ring

theorem symmUnit_eq_rankOne (i j : n) :
    symmUnit i j = rankOne (vectorUnit i + vectorUnit j) -
      rankOne (vectorUnit i) - rankOne (vectorUnit j) := by
  rw [rankOne_add]
  rw [← outer_eq_vecMulVec, ← outer_eq_vecMulVec, outer_vectorUnit, outer_vectorUnit]
  unfold symmUnit
  abel

theorem symmetric_expansion (X : Matrix n n ℝ) (hX : X.IsSymm) :
    X = (1 / 2 : ℝ) • ∑ i, ∑ j, X i j • symmUnit i j := by
  ext r c
  simp only [symmUnit, smul_add, Finset.sum_add_distrib]
  simp [unit, Matrix.sum_apply, hX.apply r c]
  ring

theorem linear_vanish_of_rankOne (L : Matrix n n ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ u : n → ℝ, L (rankOne u) = 0)
    (X : Matrix n n ℝ) (hX : X.IsSymm) : L X = 0 := by
  have hb (i j : n) : L (symmUnit i j) = 0 := by
    rw [symmUnit_eq_rankOne]
    simp only [map_sub, hL, sub_zero]
  rw [symmetric_expansion X hX]
  simp [hb]

theorem bilinear_vanish_of_rankOne
    (B : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] ℝ)
    (hB : ∀ u v : n → ℝ, B (rankOne u) (rankOne v) = 0)
    (X Y : Matrix n n ℝ) (hX : X.IsSymm) (hY : Y.IsSymm) : B X Y = 0 := by
  apply linear_vanish_of_rankOne (B X) _ Y hY
  intro v
  exact linear_vanish_of_rankOne (B.flip (rankOne v)) (fun u => hB u v) X hX

theorem bilinear_eq_of_rankOne
    (B C : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] ℝ)
    (hBC : ∀ u v : n → ℝ, B (rankOne u) (rankOne v) = C (rankOne u) (rankOne v))
    (X Y : Matrix n n ℝ) (hX : X.IsSymm) (hY : Y.IsSymm) : B X Y = C X Y := by
  have h := bilinear_vanish_of_rankOne (B - C)
    (fun u v => by simp only [LinearMap.sub_apply, hBC, sub_self]) X Y hX hY
  exact sub_eq_zero.mp h

theorem quadratic_vanish_of_rankTwo
    (Q : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] ℝ)
    (hsym : ∀ X Y, Q X Y = Q Y X)
    (hQ : ∀ u v : n → ℝ,
      Q (rankOne u + rankOne v) (rankOne u + rankOne v) = 0)
    (X Y : Matrix n n ℝ) (hX : X.IsSymm) (hY : Y.IsSymm) : Q X Y = 0 := by
  have hrank (u : n → ℝ) : Q (rankOne u) (rankOne u) = 0 := by
    simpa [rankOne] using hQ u 0
  apply bilinear_vanish_of_rankOne Q _ X Y hX hY
  intro u v
  have h := hQ u v
  simp only [map_add, LinearMap.add_apply, hrank] at h
  rw [hsym (rankOne v) (rankOne u)] at h
  linarith

theorem rankOne_mul_rankOne (u v : n → ℝ) :
    rankOne u * rankOne v = (u ⬝ᵥ v) • vecMulVec u v := by
  simp only [rankOne, vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

theorem rankOne_product_zero (u v : n → ℝ) (huv : u ⬝ᵥ v = 0) :
    rankOne u * rankOne v = 0 := by
  rw [rankOne_mul_rankOne, huv, zero_smul]

def upperIndex : Fin 15 → Fin 5 × Fin 5 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
    (1, 1), (1, 2), (1, 3), (1, 4), (2, 2),
    (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)]

def upperBasis : Fin 15 → Matrix (Fin 5) (Fin 5) ℝ :=
  ![unit 0 0, symmUnit 0 1, symmUnit 0 2, symmUnit 0 3, symmUnit 0 4,
    unit 1 1, symmUnit 1 2, symmUnit 1 3, symmUnit 1 4, unit 2 2,
    symmUnit 2 3, symmUnit 2 4, unit 3 3, symmUnit 3 4, unit 4 4]

def upperCoordinate (X : Matrix (Fin 5) (Fin 5) ℝ) (a : Fin 15) : ℝ :=
  X (upperIndex a).1 (upperIndex a).2

theorem upper_expansion (X : Matrix (Fin 5) (Fin 5) ℝ) (hX : X.IsSymm) :
    X = ∑ a : Fin 15, upperCoordinate X a • upperBasis a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperCoordinate, upperBasis, upperIndex, unit, symmUnit,
      Fin.sum_univ_succ, Matrix.sum_apply, Matrix.smul_apply, Fin.ext_iff]
  all_goals first | rfl | exact hX.apply _ _

theorem upperBasis_isSymm (a : Fin 15) : (upperBasis a).IsSymm := by
  fin_cases a <;> first
  | exact symmUnit_isSymm _ _
  | exact unit_diag_isSymm _

theorem linear_upper_expansion (L : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin 5) (Fin 5) ℝ) (hX : X.IsSymm) :
    L X = ∑ a : Fin 15, upperCoordinate X a * L (upperBasis a) := by
  conv_lhs => rw [upper_expansion X hX]
  simp

theorem bilinear_upper_expansion
    (B : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ)
    (X Y : Matrix (Fin 5) (Fin 5) ℝ) (hX : X.IsSymm) (hY : Y.IsSymm) :
    B X Y = ∑ a : Fin 15, ∑ b : Fin 15,
      upperCoordinate X a * upperCoordinate Y b * B (upperBasis a) (upperBasis b) := by
  calc
    B X Y = ∑ a : Fin 15, upperCoordinate X a * B (upperBasis a) Y :=
      linear_upper_expansion (B.flip Y) X hX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [linear_upper_expansion (B (upperBasis a)) Y hY, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

def rankOneCoordinate (u : Fin 5 → ℝ) (a : Fin 15) : ℝ :=
  u (upperIndex a).1 * u (upperIndex a).2

def diagonalIndex : Fin 5 → Fin 15 := ![0, 5, 9, 12, 14]

def pairIndex : Fin 5 → Fin 5 → Fin 15 :=
  ![![0, 1, 2, 3, 4], ![1, 5, 6, 7, 8], ![2, 6, 9, 10, 11],
    ![3, 7, 10, 12, 13], ![4, 8, 11, 13, 14]]

def coefficientMatrix (T : Fin 15 → Fin 15 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => T (diagonalIndex i) (pairIndex i j)

def productCoefficient (C : Matrix (Fin 5) (Fin 5) ℝ) (a b : Fin 15) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, C i j * (upperBasis a * upperBasis b) i j

set_option maxHeartbeats 0 in
/-- The coefficients of a bilinear form annihilating orthogonal rank-one squares
are the coefficients of one linear functional of the matrix product. -/
theorem orthogonal_rankOne_coefficient_classification
    (T : Fin 15 → Fin 15 → ℝ)
    (h : ∀ u v : Fin 5 → ℝ, u ⬝ᵥ v = 0 →
      (∑ a : Fin 15, ∑ b : Fin 15,
        rankOneCoordinate u a * rankOneCoordinate v b * T a b) = 0) :
    ∀ a b : Fin 15, T a b = productCoefficient (coefficientMatrix T) a b := by
  have h0 := h ![1, 0, 0, 0, 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h0
  have h1 := h ![1, 0, 0, 0, 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h1
  have h2 := h ![1, 0, 0, 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h2
  have h3 := h ![1, 0, 0, 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h3
  have h4 := h ![1, 0, 0, 0, 0] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h4
  have h5 := h ![1, 0, 0, 0, 0] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h5
  have h6 := h ![1, 0, 0, 0, 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h6
  have h7 := h ![1, 0, 0, 0, 0] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h7
  have h8 := h ![1, 0, 0, 0, 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h8
  have h9 := h ![1, 0, 0, 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h9
  have h10 := h ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h10
  have h11 := h ![0, 1, 0, 0, 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h11
  have h12 := h ![0, 1, 0, 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h12
  have h13 := h ![0, 1, 0, 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h13
  have h14 := h ![0, 1, 0, 0, 0] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h14
  have h15 := h ![0, 1, 0, 0, 0] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h15
  have h16 := h ![0, 1, 0, 0, 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h16
  have h17 := h ![0, 1, 0, 0, 0] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h17
  have h18 := h ![0, 1, 0, 0, 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h18
  have h19 := h ![0, 1, 0, 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h19
  have h20 := h ![0, 0, 1, 0, 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h20
  have h21 := h ![0, 0, 1, 0, 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h21
  have h22 := h ![0, 0, 1, 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h22
  have h23 := h ![0, 0, 1, 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h23
  have h24 := h ![0, 0, 1, 0, 0] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h24
  have h25 := h ![0, 0, 1, 0, 0] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h25
  have h26 := h ![0, 0, 1, 0, 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h26
  have h27 := h ![0, 0, 1, 0, 0] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h27
  have h28 := h ![0, 0, 1, 0, 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h28
  have h29 := h ![0, 0, 1, 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h29
  have h30 := h ![0, 0, 0, 1, 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h30
  have h31 := h ![0, 0, 0, 1, 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h31
  have h32 := h ![0, 0, 0, 1, 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h32
  have h33 := h ![0, 0, 0, 1, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h33
  have h34 := h ![0, 0, 0, 1, 0] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h34
  have h35 := h ![0, 0, 0, 1, 0] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h35
  have h36 := h ![0, 0, 0, 1, 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h36
  have h37 := h ![0, 0, 0, 1, 0] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h37
  have h38 := h ![0, 0, 0, 1, 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h38
  have h39 := h ![0, 0, 0, 1, 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h39
  have h40 := h ![0, 0, 0, 0, 1] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h40
  have h41 := h ![0, 0, 0, 0, 1] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h41
  have h42 := h ![0, 0, 0, 0, 1] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h42
  have h43 := h ![0, 0, 0, 0, 1] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h43
  have h44 := h ![0, 0, 0, 0, 1] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h44
  have h45 := h ![0, 0, 0, 0, 1] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h45
  have h46 := h ![0, 0, 0, 0, 1] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h46
  have h47 := h ![0, 0, 0, 0, 1] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h47
  have h48 := h ![0, 0, 0, 0, 1] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h48
  have h49 := h ![0, 0, 0, 0, 1] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h49
  have h50 := h ![1, (-1), 0, 0, 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h50
  have h51 := h ![1, (-1), 0, 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h51
  have h52 := h ![1, (-1), 0, 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h52
  have h53 := h ![1, (-1), 0, 0, 0] ![1, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h53
  have h54 := h ![1, (-1), 0, 0, 0] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h54
  have h55 := h ![1, (-1), 0, 0, 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h55
  have h56 := h ![1, (-1), 0, 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h56
  have h57 := h ![1, (-1), 0, 0, 0] ![1, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h57
  have h58 := h ![1, (-1), 0, 0, 0] ![1, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h58
  have h59 := h ![1, (-1), 0, 0, 0] ![1, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h59
  have h60 := h ![1, 1, 0, 0, 0] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h60
  have h61 := h ![1, 1, 0, 0, 0] ![1, (-1), (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h61
  have h62 := h ![1, 1, 0, 0, 0] ![1, (-1), 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h62
  have h63 := h ![1, 1, 0, 0, 0] ![1, (-1), 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h63
  have h64 := h ![1, 0, (-1), 0, 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h64
  have h65 := h ![1, 0, (-1), 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h65
  have h66 := h ![1, 0, (-1), 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h66
  have h67 := h ![1, 0, (-1), 0, 0] ![1, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h67
  have h68 := h ![1, 0, (-1), 0, 0] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h68
  have h69 := h ![1, 0, (-1), 0, 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h69
  have h70 := h ![1, 0, (-1), 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h70
  have h71 := h ![1, 0, (-1), 0, 0] ![1, (-1), 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h71
  have h72 := h ![1, 0, (-1), 0, 0] ![1, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h72
  have h73 := h ![1, 0, (-1), 0, 0] ![1, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h73
  have h74 := h ![1, 0, 1, 0, 0] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h74
  have h75 := h ![1, 0, 1, 0, 0] ![1, (-1), (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h75
  have h76 := h ![1, 0, 1, 0, 0] ![1, 0, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h76
  have h77 := h ![1, 0, 1, 0, 0] ![1, 0, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h77
  have h78 := h ![1, 0, 0, (-1), 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h78
  have h79 := h ![1, 0, 0, (-1), 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h79
  have h80 := h ![1, 0, 0, (-1), 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h80
  have h81 := h ![1, 0, 0, (-1), 0] ![1, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h81
  have h82 := h ![1, 0, 0, (-1), 0] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h82
  have h83 := h ![1, 0, 0, (-1), 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h83
  have h84 := h ![1, 0, 0, (-1), 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h84
  have h85 := h ![1, 0, 0, (-1), 0] ![1, (-1), 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h85
  have h86 := h ![1, 0, 0, (-1), 0] ![1, 0, (-1), 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h86
  have h87 := h ![1, 0, 0, (-1), 0] ![1, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h87
  have h88 := h ![1, 0, 0, 1, 0] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h88
  have h89 := h ![1, 0, 0, 1, 0] ![1, (-1), 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h89
  have h90 := h ![1, 0, 0, 1, 0] ![1, 0, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h90
  have h91 := h ![1, 0, 0, 1, 0] ![1, 0, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h91
  have h92 := h ![1, 0, 0, 0, (-1)] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h92
  have h93 := h ![1, 0, 0, 0, (-1)] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h93
  have h94 := h ![1, 0, 0, 0, (-1)] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h94
  have h95 := h ![1, 0, 0, 0, (-1)] ![1, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h95
  have h96 := h ![1, 0, 0, 0, (-1)] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h96
  have h97 := h ![1, 0, 0, 0, (-1)] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h97
  have h98 := h ![1, 0, 0, 0, (-1)] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h98
  have h99 := h ![1, 0, 0, 0, (-1)] ![1, (-1), 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h99
  have h100 := h ![1, 0, 0, 0, (-1)] ![1, 0, (-1), 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h100
  have h101 := h ![1, 0, 0, 0, (-1)] ![1, 0, 0, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h101
  have h102 := h ![1, 0, 0, 0, 1] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h102
  have h103 := h ![1, 0, 0, 0, 1] ![1, (-1), 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h103
  have h104 := h ![1, 0, 0, 0, 1] ![1, 0, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h104
  have h105 := h ![1, 0, 0, 0, 1] ![1, 0, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h105
  have h106 := h ![0, 1, (-1), 0, 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h106
  have h107 := h ![0, 1, (-1), 0, 0] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h107
  have h108 := h ![0, 1, (-1), 0, 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h108
  have h109 := h ![0, 1, (-1), 0, 0] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h109
  have h110 := h ![0, 1, (-1), 0, 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h110
  have h111 := h ![0, 1, (-1), 0, 0] ![0, 1, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h111
  have h112 := h ![0, 1, (-1), 0, 0] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h112
  have h113 := h ![0, 1, (-1), 0, 0] ![1, (-1), (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h113
  have h114 := h ![0, 1, (-1), 0, 0] ![0, 1, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h114
  have h115 := h ![0, 1, (-1), 0, 0] ![0, 1, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h115
  have h116 := h ![0, 1, 1, 0, 0] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h116
  have h117 := h ![0, 1, 1, 0, 0] ![1, (-1), 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h117
  have h118 := h ![0, 1, 1, 0, 0] ![0, 1, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h118
  have h119 := h ![0, 1, 1, 0, 0] ![0, 1, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h119
  have h120 := h ![0, 1, 0, (-1), 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h120
  have h121 := h ![0, 1, 0, (-1), 0] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h121
  have h122 := h ![0, 1, 0, (-1), 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h122
  have h123 := h ![0, 1, 0, (-1), 0] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h123
  have h124 := h ![0, 1, 0, (-1), 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h124
  have h125 := h ![0, 1, 0, (-1), 0] ![0, 1, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h125
  have h126 := h ![0, 1, 0, (-1), 0] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h126
  have h127 := h ![0, 1, 0, (-1), 0] ![1, (-1), 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h127
  have h128 := h ![0, 1, 0, (-1), 0] ![0, 1, (-1), 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h128
  have h129 := h ![0, 1, 0, (-1), 0] ![0, 1, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h129
  have h130 := h ![0, 1, 0, 1, 0] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h130
  have h131 := h ![0, 1, 0, 1, 0] ![1, (-1), 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h131
  have h132 := h ![0, 1, 0, 1, 0] ![0, 1, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h132
  have h133 := h ![0, 1, 0, 1, 0] ![0, 1, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h133
  have h134 := h ![0, 1, 0, 0, (-1)] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h134
  have h135 := h ![0, 1, 0, 0, (-1)] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h135
  have h136 := h ![0, 1, 0, 0, (-1)] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h136
  have h137 := h ![0, 1, 0, 0, (-1)] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h137
  have h138 := h ![0, 1, 0, 0, (-1)] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h138
  have h139 := h ![0, 1, 0, 0, (-1)] ![0, 1, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h139
  have h140 := h ![0, 1, 0, 0, (-1)] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h140
  have h141 := h ![0, 1, 0, 0, (-1)] ![1, (-1), 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h141
  have h142 := h ![0, 1, 0, 0, (-1)] ![0, 1, (-1), 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h142
  have h143 := h ![0, 1, 0, 0, (-1)] ![0, 1, 0, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h143
  have h144 := h ![0, 1, 0, 0, 1] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h144
  have h145 := h ![0, 1, 0, 0, 1] ![1, (-1), 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h145
  have h146 := h ![0, 1, 0, 0, 1] ![0, 1, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h146
  have h147 := h ![0, 1, 0, 0, 1] ![0, 1, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h147
  have h148 := h ![0, 0, 1, (-1), 0] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h148
  have h149 := h ![0, 0, 1, (-1), 0] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h149
  have h150 := h ![0, 0, 1, (-1), 0] ![0, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h150
  have h151 := h ![0, 0, 1, (-1), 0] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h151
  have h152 := h ![0, 0, 1, (-1), 0] ![1, 0, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h152
  have h153 := h ![0, 0, 1, (-1), 0] ![0, 1, 0, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h153
  have h154 := h ![0, 0, 1, (-1), 0] ![0, 0, 1, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h154
  have h155 := h ![0, 0, 1, (-1), 0] ![1, 0, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h155
  have h156 := h ![0, 0, 1, (-1), 0] ![0, 1, (-1), (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h156
  have h157 := h ![0, 0, 1, (-1), 0] ![0, 0, 1, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h157
  have h158 := h ![0, 0, 1, 1, 0] ![0, 0, 1, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h158
  have h159 := h ![0, 0, 1, 1, 0] ![1, 0, (-1), 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h159
  have h160 := h ![0, 0, 1, 1, 0] ![0, 1, (-1), 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h160
  have h161 := h ![0, 0, 1, 1, 0] ![0, 0, 1, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h161
  have h162 := h ![0, 0, 1, 0, (-1)] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h162
  have h163 := h ![0, 0, 1, 0, (-1)] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h163
  have h164 := h ![0, 0, 1, 0, (-1)] ![0, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h164
  have h165 := h ![0, 0, 1, 0, (-1)] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h165
  have h166 := h ![0, 0, 1, 0, (-1)] ![1, 0, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h166
  have h167 := h ![0, 0, 1, 0, (-1)] ![0, 1, 0, (-1), 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h167
  have h168 := h ![0, 0, 1, 0, (-1)] ![0, 0, 1, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h168
  have h169 := h ![0, 0, 1, 0, (-1)] ![1, 0, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h169
  have h170 := h ![0, 0, 1, 0, (-1)] ![0, 1, (-1), 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h170
  have h171 := h ![0, 0, 1, 0, (-1)] ![0, 0, 1, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h171
  have h172 := h ![0, 0, 1, 0, 1] ![0, 0, 1, 0, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h172
  have h173 := h ![0, 0, 1, 0, 1] ![1, 0, (-1), 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h173
  have h174 := h ![0, 0, 1, 0, 1] ![0, 1, (-1), 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h174
  have h175 := h ![0, 0, 1, 0, 1] ![0, 0, 1, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h175
  have h176 := h ![0, 0, 0, 1, (-1)] ![1, 0, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h176
  have h177 := h ![0, 0, 0, 1, (-1)] ![0, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h177
  have h178 := h ![0, 0, 0, 1, (-1)] ![0, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h178
  have h179 := h ![0, 0, 0, 1, (-1)] ![1, (-1), 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h179
  have h180 := h ![0, 0, 0, 1, (-1)] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h180
  have h181 := h ![0, 0, 0, 1, (-1)] ![0, 1, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h181
  have h182 := h ![0, 0, 0, 1, (-1)] ![0, 0, 0, 1, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h182
  have h183 := h ![0, 0, 0, 1, (-1)] ![1, 0, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h183
  have h184 := h ![0, 0, 0, 1, (-1)] ![0, 1, 0, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h184
  have h185 := h ![0, 0, 0, 1, (-1)] ![0, 0, 1, (-1), (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h185
  have h186 := h ![0, 0, 0, 1, 1] ![0, 0, 0, 1, (-1)] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h186
  have h187 := h ![0, 0, 0, 1, 1] ![1, 0, 0, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h187
  have h188 := h ![0, 0, 0, 1, 1] ![0, 1, 0, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h188
  have h189 := h ![0, 0, 0, 1, 1] ![0, 0, 1, (-1), 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h189
  have h190 := h ![1, (-1), (-1), 0, 0] ![1, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h190
  have h191 := h ![1, (-1), (-1), 0, 0] ![1, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h191
  have h192 := h ![1, (-1), 1, 0, 0] ![1, 0, (-1), 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h192
  have h193 := h ![1, (-1), 0, (-1), 0] ![1, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h193
  have h194 := h ![1, (-1), 0, (-1), 0] ![1, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h194
  have h195 := h ![1, (-1), 0, 0, (-1)] ![1, 1, 0, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h195
  have h196 := h ![1, (-1), 0, 0, (-1)] ![1, 0, 0, 0, 1] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h196
  have h197 := h ![1, 0, (-1), (-1), 0] ![1, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h197
  have h198 := h ![1, 0, (-1), 0, (-1)] ![1, 0, 1, 0, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h198
  have h199 := h ![1, 0, 0, (-1), (-1)] ![1, 0, 0, 1, 0] (by
    norm_num [dotProduct, Fin.sum_univ_succ])
  norm_num [rankOneCoordinate, upperIndex, Fin.sum_univ_succ] at h199
  intro a b
  fin_cases a <;> fin_cases b
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h1 - h4
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h2 - h5
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h3 - h6
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h2 - h7
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h3 - h8
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h3 - h9
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h3
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h1 + h21 - h24 + h50 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h10 + (-1 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h60
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + 2 * h1 - h4 + h11 - h50 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h57 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h61
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + 2 * h2 - h5 + h12 - h51 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h58 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h62
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + 2 * h3 - h6 + h13 - h52 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h63
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 - h21 + h24 - h50 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h1 + h10 - h14 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h57 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h61
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h2 + h10 - h15 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h58 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h62
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h3 + h10 - h16 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h63
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h11 - h50
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h2 - h7 + h11 + h12 - h17 - h50 - h51 + h54
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h3 - h8 + h11 + h13 - h18 - h50 - h52 + h55
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h12 - h51
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h3 - h9 + h12 + h13 - h19 - h51 - h52 + h56
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h3 + h13 - h52
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 - 3 * h1 + 2 * h4 + 5 * h10 + h11 - 2 * h14 + 5 * h20 - h24 + h50 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h57 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h61 + 2 * h64 + h67 + (-1 / 2 : ℝ) * h71 - h74 + (1 / 2 : ℝ) * h75 - 3 * h106 - h111 + (1 / 2 : ℝ) * h113 + h116 + (-1 / 2 : ℝ) * h117 - h190 + (-1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h0 + h1 - h4 + h21 - h64 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h71 + (1 / 2 : ℝ) * h74 + (-1 / 2 : ℝ) * h75
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h20 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + 2 * h2 - h7 + h22 - h65 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h72 + (1 / 2 : ℝ) * h74 + (-1 / 2 : ℝ) * h76
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + 2 * h3 - h8 + h23 - h66 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h73 + (1 / 2 : ℝ) * h74 + (-1 / 2 : ℝ) * h77
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h21 - h64
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 + h20 - h24 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h71 + (-1 / 2 : ℝ) * h74 + (1 / 2 : ℝ) * h75
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h2 - h5 + h21 + h22 - h27 - h64 - h65 + h68
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h3 - h6 + h21 + h23 - h28 - h64 - h66 + h69
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 + 3 * h1 - 2 * h4 - 5 * h10 - h11 + 2 * h14 - 5 * h20 + h24 - h50 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h57 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h61 - 2 * h64 + (-3 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h71 + (3 / 2 : ℝ) * h74 + (-1 / 2 : ℝ) * h75 + 3 * h106 + h111 + (-1 / 2 : ℝ) * h113 - h116 + (1 / 2 : ℝ) * h117 + h190 + (1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h2 + h20 - h25 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h72 + (-1 / 2 : ℝ) * h74 + (1 / 2 : ℝ) * h76
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h3 + h20 - h26 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h73 + (-1 / 2 : ℝ) * h74 + (1 / 2 : ℝ) * h77
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h22 - h65
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h3 - h9 + h22 + h23 - h29 - h65 - h66 + h70
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h3 + h23 - h66
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 + h1 - 4 * h2 + 2 * h5 + 5 * h10 + h12 - 2 * h15 - h21 + h24 + 5 * h30 + h31 - 2 * h34 - h50 + 2 * h51 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h58 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h62 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + 2 * h78 + (3 / 2 : ℝ) * h81 + (-1 / 2 : ℝ) * h85 + (-1 / 2 : ℝ) * h88 + (1 / 2 : ℝ) * h89 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - 3 * h120 + (-3 / 2 : ℝ) * h125 + h127 + (1 / 2 : ℝ) * h130 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h193 - h194
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h0 + h2 - h5 + h31 - h78 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h85 + (1 / 2 : ℝ) * h88 + (-1 / 2 : ℝ) * h89
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h1 + h2 - h7 + h32 - h79 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h86 + (1 / 2 : ℝ) * h88 + (-1 / 2 : ℝ) * h90
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h30 + (-1 / 2 : ℝ) * h81 + (-1 / 2 : ℝ) * h88
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + 2 * h3 - h9 + h33 - h80 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h87 + (1 / 2 : ℝ) * h88 + (-1 / 2 : ℝ) * h91
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h31 - h78
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h1 - h4 + h31 + h32 - h37 - h78 - h79 + h82
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 + h30 - h34 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h85 + (-1 / 2 : ℝ) * h88 + (1 / 2 : ℝ) * h89
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h3 - h6 + h31 + h33 - h38 - h78 - h80 + h83
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h32 - h79
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h1 + h30 - h35 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h86 + (-1 / 2 : ℝ) * h88 + (1 / 2 : ℝ) * h90
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h3 - h8 + h32 + h33 - h39 - h79 - h80 + h84
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 - h1 + 4 * h2 - 2 * h5 - 5 * h10 - h12 + 2 * h15 + h21 - h24 - 5 * h30 - h31 + 2 * h34 + h50 - 2 * h51 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h58 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h62 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - 2 * h78 - 2 * h81 + (1 / 2 : ℝ) * h85 + h88 + (-1 / 2 : ℝ) * h89 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + 3 * h120 + (3 / 2 : ℝ) * h125 - h127 + (-1 / 2 : ℝ) * h130 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h193 + h194
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h3 + h30 - h36 + (-1 / 2 : ℝ) * h81 + (1 / 2 : ℝ) * h87 + (-1 / 2 : ℝ) * h88 + (1 / 2 : ℝ) * h91
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h3 + h33 - h80
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 + h1 - 4 * h3 + 2 * h6 + 5 * h10 + h13 - 2 * h16 - h21 + h24 + 5 * h40 + h41 - 2 * h44 - h50 + 2 * h52 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h59 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h63 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + 2 * h92 + (3 / 2 : ℝ) * h95 + (-1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h103 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - 3 * h134 + (-3 / 2 : ℝ) * h139 + h141 + (1 / 2 : ℝ) * h144 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h195 - h196
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h0 + h3 - h6 + h41 - h92 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h103
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h1 + h3 - h8 + h42 - h93 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h104
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h2 + h3 - h9 + h43 - h94 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h105
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h3 + h40 + (-1 / 2 : ℝ) * h95 + (-1 / 2 : ℝ) * h102
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h41 - h92
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h1 - h4 + h41 + h42 - h47 - h92 - h93 + h96
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + h2 - h5 + h41 + h43 - h48 - h92 - h94 + h97
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 + h40 - h44 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h103
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h42 - h93
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h1 + h2 - h7 + h42 + h43 - h49 - h93 - h94 + h98
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h1 + h40 - h45 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h104
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h2 + h43 - h94
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h2 + h40 - h46 + (-1 / 2 : ℝ) * h95 + (1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h105
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 - h1 + 4 * h3 - 2 * h6 - 5 * h10 - h13 + 2 * h16 + h21 - h24 - 5 * h40 - h41 + 2 * h44 + h50 - 2 * h52 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h63 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - 2 * h92 - 2 * h95 + (1 / 2 : ℝ) * h99 + h102 + (-1 / 2 : ℝ) * h103 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + 3 * h134 + (3 / 2 : ℝ) * h139 - h141 + (-1 / 2 : ℝ) * h144 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h195 + h196
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h11 - h14
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h12 - h15
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h13 - h16
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h12 - h17
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h13 - h18
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + h13 - h19
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h13
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h20 - h106
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h10 + h11 - h14 + h20 - h106 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h10 + h21 - h24 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h12 - h15 + h20 + h22 - h25 - h106 - h107 + h109
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h13 - h16 + h20 + h23 - h26 - h106 - h108 + h110
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 - 2 * h1 + h4 + 2 * h10 - h14 + h20 + h50 + (1 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h57 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h61 + (1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 - h106 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h21 + (-1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h116
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + 2 * h12 - h17 + h22 - h107 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h114 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h118
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + 2 * h13 - h18 + h23 - h108 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h115 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h119
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 + 2 * h1 - h4 - 2 * h10 + h14 - h20 - h50 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h57 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h61 + (-1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 + h106 + (1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h12 + h21 - h27 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h114 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h118
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h13 + h21 - h28 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h115 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h119
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + h22 - h107
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + h13 - h19 + h22 + h23 - h29 - h107 - h108 + h112
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h13 + h23 - h108
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h30 - h120
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h10 + h12 - h15 + h30 - h120 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h127 + (1 / 2 : ℝ) * h130 + (-1 / 2 : ℝ) * h131
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h11 - h14 + h30 + h32 - h35 - h120 - h121 + h123
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h10 + h31 - h34 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h127 + (-1 / 2 : ℝ) * h130 + (1 / 2 : ℝ) * h131
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h13 - h16 + h30 + h33 - h36 - h120 - h122 + h124
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 + h1 - 3 * h2 + h5 + 2 * h10 - h15 - h21 + h24 + h30 + h31 - h34 - h50 + 2 * h51 + (1 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h58 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h62 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + h81 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - h120 - h125 + (1 / 2 : ℝ) * h127 + (1 / 2 : ℝ) * h131 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h194
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h11 + h12 - h17 + h32 - h121 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h128 + (1 / 2 : ℝ) * h130 + (-1 / 2 : ℝ) * h132
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + h31 + (-1 / 2 : ℝ) * h125 + (-1 / 2 : ℝ) * h130
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + 2 * h13 - h19 + h33 - h122 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h129 + (1 / 2 : ℝ) * h130 + (-1 / 2 : ℝ) * h133
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h32 - h121
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h11 + h31 - h37 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h128 + (-1 / 2 : ℝ) * h130 + (1 / 2 : ℝ) * h132
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h13 - h18 + h32 + h33 - h39 - h121 - h122 + h126
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 - h1 + 3 * h2 - h5 - 2 * h10 + h15 + h21 - h24 - h30 - h31 + h34 + h50 - 2 * h51 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h58 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h62 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - h81 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + h120 + (1 / 2 : ℝ) * h125 + (-1 / 2 : ℝ) * h127 + (1 / 2 : ℝ) * h130 + (-1 / 2 : ℝ) * h131 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h194
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h13 + h31 - h38 + (-1 / 2 : ℝ) * h125 + (1 / 2 : ℝ) * h129 + (-1 / 2 : ℝ) * h130 + (1 / 2 : ℝ) * h133
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h13 + h33 - h122
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h40 - h134
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h10 + h13 - h16 + h40 - h134 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h141 + (1 / 2 : ℝ) * h144 + (-1 / 2 : ℝ) * h145
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h11 - h14 + h40 + h42 - h45 - h134 - h135 + h137
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h10 + h12 - h15 + h40 + h43 - h46 - h134 - h136 + h138
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h10 + h41 - h44 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h141 + (-1 / 2 : ℝ) * h144 + (1 / 2 : ℝ) * h145
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h0 + h1 - 3 * h3 + h6 + 2 * h10 - h16 - h21 + h24 + h40 + h41 - h44 - h50 + 2 * h52 + (1 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h59 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h63 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + h95 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - h134 - h139 + (1 / 2 : ℝ) * h141 + (1 / 2 : ℝ) * h145 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h196
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h11 + h13 - h18 + h42 - h135 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h142 + (1 / 2 : ℝ) * h144 + (-1 / 2 : ℝ) * h146
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h12 + h13 - h19 + h43 - h136 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h143 + (1 / 2 : ℝ) * h144 + (-1 / 2 : ℝ) * h147
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h13 + h41 + (-1 / 2 : ℝ) * h139 + (-1 / 2 : ℝ) * h144
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h42 - h135
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h11 + h12 - h17 + h42 + h43 - h49 - h135 - h136 + h140
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h11 + h41 - h47 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h142 + (-1 / 2 : ℝ) * h144 + (1 / 2 : ℝ) * h146
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h12 + h43 - h136
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h12 + h41 - h48 + (-1 / 2 : ℝ) * h139 + (1 / 2 : ℝ) * h143 + (-1 / 2 : ℝ) * h144 + (1 / 2 : ℝ) * h147
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h0 - h1 + 3 * h3 - h6 - 2 * h10 + h16 + h21 - h24 - h40 - h41 + h44 + h50 - 2 * h52 + (-1 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h63 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - h95 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + h134 + (1 / 2 : ℝ) * h139 + (-1 / 2 : ℝ) * h141 + (1 / 2 : ℝ) * h144 + (-1 / 2 : ℝ) * h145 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h196
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h21 - h24
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h22 - h25
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h23 - h26
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h22 - h27
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h23 - h28
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h22
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h22 + h23 - h29
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h23
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h30 - h148
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h21 - h24 + h30 + h31 - h34 - h148 - h149 + h151
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h20 + h22 - h25 + h30 - h148 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h155 + (1 / 2 : ℝ) * h158 + (-1 / 2 : ℝ) * h159
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h20 + h32 - h35 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h155 + (-1 / 2 : ℝ) * h158 + (1 / 2 : ℝ) * h159
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h23 - h26 + h30 + h33 - h36 - h148 - h150 + h152
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h31 - h149
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h21 + h22 - h27 + h31 - h149 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h156 + (1 / 2 : ℝ) * h158 + (-1 / 2 : ℝ) * h160
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h21 + h32 - h37 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h156 + (-1 / 2 : ℝ) * h158 + (1 / 2 : ℝ) * h160
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h23 - h28 + h31 + h33 - h38 - h149 - h150 + h153
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 + 4 * h1 - 3 * h2 + 2 * h5 - h7 + 5 * h10 + h12 - 2 * h15 - 3 * h20 - h21 - h22 + h24 + h25 + h30 + h31 - 2 * h34 + h35 - h50 + 2 * h51 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h58 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h62 + (-3 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + 2 * h78 - 2 * h79 + h81 + (-1 / 2 : ℝ) * h85 + (1 / 2 : ℝ) * h86 + (1 / 2 : ℝ) * h89 + (-1 / 2 : ℝ) * h90 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - 3 * h120 + (-3 / 2 : ℝ) * h125 + h127 + (1 / 2 : ℝ) * h130 + 2 * h148 + (1 / 2 : ℝ) * h154 + (-1 / 2 : ℝ) * h155 + (-1 / 2 : ℝ) * h158 + (1 / 2 : ℝ) * h159 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h193 - h194 + h197
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h22 + h32 + (-1 / 2 : ℝ) * h154 + (-1 / 2 : ℝ) * h158
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h22 + 2 * h23 - h29 + h33 - h150 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h157 + (1 / 2 : ℝ) * h158 + (-1 / 2 : ℝ) * h161
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 - 4 * h1 + 3 * h2 - 2 * h5 + h7 - 5 * h10 - h12 + 2 * h15 + 3 * h20 + h21 + h22 - h24 - h25 - h30 - h31 + 2 * h34 - h35 + h50 - 2 * h51 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h58 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h62 + (3 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - 2 * h78 + 2 * h79 - h81 + (1 / 2 : ℝ) * h85 + (-1 / 2 : ℝ) * h86 + (-1 / 2 : ℝ) * h89 + (1 / 2 : ℝ) * h90 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + 3 * h120 + (3 / 2 : ℝ) * h125 - h127 + (-1 / 2 : ℝ) * h130 - 2 * h148 - h154 + (1 / 2 : ℝ) * h155 + h158 + (-1 / 2 : ℝ) * h159 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h193 + h194 - h197
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h23 + h32 - h39 + (-1 / 2 : ℝ) * h154 + (1 / 2 : ℝ) * h157 + (-1 / 2 : ℝ) * h158 + (1 / 2 : ℝ) * h161
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h23 + h33 - h150
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h40 - h162
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h21 - h24 + h40 + h41 - h44 - h162 - h163 + h165
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h20 + h23 - h26 + h40 - h162 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h169 + (1 / 2 : ℝ) * h172 + (-1 / 2 : ℝ) * h173
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h20 + h22 - h25 + h40 + h43 - h46 - h162 - h164 + h166
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h20 + h42 - h45 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h169 + (-1 / 2 : ℝ) * h172 + (1 / 2 : ℝ) * h173
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h41 - h163
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h21 + h23 - h28 + h41 - h163 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h170 + (1 / 2 : ℝ) * h172 + (-1 / 2 : ℝ) * h174
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h21 + h22 - h27 + h41 + h43 - h48 - h163 - h164 + h167
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h21 + h42 - h47 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h170 + (-1 / 2 : ℝ) * h172 + (1 / 2 : ℝ) * h174
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 + 4 * h1 - 3 * h3 + 2 * h6 - h8 + 5 * h10 + h13 - 2 * h16 - 3 * h20 - h21 - h23 + h24 + h26 + h40 + h41 - 2 * h44 + h45 - h50 + 2 * h52 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h59 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h63 + (-3 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 + 2 * h92 - 2 * h93 + h95 + (-1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h103 + (-1 / 2 : ℝ) * h104 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - 3 * h134 + (-3 / 2 : ℝ) * h139 + h141 + (1 / 2 : ℝ) * h144 + 2 * h162 + (1 / 2 : ℝ) * h168 + (-1 / 2 : ℝ) * h169 + (-1 / 2 : ℝ) * h172 + (1 / 2 : ℝ) * h173 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h195 - h196 + h198
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h22 + h23 - h29 + h43 - h164 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h171 + (1 / 2 : ℝ) * h172 + (-1 / 2 : ℝ) * h175
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h23 + h42 + (-1 / 2 : ℝ) * h168 + (-1 / 2 : ℝ) * h172
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h22 + h43 - h164
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h22 + h42 - h49 + (-1 / 2 : ℝ) * h168 + (1 / 2 : ℝ) * h171 + (-1 / 2 : ℝ) * h172 + (1 / 2 : ℝ) * h175
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 - 4 * h1 + 3 * h3 - 2 * h6 + h8 - 5 * h10 - h13 + 2 * h16 + 3 * h20 + h21 + h23 - h24 - h26 - h40 - h41 + 2 * h44 - h45 + h50 - 2 * h52 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h63 + (3 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 - 2 * h92 + 2 * h93 - h95 + (1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h103 + (1 / 2 : ℝ) * h104 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + 3 * h134 + (3 / 2 : ℝ) * h139 - h141 + (-1 / 2 : ℝ) * h144 - 2 * h162 - h168 + (1 / 2 : ℝ) * h169 + h172 + (-1 / 2 : ℝ) * h173 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h195 + h196 - h198
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h31 - h34
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h32 - h35
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h33 - h36
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h31
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h31 + h32 - h37
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h31 + h33 - h38
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h32
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h32 + h33 - h39
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h33
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h40 - h176
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h31 - h34 + h40 + h41 - h44 - h176 - h177 + h179
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h30 + h32 - h35 + h40 + h42 - h45 - h176 - h178 + h180
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h30 + h33 - h36 + h40 - h176 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h183 + (1 / 2 : ℝ) * h186 + (-1 / 2 : ℝ) * h187
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h30 + h43 - h46 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h183 + (-1 / 2 : ℝ) * h186 + (1 / 2 : ℝ) * h187
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h31 + h41 - h177
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h31 + h32 - h37 + h41 + h42 - h47 - h177 - h178 + h181
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h31 + h33 - h38 + h41 - h177 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h184 + (1 / 2 : ℝ) * h186 + (-1 / 2 : ℝ) * h188
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h31 + h43 - h48 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h184 + (-1 / 2 : ℝ) * h186 + (1 / 2 : ℝ) * h188
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h32 + h42 - h178
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 2 * h32 + h33 - h39 + h42 - h178 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h185 + (1 / 2 : ℝ) * h186 + (-1 / 2 : ℝ) * h189
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -h32 + h43 - h49 + (-1 / 2 : ℝ) * h182 + (1 / 2 : ℝ) * h185 + (-1 / 2 : ℝ) * h186 + (1 / 2 : ℝ) * h189
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) -4 * h0 + h1 + 3 * h2 - 3 * h3 + 2 * h6 - h9 + 5 * h10 + h13 - 2 * h16 - h21 + h24 - 3 * h30 - h33 + h36 + h40 + h41 - 2 * h44 + h46 - h50 + 2 * h52 + (3 / 2 : ℝ) * h53 + (-1 / 2 : ℝ) * h59 + (-1 / 2 : ℝ) * h60 + (1 / 2 : ℝ) * h63 + (-1 / 2 : ℝ) * h67 + (-1 / 2 : ℝ) * h74 - h81 + 2 * h92 - 2 * h94 + h95 + (-1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h103 + (-1 / 2 : ℝ) * h105 + (1 / 2 : ℝ) * h111 + (-1 / 2 : ℝ) * h113 + (1 / 2 : ℝ) * h116 + (-1 / 2 : ℝ) * h117 - 3 * h134 + (-3 / 2 : ℝ) * h139 + h141 + (1 / 2 : ℝ) * h144 + 2 * h176 + (1 / 2 : ℝ) * h182 + (-1 / 2 : ℝ) * h183 + (-1 / 2 : ℝ) * h186 + (1 / 2 : ℝ) * h187 + (1 / 2 : ℝ) * h191 + (1 / 2 : ℝ) * h192 - h195 - h196 + h199
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h33 + h43 + (-1 / 2 : ℝ) * h182 + (-1 / 2 : ℝ) * h186
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) 4 * h0 - h1 - 3 * h2 + 3 * h3 - 2 * h6 + h9 - 5 * h10 - h13 + 2 * h16 + h21 - h24 + 3 * h30 + h33 - h36 - h40 - h41 + 2 * h44 - h46 + h50 - 2 * h52 + (-3 / 2 : ℝ) * h53 + (1 / 2 : ℝ) * h59 + (1 / 2 : ℝ) * h60 + (-1 / 2 : ℝ) * h63 + (1 / 2 : ℝ) * h67 + (1 / 2 : ℝ) * h74 + h81 - 2 * h92 + 2 * h94 - h95 + (1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h103 + (1 / 2 : ℝ) * h105 + (-1 / 2 : ℝ) * h111 + (1 / 2 : ℝ) * h113 + (-1 / 2 : ℝ) * h116 + (1 / 2 : ℝ) * h117 + 3 * h134 + (3 / 2 : ℝ) * h139 - h141 + (-1 / 2 : ℝ) * h144 - 2 * h176 - h182 + (1 / 2 : ℝ) * h183 + h186 + (-1 / 2 : ℝ) * h187 + (-1 / 2 : ℝ) * h191 + (-1 / 2 : ℝ) * h192 + h195 + h196 - h199
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h40
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h40 + h41 - h44
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h40 + h42 - h45
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h40 + h43 - h46
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h41
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h41 + h42 - h47
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h41 + h43 - h48
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h42
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h42 + h43 - h49
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (norm := ring1!) h43
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp +decide [productCoefficient, coefficientMatrix, diagonalIndex, pairIndex,
      upperBasis, upperIndex, symmUnit, unit, Matrix.mul_apply, Fin.sum_univ_succ]

noncomputable def matrixFunctional (C : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ where
  toFun X := ∑ i : Fin 5, ∑ j : Fin 5, C i j * X i j
  map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm]

noncomputable def productBilinear (L : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ where
  toFun X :=
    { toFun := fun Y => L (X * Y)
      map_add' := by intros; simp [Matrix.mul_add]
      map_smul' := by intros; simp [Matrix.mul_smul] }
  map_add' := by intros; ext Y; simp [Matrix.add_mul]
  map_smul' := by intros; ext Y; simp [Matrix.smul_mul]

/-- A bilinear form on symmetric five-by-five matrices that vanishes on
orthogonal rank-one squares factors through the matrix product. -/
theorem bilinear_product_classification
    (B : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ)
    (hB : ∀ u v : Fin 5 → ℝ, u ⬝ᵥ v = 0 → B (rankOne u) (rankOne v) = 0) :
    ∃ L : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ,
      ∀ X Y : Matrix (Fin 5) (Fin 5) ℝ,
        X.IsSymm → Y.IsSymm → B X Y = L (X * Y) := by
  let T : Fin 15 → Fin 15 → ℝ := fun a b => B (upperBasis a) (upperBasis b)
  have hT := orthogonal_rankOne_coefficient_classification T (by
    intro u v huv
    change (∑ a : Fin 15, ∑ b : Fin 15,
      upperCoordinate (rankOne u) a * upperCoordinate (rankOne v) b *
        B (upperBasis a) (upperBasis b)) = 0
    rw [← bilinear_upper_expansion B (rankOne u) (rankOne v)
      (rankOne_isSymm u) (rankOne_isSymm v)]
    exact hB u v huv)
  let L := matrixFunctional (coefficientMatrix T)
  refine ⟨L, ?_⟩
  intro X Y hX hY
  change B X Y = productBilinear L X Y
  rw [bilinear_upper_expansion B X Y hX hY,
    bilinear_upper_expansion (productBilinear L) X Y hX hY]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hab : B (upperBasis a) (upperBasis b) =
      productBilinear L (upperBasis a) (upperBasis b) := hT a b
  rw [hab]

end PBCounterexample.SymmetricAlgebra
