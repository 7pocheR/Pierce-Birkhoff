import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Finite coefficient calculations and integer matrix certificates. -/

noncomputable section

namespace PBCounterexample.FiniteCoefficientCertificate

open Polynomial

def polynomialOfList {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | c :: cs => C c + X * polynomialOfList cs

theorem polynomialOfList_coeff {R : Type*} [Semiring R] (cs : List R) (k : ℕ) :
    (polynomialOfList cs).coeff k = cs[k]?.getD 0 := by
  induction cs generalizing k with
  | nil => simp [polynomialOfList]
  | cons c cs ih =>
    cases k with
    | zero => simp [polynomialOfList]
    | succ k => simp [polynomialOfList, coeff_X_mul, ih]

def coeffAt (a : List ℤ) (k : ℕ) : ℤ := a[k]?.getD 0

def convolution (a b : List ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), coeffAt a j * coeffAt b (k-j)

def CoeffCert (n : ℕ) (p : ℤ[X]) (a : List ℤ) : Prop :=
  ∀ k : Fin n, p.coeff k = coeffAt a k

theorem CoeffCert.ofList (n : ℕ) (a : List ℤ) :
    CoeffCert n (polynomialOfList a) a := fun k => polynomialOfList_coeff a k

theorem CoeffCert.const {n : ℕ} (z : ℤ) : CoeffCert n (C z) [z] := by
  intro k
  rw [coeff_C]
  rcases k with ⟨k, hk⟩
  cases k with
  | zero => simp [coeffAt]
  | succ k => simp [coeffAt]

theorem CoeffCert.add {n : ℕ} {p q : ℤ[X]} {a b c : List ℤ}
    (hp : CoeffCert n p a) (hq : CoeffCert n q b)
    (h : ∀ k : Fin n, coeffAt a k + coeffAt b k = coeffAt c k) :
    CoeffCert n (p+q) c := by
  intro k
  rw [coeff_add, hp k, hq k, h k]

theorem CoeffCert.sub {n : ℕ} {p q : ℤ[X]} {a b c : List ℤ}
    (hp : CoeffCert n p a) (hq : CoeffCert n q b)
    (h : ∀ k : Fin n, coeffAt a k - coeffAt b k = coeffAt c k) :
    CoeffCert n (p-q) c := by
  intro k
  rw [coeff_sub, hp k, hq k, h k]

theorem CoeffCert.mul {n : ℕ} {p q : ℤ[X]} {a b c : List ℤ}
    (hp : CoeffCert n p a) (hq : CoeffCert n q b)
    (h : ∀ k : Fin n, convolution a b k = coeffAt c k) :
    CoeffCert n (p*q) c := by
  intro k
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← h k]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ (k : ℕ) := by simpa using Finset.mem_range.mp hj
  rw [hp ⟨j, lt_of_le_of_lt hjk k.isLt⟩,
    hq ⟨(k : ℕ)-j, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩]

theorem CoeffCert.zero_coeff {n : ℕ} {p : ℤ[X]} (h : CoeffCert n p [])
    (k : ℕ) (hk : k < n) : p.coeff k = 0 := by
  simpa [coeffAt] using h ⟨k,hk⟩

theorem CoeffCert.X_pow_dvd {n : ℕ} {p : ℤ[X]} (h : CoeffCert n p []) :
    X^n ∣ p := X_pow_dvd_iff.mpr h.zero_coeff

theorem real_det_ne_zero_of_modular_inverse {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (V : Matrix (Fin n) (Fin n) (ZMod 1009))
    (h : M.map (Int.castRingHom (ZMod 1009)) * V = 1) :
    (M.map (Int.castRingHom ℝ)).det ≠ 0 := by
  letI : Fact (1 < 1009) := ⟨by decide⟩
  have hz : (M.map (Int.castRingHom (ZMod 1009))).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse h).ne_zero
  have hi : M.det ≠ 0 := by
    intro he
    apply hz
    change ((Int.castRingHom (ZMod 1009)).mapMatrix M).det = 0
    rw [← RingHom.map_det, he, map_zero]
  change ((Int.castRingHom ℝ).mapMatrix M).det ≠ 0
  rw [← RingHom.map_det]
  change (M.det : ℝ) ≠ 0
  exact_mod_cast hi

end PBCounterexample.FiniteCoefficientCertificate
