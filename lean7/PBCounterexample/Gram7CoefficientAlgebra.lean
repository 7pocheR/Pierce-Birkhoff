import PBCounterexample.FiniteCoefficientCertificate

/-! Coefficient identities for finite lists over a commutative ring. -/

namespace PBCounterexample.Gram7Coefficient

open Polynomial
open scoped BigOperators

noncomputable abbrev ofList := @FiniteCoefficientCertificate.polynomialOfList

def coeffAt {R : Type*} [Zero R] (a : List R) (k : ℕ) : R := a[k]?.getD 0

def convolution {R : Type*} [Semiring R] (a b : List R) (k : ℕ) : R :=
  ∑ j ∈ Finset.range (k + 1), coeffAt a j * coeffAt b (k-j)

def Cert {R : Type*} [Semiring R] (n : ℕ) (p : R[X]) (a : List R) : Prop :=
  ∀ k : Fin n, p.coeff k = coeffAt a k

theorem Cert.ofList {R : Type*} [Semiring R] (n : ℕ) (a : List R) :
    Cert n (ofList a) a := fun k => FiniteCoefficientCertificate.polynomialOfList_coeff a k

theorem Cert.const {R : Type*} [Semiring R] (n : ℕ) (r : R) :
    Cert n (C r) [r] := by
  intro k
  cases k with
  | mk k hk => cases k <;> simp [coeffAt]

theorem Cert.add {R : Type*} [Semiring R] {n : ℕ} {p q : R[X]} {a b c : List R}
    (hp : Cert n p a) (hq : Cert n q b)
    (h : ∀ k : Fin n, coeffAt a k + coeffAt b k = coeffAt c k) : Cert n (p+q) c := by
  intro k
  rw [coeff_add, hp k, hq k, h k]

theorem Cert.sub {R : Type*} [Ring R] {n : ℕ} {p q : R[X]} {a b c : List R}
    (hp : Cert n p a) (hq : Cert n q b)
    (h : ∀ k : Fin n, coeffAt a k - coeffAt b k = coeffAt c k) : Cert n (p-q) c := by
  intro k
  rw [coeff_sub, hp k, hq k, h k]

theorem Cert.scale {R : Type*} [Semiring R] {n : ℕ} {p : R[X]} {a b : List R}
    (r : R) (hp : Cert n p a)
    (h : ∀ k : Fin n, r * coeffAt a k = coeffAt b k) : Cert n (C r * p) b := by
  intro k
  rw [coeff_C_mul, hp k, h k]

theorem Cert.mul {R : Type*} [Semiring R] {n : ℕ} {p q : R[X]} {a b c : List R}
    (hp : Cert n p a) (hq : Cert n q b)
    (h : ∀ k : Fin n, convolution a b k = coeffAt c k) : Cert n (p*q) c := by
  intro k
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← h k]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ (k : ℕ) := by simpa using Finset.mem_range.mp hj
  rw [hp ⟨j, lt_of_le_of_lt hjk k.isLt⟩,
    hq ⟨(k : ℕ)-j, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩]

theorem Cert.X_pow_dvd {R : Type*} [Semiring R] {n : ℕ} {p : R[X]}
    (h : Cert n p []) : X^n ∣ p := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  simpa [coeffAt] using h ⟨k, hk⟩

end PBCounterexample.Gram7Coefficient
