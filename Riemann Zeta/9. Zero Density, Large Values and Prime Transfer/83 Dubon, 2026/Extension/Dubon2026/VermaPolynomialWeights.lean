import Dubon2026.VermaPolynomialOperators

/-! # Exact original monomial weights and singular vectors in polynomial Verma modules -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplication by the actual polynomial variable gives the next original monomial. -/
theorem vermaPolynomialF_X_pow (n : ℕ) :
    vermaPolynomialF (X ^ n : R[X]) = X ^ (n + 1) := by
  rw [vermaPolynomialF_apply, pow_succ']

/-- The original nth monomial has its exact weight μ minus twice n. -/
theorem vermaPolynomialH_X_pow (μ : R) (n : ℕ) :
    vermaPolynomialH μ (X ^ n) = (μ - 2 * n) • (X ^ n : R[X]) := by
  cases n with
  | zero => simp [vermaPolynomialH_apply, smul_eq_C_mul]
  | succ n =>
      rw [vermaPolynomialH_apply, derivative_X_pow_succ]
      simp only [smul_eq_C_mul, map_sub, map_mul, map_ofNat, map_natCast,
        Nat.cast_add, Nat.cast_one, map_add, map_one, pow_succ]
      ring

/-- The actual Verma raising coefficient is exactly (n+1)(μ-n). -/
theorem vermaPolynomialE_X_pow_succ (μ : R) (n : ℕ) :
    vermaPolynomialE μ (X ^ (n + 1)) = ((n + 1 : R) * (μ - n)) • (X ^ n : R[X]) := by
  cases n with
  | zero => simp [vermaPolynomialE_apply, smul_eq_C_mul]
  | succ n =>
      rw [vermaPolynomialE_apply, derivative_X_pow_succ, derivative_C_mul, derivative_X_pow_succ]
      simp only [smul_eq_C_mul, map_mul, map_sub, map_add, map_natCast, map_one,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- At original natural highest weight n, the original nonzero monomial X^(n+1) is killed by the actual raising operator and has reflected weight -n-2. -/
theorem vermaPolynomial_singular_vector (n : ℕ) :
    vermaPolynomialE (n : R) (X ^ (n + 1)) = 0 ∧
      vermaPolynomialH (n : R) (X ^ (n + 1)) = (-((n : R)) - 2) • (X ^ (n + 1) : R[X]) := by
  constructor
  · rw [vermaPolynomialE_X_pow_succ, sub_self, mul_zero, zero_smul]
  · rw [vermaPolynomialH_X_pow]
    congr 1
    push_cast
    ring

end
end Dubon2026
