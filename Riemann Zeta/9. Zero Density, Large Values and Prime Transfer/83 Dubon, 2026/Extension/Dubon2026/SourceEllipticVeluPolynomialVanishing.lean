import Dubon2026.SourceEllipticVeluPolePolynomial

/-! A polynomial in the literal Velu x-coordinate plus a polynomial times its
y-coordinate cannot vanish at infinity unless it is zero. The actual double
and triple poles give different parity, preventing cancellation. This lets
the explicit odd quotient equation be proved by a direct finite-formula
error estimate, avoiding separate identification of five coefficients. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- A polynomial-linear expression in the literal quotient coordinates with value below one is zero. -/
theorem velu_polynomial_pair_eq_zero_of_value_lt_one {p q : F[X]}
    (h : infinityValuation W.toAffine
      (aeval (genericVeluX W S) p * genericVeluY W S + aeval (genericVeluX W S) q) < 1) :
    aeval (genericVeluX W S) p * genericVeluY W S + aeval (genericVeluX W S) q = 0 := by
  by_cases hq : q = 0
  · by_cases hp : p = 0
    · simp [hp, hq]
    · rw [hq, map_zero, add_zero, map_mul, infinityValuation_aeval_genericVeluX W S hp,
        infinityValuation_genericVeluY, ← WithZero.exp_add,
        ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      omega
  · rw [infinityValuation_aeval_mul_add W S hq] at h
    have he := (le_max_right
      (infinityValuation W.toAffine (aeval (genericVeluX W S) p * genericVeluY W S))
      (WithZero.exp (2 * q.natDegree : ℤ))).trans_lt h
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at he
    omega

end Dubon2026.SourceEllipticFunctionField
