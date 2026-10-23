import Dubon2026.SourceEllipticVeluErrorRemainder

/-! The literal odd-order Velu coordinates satisfy the explicit quotient
equation in every characteristic. The actual fixed-field quadratic relation
and pole parity force its error to vanish, using the independently proved
finite-formula error estimate. This removes the equation assumption from the
odd quotient pullback required by DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd finite Velu formulas satisfy the explicit quotient equation, including characteristics two and three. -/
theorem odd_genericVelu_equation (hQ : addOrderOf Q = 2 * n + 1) :
    ((veluQuotient W (oddOrderSummingSet W Q n))⁄W.toAffine.FunctionField).toAffine.Equation
      (genericVeluX W (oddOrderSummingSet W Q n))
      (genericVeluY W (oddOrderSummingSet W Q n)) := by
  apply odd_velu_equation_of_error_value_lt_one W hQ
  refine (infinityValuation_veluEquationError W _).trans_lt ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

end Dubon2026.SourceEllipticFunctionField
