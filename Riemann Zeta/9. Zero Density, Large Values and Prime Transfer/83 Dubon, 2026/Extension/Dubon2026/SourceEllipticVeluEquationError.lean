import Dubon2026.SourceEllipticVeluPolynomialVanishing
import Dubon2026.SourceEllipticOddQuadraticRelation

/-! The literal explicit quotient equation error. The actual odd quadratic
relation places this error in F[X] + F[X]Y, and the proved pole parity shows
that an error vanishing at infinity must be zero. The sole remaining input
to this reduction is an explicit infinity-value estimate for the literal
finite formulas; this file does not assert that estimate or the unconditional
quotient equation. It serves the DUB-17/18 odd quotient-map dependency. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The exact error in the explicit Velu quotient equation at the literal generic coordinates. -/
noncomputable def veluEquationError : W.toAffine.FunctionField :=
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericVeluX W S
  let y := genericVeluY W S
  y ^ 2 + c W.a₁ * x * y + c W.a₃ * y -
    (x ^ 3 + c W.a₂ * x ^ 2 + c (veluQuotient W S).a₄ * x + c (veluQuotient W S).a₆)

/-- Vanishing of the exact error is the actual native explicit quotient equation. -/
theorem veluEquationError_eq_zero_iff : veluEquationError W S = 0 ↔
    ((veluQuotient W S)⁄W.toAffine.FunctionField).toAffine.Equation
      (genericVeluX W S) (genericVeluY W S) := by
  rw [Affine.equation_iff]
  exact sub_eq_zero

variable [DecidableEq F] [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd relation reduces the explicit quotient equation to the literal error's infinity estimate. -/
theorem odd_velu_equation_of_error_value_lt_one (hQ : addOrderOf Q = 2 * n + 1)
    (hsmall : infinityValuation W.toAffine
      (veluEquationError W (oddOrderSummingSet W Q n)) < 1) :
    ((veluQuotient W (oddOrderSummingSet W Q n))⁄W.toAffine.FunctionField).toAffine.Equation
      (genericVeluX W (oddOrderSummingSet W Q n))
      (genericVeluY W (oddOrderSummingSet W Q n)) := by
  let T := oddOrderSummingSet W Q n
  obtain ⟨p, q, hrel⟩ := exists_odd_genericVelu_quadratic_relation W hQ
  let r : F[X] := C W.a₁ * Polynomial.X + C W.a₃ - p
  let s : F[X] := -(Polynomial.X ^ 3 + C W.a₂ * Polynomial.X ^ 2 +
    C (veluQuotient W T).a₄ * Polynomial.X + C (veluQuotient W T).a₆) - q
  have he : aeval (genericVeluX W T) r * genericVeluY W T + aeval (genericVeluX W T) s =
      veluEquationError W T := by
    dsimp only [r, s, veluEquationError]
    simp only [map_sub, map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C]
    linear_combination (norm := ring!) -hrel
  have hz := velu_polynomial_pair_eq_zero_of_value_lt_one W T (p := r) (q := s) (by
    rw [he]
    exact hsmall)
  exact (veluEquationError_eq_zero_iff W T).mp (he.symm.trans hz)

end Dubon2026.SourceEllipticFunctionField
