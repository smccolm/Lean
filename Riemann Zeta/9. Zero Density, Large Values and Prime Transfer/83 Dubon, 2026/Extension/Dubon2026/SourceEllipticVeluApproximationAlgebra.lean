import Dubon2026.SourceEllipticVeluEquationError

/-! The exact numerator of the quotient equation on the two truncated
coordinate expansions. This field identity is applied to the actual generic
point and the literal T and W sums. It uses the original Weierstrass equation,
and introduces no assumptions about the quotient equation (DUB-17/18). -/

namespace Dubon2026.SourceEllipticFunctionField

/-- The truncated coordinates have an equation error with numerator of weighted degree at most eleven. -/
theorem velu_approximation_error_identity {K : Type*} [Field K]
    (a₁ a₂ a₃ a₄ a₆ t w x y : K) (hx : x ≠ 0)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    let X := (x ^ 3 + t * x + w) / x ^ 2
    let Y := ((x ^ 3 - t * x - 2 * w) * y - a₁ * t * x ^ 2) / x ^ 3
    Y ^ 2 + a₁ * X * Y + a₃ * Y -
      (X ^ 3 + a₂ * X ^ 2 + (a₄ - 5 * t) * X + (a₆ - (a₁ ^ 2 + 4 * a₂) * t - 7 * w)) =
      ((3 * t ^ 2 - 6 * a₂ * w - 3 * a₄ * t - a₁ * a₃ * t) * x ^ 5 +
        (3 * t * w - 5 * a₄ * w - 2 * a₆ * t) * x ^ 4 +
        (w ^ 2 + (2 * a₂ - a₁ ^ 2) * t * w + a₄ * t ^ 2 - 4 * a₆ * w - t ^ 3) * x ^ 3 +
        (3 * a₂ * w ^ 2 + 4 * a₄ * t * w + a₆ * t ^ 2 - 3 * t ^ 2 * w) * x ^ 2 +
        (4 * a₄ * w ^ 2 + 4 * a₆ * t * w - 3 * t * w ^ 2) * x +
        (4 * a₆ * w ^ 2 - w ^ 3) +
        (x ^ 3 - t * x - 2 * w) * ((a₃ * t + 3 * a₁ * w) * x + 2 * a₃ * w) * y) / x ^ 6 := by
  dsimp only
  field_simp
  linear_combination (x ^ 3 - t * x - 2 * w) ^ 2 * h

end Dubon2026.SourceEllipticFunctionField
