import Dubon2026.SourceEllipticInfinityBounds

/-! Product and denominator estimates for the literal finite quotient error.
These compose the already proved actual infinity valuation bounds. They are
used for the finite reciprocal expansions needed to prove that the explicit
odd quotient equation error vanishes at infinity on the DUB-17/18 chain. -/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- Actual infinity-value exponents add under a product bound. -/
theorem infinityValuation_mul_le {a b : W.FunctionField} {m n : ℤ}
    (ha : infinityValuation W a ≤ WithZero.exp m) (hb : infinityValuation W b ≤ WithZero.exp n) :
    infinityValuation W (a * b) ≤ WithZero.exp (m + n) := by
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' ha hb

/-- Actual infinity-value exponents multiply under a natural power bound. -/
theorem infinityValuation_pow_le {a : W.FunctionField} {m : ℤ}
    (ha : infinityValuation W a ≤ WithZero.exp m) (k : ℕ) :
    infinityValuation W (a ^ k) ≤ WithZero.exp ((k : ℤ) * m) := by
  rw [map_pow, ← nsmul_eq_mul, WithZero.exp_nsmul]
  exact pow_le_pow_left' ha k

/-- Division by a power of the actual generic x-coordinate lowers the exponent by twice its power. -/
theorem infinityValuation_div_genericX_power_le {a : W.FunctionField} {m : ℤ}
    (ha : infinityValuation W a ≤ WithZero.exp m) (k : ℕ) :
    infinityValuation W (a / genericX W ^ k) ≤ WithZero.exp (m - 2 * k) := by
  simpa only [map_zero, sub_zero] using infinityValuation_div_kernel_power_le W 0 k ha

/-- The reciprocal of every actual shifted x-coordinate has value exp minus two. -/
theorem infinityValuation_inv_kernel (a : F) :
    infinityValuation W ((genericX W - algebraMap F W.FunctionField a)⁻¹) =
      WithZero.exp (-2) := by
  rw [map_inv₀, infinityValuation_genericX_sub_constant, ← WithZero.exp_neg]

/-- The reciprocal of the actual generic x-coordinate has value exp minus two. -/
theorem infinityValuation_inv_genericX :
    infinityValuation W (genericX W)⁻¹ = WithZero.exp (-2) := by
  rw [map_inv₀, infinityValuation_genericX, ← WithZero.exp_neg]

end Dubon2026.SourceEllipticFunctionField
