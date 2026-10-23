import Dubon2026.SourceEllipticInfinityValuation

/-! Bounds for the actual coordinate denominators and constant coefficients at
infinity. These are the specific valuation inputs for the literal finite Velu
corrections; no pole or regularity assumption is added to those coordinates. -/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- Every original constant has infinity value at most one. -/
theorem infinityValuation_constant_le_one (a : F) :
    infinityValuation W (algebraMap F W.FunctionField a) ≤ 1 := by
  letI := infinityValuation_trivial W
  exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ a

/-- Subtracting an original constant does not alter the generic x pole. -/
theorem infinityValuation_genericX_sub_constant (a : F) :
    infinityValuation W (genericX W - algebraMap F W.FunctionField a) = WithZero.exp 2 := by
  have hlt : infinityValuation W (algebraMap F W.FunctionField a) <
      infinityValuation W (genericX W) := by
    rw [infinityValuation_genericX]
    refine (infinityValuation_constant_le_one W a).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  rw [Valuation.map_sub_eq_of_lt_left _ hlt, infinityValuation_genericX]

/-- An actual constant multiplier cannot increase an infinity-value bound. -/
theorem infinityValuation_constant_mul_le (a : F) {z : W.FunctionField} {m : ℤ}
    (hz : infinityValuation W z ≤ WithZero.exp m) :
    infinityValuation W (algebraMap F W.FunctionField a * z) ≤ WithZero.exp m := by
  rw [map_mul]
  calc
    _ ≤ 1 * infinityValuation W z := mul_le_mul_left (infinityValuation_constant_le_one W a) _
    _ = infinityValuation W z := one_mul _
    _ ≤ _ := hz

/-- A power of an actual kernel denominator lowers the value exponent by twice its power. -/
theorem infinityValuation_div_kernel_power_le (a : F) (k : ℕ)
    {z : W.FunctionField} {m : ℤ} (hz : infinityValuation W z ≤ WithZero.exp m) :
    infinityValuation W (z / (genericX W - algebraMap F W.FunctionField a) ^ k) ≤
      WithZero.exp (m - 2 * k) := by
  rw [map_div₀, map_pow, infinityValuation_genericX_sub_constant, ← WithZero.exp_nsmul]
  calc
    _ ≤ WithZero.exp m / WithZero.exp (k • (2 : ℤ)) := by
      gcongr
      exact zero_le
    _ = WithZero.exp (m - 2 * k) := by
      rw [← WithZero.exp_sub]
      simp only [nsmul_eq_mul, mul_comm]

end Dubon2026.SourceEllipticFunctionField
