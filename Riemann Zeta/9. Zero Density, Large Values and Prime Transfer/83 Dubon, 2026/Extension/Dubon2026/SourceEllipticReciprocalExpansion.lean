import Dubon2026.SourceEllipticInfinityProducts
import Dubon2026.SourceEllipticTranslationCoordinates

/-! The two finite reciprocal expansions needed by the literal Velu corrections.
Exact field identities give remainder bounds at the actual infinity valuation.
These estimates will discharge the explicit quotient error bound, the remaining
equation input to the odd quotient map on the DUB-17/18 dependency chain. -/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- The shifted reciprocal differs from the actual x reciprocal by a term of order at least four. -/
theorem infinityValuation_inv_kernel_sub_inv (a : F) :
    infinityValuation W ((genericX W - algebraMap F W.FunctionField a)⁻¹ - (genericX W)⁻¹) ≤
      WithZero.exp (-4) := by
  have hx : genericX W ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W 0
  have hd := sub_ne_zero.mpr (genericX_ne_constant W a)
  have he : (genericX W - algebraMap F W.FunctionField a)⁻¹ - (genericX W)⁻¹ =
      algebraMap F W.FunctionField a /
        (genericX W * (genericX W - algebraMap F W.FunctionField a)) := by
    field_simp
    ring
  rw [he, div_mul_eq_div_div]
  have h : infinityValuation W (algebraMap F W.FunctionField a / genericX W) ≤
      WithZero.exp (-2) := by
    simpa only [pow_one] using infinityValuation_div_genericX_power_le W
      (m := 0) (by simpa only [WithZero.exp_zero] using infinityValuation_constant_le_one W a) 1
  simpa only [pow_one] using infinityValuation_div_kernel_power_le W a 1 h

/-- Removing the linear reciprocal correction leaves a term of order at least six. -/
theorem infinityValuation_inv_kernel_second_remainder (a : F) :
    infinityValuation W ((genericX W - algebraMap F W.FunctionField a)⁻¹ - (genericX W)⁻¹ -
      algebraMap F W.FunctionField a / genericX W ^ 2) ≤ WithZero.exp (-6) := by
  have hx : genericX W ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W 0
  have hd := sub_ne_zero.mpr (genericX_ne_constant W a)
  have he : (genericX W - algebraMap F W.FunctionField a)⁻¹ - (genericX W)⁻¹ -
      algebraMap F W.FunctionField a / genericX W ^ 2 =
      algebraMap F W.FunctionField (a ^ 2) /
        (genericX W ^ 2 * (genericX W - algebraMap F W.FunctionField a)) := by
    rw [map_pow]
    field_simp
    ring
  rw [he, div_mul_eq_div_div]
  have h : infinityValuation W (algebraMap F W.FunctionField (a ^ 2) / genericX W ^ 2) ≤
      WithZero.exp (-4) :=
    infinityValuation_div_genericX_power_le W (m := 0)
      (by simpa only [WithZero.exp_zero] using infinityValuation_constant_le_one W (a ^ 2)) 2
  simpa only [pow_one] using infinityValuation_div_kernel_power_le W a 1 h

end Dubon2026.SourceEllipticFunctionField
