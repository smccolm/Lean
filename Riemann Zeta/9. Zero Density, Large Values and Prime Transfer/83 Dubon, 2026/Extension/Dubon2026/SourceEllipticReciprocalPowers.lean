import Dubon2026.SourceEllipticReciprocalExpansion

/-! The squared and cubed reciprocal remainders needed by the literal finite
Velu formulas. Factoring differences of powers uses the already proved first
reciprocal remainders. These are the specific expansions needed to make the
explicit odd quotient error vanish at infinity, including characteristics two
and three, on the DUB-17/18 quotient-map dependency. -/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- The squared reciprocal correction has order at least six. -/
theorem infinityValuation_inv_kernel_square_sub (a : F) :
    infinityValuation W (((genericX W - algebraMap F W.FunctionField a)⁻¹) ^ 2 -
      ((genericX W)⁻¹) ^ 2) ≤ WithZero.exp (-6) := by
  rw [show ∀ A B : W.FunctionField, A ^ 2 - B ^ 2 = (A - B) * (A + B) from fun A B => by ring]
  exact infinityValuation_mul_le W (infinityValuation_inv_kernel_sub_inv W a)
    ((infinityValuation W).map_add_le (infinityValuation_inv_kernel W a).le
      (infinityValuation_inv_genericX W).le)

/-- Removing the first squared-reciprocal correction leaves order at least eight. -/
theorem infinityValuation_inv_kernel_square_remainder (a : F) :
    infinityValuation W (((genericX W - algebraMap F W.FunctionField a)⁻¹) ^ 2 -
      ((genericX W)⁻¹) ^ 2 - 2 * algebraMap F W.FunctionField a * ((genericX W)⁻¹) ^ 3) ≤
      WithZero.exp (-8) := by
  let A := (genericX W - algebraMap F W.FunctionField a)⁻¹
  let B := (genericX W)⁻¹
  have he : A ^ 2 - B ^ 2 - 2 * algebraMap F W.FunctionField a * B ^ 3 =
      (A - B) ^ 2 + (2 * B) * (A - B - algebraMap F W.FunctionField a * B ^ 2) := by ring
  rw [he]
  apply Valuation.map_add_le
  · exact infinityValuation_pow_le W (infinityValuation_inv_kernel_sub_inv W a) 2
  · have h2 : infinityValuation W (2 * B) ≤ WithZero.exp (-2) := by
      simpa only [map_ofNat] using infinityValuation_constant_mul_le W (2 : F)
        (infinityValuation_inv_genericX W).le
    have hr : infinityValuation W (A - B - algebraMap F W.FunctionField a * B ^ 2) ≤
        WithZero.exp (-6) := by
      simpa only [div_eq_mul_inv, ← inv_pow] using infinityValuation_inv_kernel_second_remainder W a
    exact infinityValuation_mul_le W h2 hr

/-- The cubed reciprocal correction has order at least eight. -/
theorem infinityValuation_inv_kernel_cube_sub (a : F) :
    infinityValuation W (((genericX W - algebraMap F W.FunctionField a)⁻¹) ^ 3 -
      ((genericX W)⁻¹) ^ 3) ≤ WithZero.exp (-8) := by
  let A := (genericX W - algebraMap F W.FunctionField a)⁻¹
  let B := (genericX W)⁻¹
  have he : A ^ 3 - B ^ 3 = (A - B) * (A ^ 2 + A * B + B ^ 2) := by ring
  rw [he]
  have hA : infinityValuation W A ≤ WithZero.exp (-2) := (infinityValuation_inv_kernel W a).le
  have hB : infinityValuation W B ≤ WithZero.exp (-2) := (infinityValuation_inv_genericX W).le
  exact infinityValuation_mul_le W (infinityValuation_inv_kernel_sub_inv W a)
    ((infinityValuation W).map_add_le
      ((infinityValuation W).map_add_le (infinityValuation_pow_le W hA 2)
        (infinityValuation_mul_le W hA hB)) (infinityValuation_pow_le W hB 2))

end Dubon2026.SourceEllipticFunctionField
