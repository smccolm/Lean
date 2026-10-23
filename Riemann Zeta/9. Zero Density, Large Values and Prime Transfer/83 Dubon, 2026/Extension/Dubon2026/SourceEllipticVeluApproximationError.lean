import Dubon2026.SourceEllipticVeluApproximation
import Dubon2026.SourceEllipticVeluApproximationAlgebra

/-! The explicit quotient equation evaluated on the proved truncated
coordinates has value at most exp(-1). The exact numerator identity uses the
original Weierstrass equation, with all coefficients in the actual base field.
This is the main cancellation needed to discharge the odd quotient equation
on the DUB-17/18 quotient-map dependency. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The actual explicit quotient equation evaluated on the proved truncations. -/
noncomputable def veluApproxError : W.toAffine.FunctionField :=
  let c := algebraMap F W.toAffine.FunctionField
  let X := veluApproxX W S
  let Y := veluApproxY W S
  Y ^ 2 + c W.a₁ * X * Y + c W.a₃ * Y -
    (X ^ 3 + c W.a₂ * X ^ 2 + c (veluQuotient W S).a₄ * X + c (veluQuotient W S).a₆)

/-- Cancellation of the explicit quotient coefficients leaves an error vanishing at infinity. -/
theorem infinityValuation_veluApproxError :
    infinityValuation W.toAffine (veluApproxError W S) ≤ WithZero.exp (-1) := by
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  let t := veluTSum W S
  let w := veluWSum W S
  let n5 := 3 * t ^ 2 - 6 * W.a₂ * w - 3 * W.a₄ * t - W.a₁ * W.a₃ * t
  let n4 := 3 * t * w - 5 * W.a₄ * w - 2 * W.a₆ * t
  let n3 := w ^ 2 + (2 * W.a₂ - W.a₁ ^ 2) * t * w + W.a₄ * t ^ 2 - 4 * W.a₆ * w - t ^ 3
  let n2 := 3 * W.a₂ * w ^ 2 + 4 * W.a₄ * t * w + W.a₆ * t ^ 2 - 3 * t ^ 2 * w
  let n1 := 4 * W.a₄ * w ^ 2 + 4 * W.a₆ * t * w - 3 * t * w ^ 2
  let n0 := 4 * W.a₆ * w ^ 2 - w ^ 3
  have hx : x ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W.toAffine 0
  have hcurve := (Affine.equation_iff (W := (W.toAffine⁄W.toAffine.FunctionField).toAffine)
    x y).mp (equation_genericX_genericY W.toAffine)
  change y ^ 2 + c W.a₁ * x * y + c W.a₃ * y = x ^ 3 + c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆ at hcurve
  have hid := velu_approximation_error_identity (c W.a₁) (c W.a₂) (c W.a₃) (c W.a₄) (c W.a₆)
    (c t) (c w) x y hx hcurve
  have he : veluApproxError W S =
      (c n5 * x ^ 5 + c n4 * x ^ 4 + c n3 * x ^ 3 + c n2 * x ^ 2 + c n1 * x + c n0 +
        (x ^ 3 - c t * x - c (2 * w)) * (c (W.a₃ * t + 3 * W.a₁ * w) * x + c (2 * W.a₃ * w)) * y) / x ^ 6 := by
    unfold veluApproxError
    rw [veluApproxX_eq_ratio, veluApproxY_eq_ratio, veluQuotient_a₄, veluQuotient_a₆]
    simpa only [n5, n4, n3, n2, n1, n0, WeierstrassCurve.b₂, map_add, map_sub, map_mul,
      map_pow, map_ofNat] using hid
  rw [he]
  let v := infinityValuation W.toAffine
  have hX : v x ≤ WithZero.exp 2 := (infinityValuation_genericX W.toAffine).le
  have hY : v y ≤ WithZero.exp 3 := (infinityValuation_genericY W.toAffine).le
  have hc (a : F) : v (c a) ≤ WithZero.exp 0 := by
    simpa only [WithZero.exp_zero] using infinityValuation_constant_le_one W.toAffine a
  have hexp : ∀ m n : ℤ, m ≤ n →
      (WithZero.exp m : WithZero (Multiplicative ℤ)) ≤ WithZero.exp n :=
    fun _ _ h => WithZero.exp_le_exp.mpr h
  have hmon (a : F) (k : ℕ) (hk : (k : ℤ) * 2 ≤ 11) :
      v (c a * x ^ k) ≤ WithZero.exp 11 :=
    (infinityValuation_constant_mul_le W.toAffine a (infinityValuation_pow_le W.toAffine hX k)).trans (hexp _ _ hk)
  have hN : v (c n5 * x ^ 5 + c n4 * x ^ 4 + c n3 * x ^ 3 + c n2 * x ^ 2 + c n1 * x + c n0) ≤ WithZero.exp 11 := by
    refine v.map_add_le (v.map_add_le (v.map_add_le (v.map_add_le (v.map_add_le
      (hmon n5 5 (by norm_num)) (hmon n4 4 (by norm_num))) (hmon n3 3 (by norm_num)))
      (hmon n2 2 (by norm_num))) ?_) ((hc n0).trans (hexp _ _ (by norm_num)))
    simpa only [pow_one] using hmon n1 1 (by norm_num)
  have hA : v (x ^ 3 - c t * x - c (2 * w)) ≤ WithZero.exp 6 :=
    v.map_sub_le (v.map_sub_le (infinityValuation_pow_le W.toAffine hX 3)
      ((infinityValuation_constant_mul_le W.toAffine t hX).trans (hexp _ _ (by norm_num))))
      ((hc _).trans (hexp _ _ (by norm_num)))
  have hD : v (c (W.a₃ * t + 3 * W.a₁ * w) * x + c (2 * W.a₃ * w)) ≤ WithZero.exp 2 :=
    v.map_add_le (infinityValuation_constant_mul_le W.toAffine _ hX)
      ((hc _).trans (hexp _ _ (by norm_num)))
  have hM := infinityValuation_mul_le W.toAffine (infinityValuation_mul_le W.toAffine hA hD) hY
  exact infinityValuation_div_genericX_power_le W.toAffine (v.map_add_le hN hM) 6

end Dubon2026.SourceEllipticFunctionField
