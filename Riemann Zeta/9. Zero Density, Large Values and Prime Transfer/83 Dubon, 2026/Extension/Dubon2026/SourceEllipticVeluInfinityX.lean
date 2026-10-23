import Dubon2026.SourceEllipticInfinityBounds
import Dubon2026.SourceEllipticOddGenericCoordinate

/-! The literal finite Velu x-correction vanishes at infinity. The actual
coordinate denominator values give the bound directly, without an assumed
pole divisor. This supplies the double pole of the explicit quotient coordinate
needed to identify its polynomial quadratic relation on DUB-17/18. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable (S : Finset (F × F))

/-- The actual explicit Velu x-correction has a zero of order at least two at infinity. -/
theorem infinityValuation_genericVeluX_sub :
    infinityValuation W.toAffine (genericVeluX W S - genericX W.toAffine) ≤
      WithZero.exp (-2) := by
  unfold genericVeluX Xv
  rw [add_sub_cancel_left]
  apply Valuation.map_sum_le
  intro P _hP
  apply Valuation.map_add_le
  · have h := infinityValuation_div_kernel_power_le W.toAffine P.1 1
      (z := algebraMap F W.toAffine.FunctionField (veluT W P.1 P.2)) (m := 0)
      (by simpa only [WithZero.exp_zero] using infinityValuation_constant_le_one W.toAffine _)
    simpa only [pow_one] using h
  · have h := infinityValuation_div_kernel_power_le W.toAffine P.1 2
      (z := algebraMap F W.toAffine.FunctionField (veluU W P.1 P.2)) (m := 0)
      (by simpa only [WithZero.exp_zero] using infinityValuation_constant_le_one W.toAffine _)
    exact h.trans (WithZero.exp_le_exp.mpr (by norm_num))

/-- The literal Velu x-coordinate retains the actual generic coordinate's double pole. -/
theorem infinityValuation_genericVeluX :
    infinityValuation W.toAffine (genericVeluX W S) = WithZero.exp 2 := by
  have hlt : infinityValuation W.toAffine (genericVeluX W S - genericX W.toAffine) <
      infinityValuation W.toAffine (genericX W.toAffine) := by
    rw [infinityValuation_genericX]
    exact (infinityValuation_genericVeluX_sub W S).trans_lt
      (WithZero.exp_lt_exp.mpr (by norm_num))
  have h := Valuation.map_add_eq_of_lt_right (infinityValuation W.toAffine) hlt
  rw [sub_add_cancel, infinityValuation_genericX] at h
  exact h

end Dubon2026.SourceEllipticFunctionField
