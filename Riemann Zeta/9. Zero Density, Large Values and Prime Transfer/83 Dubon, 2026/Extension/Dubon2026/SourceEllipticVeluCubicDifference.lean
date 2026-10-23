import Dubon2026.SourceEllipticVeluInfinityY

/-! The leading cubic terms of the actual Velu coordinates cancel at infinity.
Adapted from TauCeti Isogeny/Velu/Equation.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba. The actual original Weierstrass
equation and proved correction bounds force a pole of order at most five.
This identifies the leading cubic coefficient in the odd quotient relation. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The square-minus-cube of the actual Velu coordinates has pole order at most five. -/
theorem infinityValuation_velu_square_sub_cube_le :
    infinityValuation W.toAffine (genericVeluY W S ^ 2 - genericVeluX W S ^ 3) ≤
      WithZero.exp 5 := by
  let v := infinityValuation W.toAffine
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  let c := algebraMap F W.toAffine.FunctionField
  have hx : v x = WithZero.exp 2 := infinityValuation_genericX W.toAffine
  have hy : v y = WithZero.exp 3 := infinityValuation_genericY W.toAffine
  have hX := infinityValuation_genericVeluX W S
  have hY := infinityValuation_genericVeluY W S
  have hc : ∀ a : F, v (c a) ≤ 1 := infinityValuation_constant_le_one W.toAffine
  have hexp : ∀ m n : ℤ, m ≤ n →
      (WithZero.exp m : WithZero (Multiplicative ℤ)) ≤ WithZero.exp n :=
    fun _ _ h => WithZero.exp_le_exp.mpr h
  have hXx : v (genericVeluX W S - x) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact (infinityValuation_genericVeluX_sub W S).trans (hexp _ _ (by norm_num))
  have hYy : v (genericVeluY W S - y) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact (infinityValuation_genericVeluY_sub W S).trans (hexp _ _ (by norm_num))
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 5 := by
    rw [← WithZero.exp_zero]
    exact hexp _ _ (by norm_num)
  have heq := (Affine.equation_iff (W := (W.toAffine⁄W.toAffine.FunctionField).toAffine)
    x y).mp (equation_genericX_genericY W.toAffine)
  have hdecomp : genericVeluY W S ^ 2 - genericVeluX W S ^ 3 =
      (genericVeluY W S - y) * (genericVeluY W S + y) -
        (genericVeluX W S - x) * (genericVeluX W S ^ 2 + genericVeluX W S * x + x ^ 2) +
        (c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆ - c W.a₁ * x * y - c W.a₃ * y) := by
    linear_combination (norm := ring!) heq
  rw [hdecomp]
  refine v.map_add_le (v.map_sub_le ?_ ?_) ?_
  · rw [map_mul]
    refine (mul_le_of_le_one_left' hYy).trans (v.map_add_le ?_ ?_)
    · rw [hY]; exact hexp _ _ (by norm_num)
    · rw [hy]; exact hexp _ _ (by norm_num)
  · rw [map_mul]
    refine (mul_le_of_le_one_left' hXx).trans (v.map_add_le (v.map_add_le ?_ ?_) ?_)
    · rw [map_pow, hX, ← WithZero.exp_nsmul]; exact hexp _ _ (by norm_num)
    · rw [map_mul, hX, hx, ← WithZero.exp_add]; exact hexp _ _ (by norm_num)
    · rw [map_pow, hx, ← WithZero.exp_nsmul]; exact hexp _ _ (by norm_num)
  · refine v.map_sub_le (v.map_sub_le (v.map_add_le (v.map_add_le ?_ ?_) ?_) ?_) ?_
    · rw [map_mul, map_pow, hx, ← WithZero.exp_nsmul]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · rw [map_mul, hx]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · exact (hc _).trans h1
    · rw [map_mul, map_mul, hx, hy, mul_assoc, ← WithZero.exp_add]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))
    · rw [map_mul, hy]
      exact (mul_le_of_le_one_left' (hc _)).trans (hexp _ _ (by norm_num))

end Dubon2026.SourceEllipticFunctionField
