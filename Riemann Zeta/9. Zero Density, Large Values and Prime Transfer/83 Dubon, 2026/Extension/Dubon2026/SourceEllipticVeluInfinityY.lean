import Dubon2026.SourceEllipticVeluInfinityX
import Dubon2026.SourceEllipticOddGenericY

/-! The literal finite Velu y-correction vanishes at infinity. Its three
explicit summands are bounded using the already proved actual denominator
values. This gives the triple pole used to identify the polynomial quadratic
relation coefficients of the explicit odd quotient on the DUB-17/18 chain. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable (S : Finset (F × F))

/-- The actual explicit Velu y-correction has a zero of order at least one at infinity. -/
theorem infinityValuation_genericVeluY_sub :
    infinityValuation W.toAffine (genericVeluY W S - genericY W.toAffine) ≤
      WithZero.exp (-1) := by
  let v := infinityValuation W.toAffine
  have hc := infinityValuation_constant_le_one W.toAffine
  have h03 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 3 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have h23 : (WithZero.exp 2 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 3 :=
    WithZero.exp_le_exp.mpr (by norm_num)
  have hy : v (genericY W.toAffine) ≤ WithZero.exp 3 :=
    (infinityValuation_genericY W.toAffine).le
  have hx : v (genericX W.toAffine) ≤ WithZero.exp 2 :=
    (infinityValuation_genericX W.toAffine).le
  have h2y : v (2 * genericY W.toAffine) ≤ WithZero.exp 3 := by
    simpa only [map_ofNat] using infinityValuation_constant_mul_le W.toAffine (2 : F) hy
  unfold genericVeluY
  rw [show ∀ a b : W.toAffine.FunctionField, (a - b) - a = -b from fun a b => by ring,
    Valuation.map_neg]
  apply Valuation.map_sum_le
  intro P _hP
  apply Valuation.map_add_le
  · apply Valuation.map_add_le
    · have hn : v (2 * genericY W.toAffine +
          algebraMap F W.toAffine.FunctionField W.a₁ * genericX W.toAffine +
          algebraMap F W.toAffine.FunctionField W.a₃) ≤ WithZero.exp 3 :=
        v.map_add_le (v.map_add_le h2y
          ((infinityValuation_constant_mul_le W.toAffine W.a₁ hx).trans h23)) ((hc _).trans h03)
      have h := infinityValuation_div_kernel_power_le W.toAffine P.1 3
        (infinityValuation_constant_mul_le W.toAffine (veluU W P.1 P.2) hn)
      exact h.trans (WithZero.exp_le_exp.mpr (by norm_num))
    · have hd : v (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1) ≤
          WithZero.exp 2 := (infinityValuation_genericX_sub_constant W.toAffine P.1).le
      have hn : v (algebraMap F W.toAffine.FunctionField W.a₁ *
          (genericX W.toAffine - algebraMap F W.toAffine.FunctionField P.1) +
          genericY W.toAffine - algebraMap F W.toAffine.FunctionField P.2) ≤ WithZero.exp 3 :=
        v.map_sub_le (v.map_add_le
          ((infinityValuation_constant_mul_le W.toAffine W.a₁ hd).trans h23) hy) ((hc _).trans h03)
      exact infinityValuation_div_kernel_power_le W.toAffine P.1 2
        (infinityValuation_constant_mul_le W.toAffine (veluT W P.1 P.2) hn)
  · have h := infinityValuation_div_kernel_power_le W.toAffine P.1 2
      (z := algebraMap F W.toAffine.FunctionField
        (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2)) (m := 0)
      (by simpa only [WithZero.exp_zero] using hc _)
    exact h.trans (WithZero.exp_le_exp.mpr (by norm_num))

/-- The literal Velu y-coordinate retains the actual generic coordinate's triple pole. -/
theorem infinityValuation_genericVeluY :
    infinityValuation W.toAffine (genericVeluY W S) = WithZero.exp 3 := by
  have hlt : infinityValuation W.toAffine (genericVeluY W S - genericY W.toAffine) <
      infinityValuation W.toAffine (genericY W.toAffine) := by
    rw [infinityValuation_genericY]
    exact (infinityValuation_genericVeluY_sub W S).trans_lt
      (WithZero.exp_lt_exp.mpr (by norm_num))
  have h := Valuation.map_add_eq_of_lt_right (infinityValuation W.toAffine) hlt
  rw [sub_add_cancel, infinityValuation_genericY] at h
  exact h

end Dubon2026.SourceEllipticFunctionField
