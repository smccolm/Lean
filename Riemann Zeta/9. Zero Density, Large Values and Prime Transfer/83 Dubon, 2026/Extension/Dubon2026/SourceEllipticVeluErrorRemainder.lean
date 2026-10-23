import Dubon2026.SourceEllipticVeluApproximationError

/-! Transferring the proved equation-error estimate from the truncated
coordinates to the literal finite Velu coordinates. Every difference term
vanishes at the actual infinity valuation; no smoothness or equation of the
quotient is assumed. This discharges the error estimate needed on DUB-17/18. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The error changes by a function vanishing at infinity when passing to the proved truncations. -/
theorem infinityValuation_velu_error_sub_approx :
    infinityValuation W.toAffine (veluEquationError W S - veluApproxError W S) ≤ WithZero.exp (-1) := by
  let c := algebraMap F W.toAffine.FunctionField
  let X := genericVeluX W S
  let Y := genericVeluY W S
  let U := veluApproxX W S
  let V := veluApproxY W S
  let v := infinityValuation W.toAffine
  have he : veluEquationError W S - veluApproxError W S =
      (Y - V) * (Y + V) + c W.a₁ * ((X - U) * Y + U * (Y - V)) + c W.a₃ * (Y - V) -
      ((X - U) * (X ^ 2 + X * U + U ^ 2) + c W.a₂ * ((X - U) * (X + U)) +
        c (veluQuotient W S).a₄ * (X - U)) := by
    dsimp only [veluEquationError, veluApproxError, c, X, Y, U, V]
    ring
  rw [he]
  have hX : v X ≤ WithZero.exp 2 := (infinityValuation_genericVeluX W S).le
  have hY : v Y ≤ WithZero.exp 3 := (infinityValuation_genericVeluY W S).le
  have hU : v U ≤ WithZero.exp 2 := infinityValuation_veluApproxX W S
  have hV : v V ≤ WithZero.exp 3 := infinityValuation_veluApproxY W S
  have hdX : v (X - U) ≤ WithZero.exp (-6) := infinityValuation_genericVeluX_sub_approx W S
  have hdY : v (Y - V) ≤ WithZero.exp (-4) := infinityValuation_genericVeluY_sub_approx W S
  have hexp : ∀ m n : ℤ, m ≤ n →
      (WithZero.exp m : WithZero (Multiplicative ℤ)) ≤ WithZero.exp n :=
    fun _ _ h => WithZero.exp_le_exp.mpr h
  have h1 : v ((Y - V) * (Y + V)) ≤ WithZero.exp (-1) :=
    infinityValuation_mul_le W.toAffine hdY (v.map_add_le hY hV)
  have h2 : v (c W.a₁ * ((X - U) * Y + U * (Y - V))) ≤ WithZero.exp (-1) :=
    infinityValuation_constant_mul_le W.toAffine _ (v.map_add_le
      ((infinityValuation_mul_le W.toAffine hdX hY).trans (hexp _ _ (by norm_num)))
      ((infinityValuation_mul_le W.toAffine hU hdY).trans (hexp _ _ (by norm_num))))
  have h3 : v (c W.a₃ * (Y - V)) ≤ WithZero.exp (-1) :=
    (infinityValuation_constant_mul_le W.toAffine _ hdY).trans (hexp _ _ (by norm_num))
  have hcub : v (X ^ 2 + X * U + U ^ 2) ≤ WithZero.exp 4 :=
    v.map_add_le (v.map_add_le (infinityValuation_pow_le W.toAffine hX 2)
      (infinityValuation_mul_le W.toAffine hX hU)) (infinityValuation_pow_le W.toAffine hU 2)
  have h4 : v ((X - U) * (X ^ 2 + X * U + U ^ 2)) ≤ WithZero.exp (-1) :=
    (infinityValuation_mul_le W.toAffine hdX hcub).trans (hexp _ _ (by norm_num))
  have h5 : v (c W.a₂ * ((X - U) * (X + U))) ≤ WithZero.exp (-1) :=
    (infinityValuation_constant_mul_le W.toAffine _
      (infinityValuation_mul_le W.toAffine hdX (v.map_add_le hX hU))).trans (hexp _ _ (by norm_num))
  have h6 : v (c (veluQuotient W S).a₄ * (X - U)) ≤ WithZero.exp (-1) :=
    (infinityValuation_constant_mul_le W.toAffine _ hdX).trans (hexp _ _ (by norm_num))
  exact v.map_sub_le (v.map_add_le (v.map_add_le h1 h2) h3) (v.map_add_le (v.map_add_le h4 h5) h6)

/-- The actual explicit finite-formula quotient error vanishes at infinity. -/
theorem infinityValuation_veluEquationError :
    infinityValuation W.toAffine (veluEquationError W S) ≤ WithZero.exp (-1) := by
  have h := (infinityValuation W.toAffine).map_add_le (infinityValuation_velu_error_sub_approx W S)
    (infinityValuation_veluApproxError W S)
  simpa only [sub_add_cancel] using h

end Dubon2026.SourceEllipticFunctionField
