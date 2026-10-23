import Dubon2026.SourceEllipticVeluExpansionY

/-! Truncating the actual Velu coordinate expansions with rigorously bounded
remainders. These particular approximations suffice to prove that the literal
quotient equation error vanishes at infinity, on the DUB-17/18 dependency. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The actual two-term truncation of the finite x-correction. -/
noncomputable def veluApproxX : W.toAffine.FunctionField :=
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  x + c (veluTSum W S) / x + c (veluWSum W S) / x ^ 2

/-- The actual three-term truncation of the finite y-correction. -/
noncomputable def veluApproxY : W.toAffine.FunctionField :=
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  y - c (veluTSum W S) * y / x ^ 2 - c (W.a₁ * veluTSum W S) / x -
    2 * c (veluWSum W S) * y / x ^ 3

/-- The x-approximation differs from the actual coordinate by order at least six. -/
theorem infinityValuation_genericVeluX_sub_approx :
    infinityValuation W.toAffine (genericVeluX W S - veluApproxX W S) ≤ WithZero.exp (-6) := by
  convert infinityValuation_genericVeluX_remainder W S using 1
  congr 1
  dsimp only [veluApproxX]
  ring

/-- The y-approximation differs from the actual coordinate by order at least four. -/
theorem infinityValuation_genericVeluY_sub_approx :
    infinityValuation W.toAffine (genericVeluY W S - veluApproxY W S) ≤ WithZero.exp (-4) := by
  convert infinityValuation_genericVeluY_remainder W S using 1
  congr 1
  dsimp only [veluApproxY]
  ring

/-- The truncated x-coordinate has pole order at most two. -/
theorem infinityValuation_veluApproxX :
    infinityValuation W.toAffine (veluApproxX W S) ≤ WithZero.exp 2 := by
  have h := (infinityValuation W.toAffine).map_sub_le (infinityValuation_genericVeluX W S).le
    ((infinityValuation_genericVeluX_sub_approx W S).trans (WithZero.exp_le_exp.mpr (by norm_num : (-6 : ℤ) ≤ 2)))
  simpa only [sub_sub_cancel] using h

/-- The truncated y-coordinate has pole order at most three. -/
theorem infinityValuation_veluApproxY :
    infinityValuation W.toAffine (veluApproxY W S) ≤ WithZero.exp 3 := by
  have h := (infinityValuation W.toAffine).map_sub_le (infinityValuation_genericVeluY W S).le
    ((infinityValuation_genericVeluY_sub_approx W S).trans (WithZero.exp_le_exp.mpr (by norm_num : (-4 : ℤ) ≤ 3)))
  simpa only [sub_sub_cancel] using h

/-- The truncated x-coordinate has its exact polynomial numerator. -/
theorem veluApproxX_eq_ratio : veluApproxX W S =
    (genericX W.toAffine ^ 3 + algebraMap F W.toAffine.FunctionField (veluTSum W S) * genericX W.toAffine +
      algebraMap F W.toAffine.FunctionField (veluWSum W S)) / genericX W.toAffine ^ 2 := by
  have hx : genericX W.toAffine ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W.toAffine 0
  unfold veluApproxX
  field_simp

/-- The truncated y-coordinate has its exact polynomial numerator. -/
theorem veluApproxY_eq_ratio : veluApproxY W S =
    ((genericX W.toAffine ^ 3 - algebraMap F W.toAffine.FunctionField (veluTSum W S) * genericX W.toAffine -
      2 * algebraMap F W.toAffine.FunctionField (veluWSum W S)) * genericY W.toAffine -
      algebraMap F W.toAffine.FunctionField W.a₁ * algebraMap F W.toAffine.FunctionField (veluTSum W S) *
        genericX W.toAffine ^ 2) / genericX W.toAffine ^ 3 := by
  have hx : genericX W.toAffine ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W.toAffine 0
  dsimp only [veluApproxY]
  rw [map_mul]
  field_simp
  ring

end Dubon2026.SourceEllipticFunctionField
