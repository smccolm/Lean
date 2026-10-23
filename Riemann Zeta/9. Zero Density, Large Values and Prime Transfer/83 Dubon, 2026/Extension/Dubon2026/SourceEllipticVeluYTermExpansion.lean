import Dubon2026.SourceEllipticVeluExpansionX

/-! The three leading terms of one literal Velu y-correction. Only the
reciprocal expansions actually needed to force the quotient equation error
to vanish are used. This serves the odd quotient-map step on DUB-17/18. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- Each literal y-correction has the indicated three leading terms and a fourth-order remainder. -/
theorem infinityValuation_veluY_term_remainder (P : F × F) :
    let c := algebraMap F W.toAffine.FunctionField
    let x := genericX W.toAffine
    let y := genericY W.toAffine
    infinityValuation W.toAffine
      ((c (veluU W P.1 P.2) * (2 * y + c W.a₁ * x + c W.a₃) / (x - c P.1) ^ 3 +
        c (veluT W P.1 P.2) * (c W.a₁ * (x - c P.1) + y - c P.2) / (x - c P.1) ^ 2 +
        c (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) / (x - c P.1) ^ 2) -
        (c (veluT W P.1 P.2) * y / x ^ 2 + c (W.a₁ * veluT W P.1 P.2) / x +
          2 * c (veluW W P.1 P.2) * y / x ^ 3)) ≤ WithZero.exp (-4) := by
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  let A := (x - c P.1)⁻¹
  let B := x⁻¹
  have hx : x ≠ 0 := by simpa only [map_zero] using genericX_ne_constant W.toAffine 0
  have hd : x - c P.1 ≠ 0 := sub_ne_zero.mpr (genericX_ne_constant W.toAffine P.1)
  have he : (c (veluU W P.1 P.2) * (2 * y + c W.a₁ * x + c W.a₃) / (x - c P.1) ^ 3 +
      c (veluT W P.1 P.2) * (c W.a₁ * (x - c P.1) + y - c P.2) / (x - c P.1) ^ 2 +
      c (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) / (x - c P.1) ^ 2) -
      (c (veluT W P.1 P.2) * y / x ^ 2 + c (W.a₁ * veluT W P.1 P.2) / x +
        2 * c (veluW W P.1 P.2) * y / x ^ 3) =
      c (veluT W P.1 P.2) * (y * (A ^ 2 - B ^ 2 - 2 * c P.1 * B ^ 3)) +
      c (2 * veluU W P.1 P.2) * (y * (A ^ 3 - B ^ 3)) +
      c (W.a₁ * veluT W P.1 P.2) * (A - B) +
      c (W.a₁ * veluU W P.1 P.2) * (x * A ^ 3) +
      c (W.a₃ * veluU W P.1 P.2) * A ^ 3 -
      c (veluT W P.1 P.2 * P.2) * A ^ 2 +
      c (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) * A ^ 2 := by
    dsimp only [A, B]
    simp only [veluW, map_add, map_sub, map_mul, map_ofNat]
    field_simp
    ring
  change infinityValuation W.toAffine _ ≤ _
  rw [he]
  let v := infinityValuation W.toAffine
  have hA : v A ≤ WithZero.exp (-2) := (infinityValuation_inv_kernel W.toAffine P.1).le
  have hy : v y ≤ WithZero.exp 3 := (infinityValuation_genericY W.toAffine).le
  have hxy : v x ≤ WithZero.exp 2 := (infinityValuation_genericX W.toAffine).le
  have h64 : (WithZero.exp (-6) : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-4) :=
    WithZero.exp_le_exp.mpr (by norm_num)
  have h54 : (WithZero.exp (-5) : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-4) :=
    WithZero.exp_le_exp.mpr (by norm_num)
  have h1 := (infinityValuation_constant_mul_le W.toAffine (veluT W P.1 P.2)
    (infinityValuation_mul_le W.toAffine hy (infinityValuation_inv_kernel_square_remainder W.toAffine P.1))).trans h54
  have h2 := (infinityValuation_constant_mul_le W.toAffine (2 * veluU W P.1 P.2)
    (infinityValuation_mul_le W.toAffine hy (infinityValuation_inv_kernel_cube_sub W.toAffine P.1))).trans h54
  have h3 := infinityValuation_constant_mul_le W.toAffine (W.a₁ * veluT W P.1 P.2)
    (infinityValuation_inv_kernel_sub_inv W.toAffine P.1)
  have h4 := infinityValuation_constant_mul_le W.toAffine (W.a₁ * veluU W P.1 P.2)
    (infinityValuation_mul_le W.toAffine hxy (infinityValuation_pow_le W.toAffine hA 3))
  have h5 := (infinityValuation_constant_mul_le W.toAffine (W.a₃ * veluU W P.1 P.2)
    (infinityValuation_pow_le W.toAffine hA 3)).trans h64
  have h6 := infinityValuation_constant_mul_le W.toAffine (veluT W P.1 P.2 * P.2)
    (infinityValuation_pow_le W.toAffine hA 2)
  have h7 := infinityValuation_constant_mul_le W.toAffine
    (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2)
    (infinityValuation_pow_le W.toAffine hA 2)
  exact v.map_add_le (v.map_sub_le (v.map_add_le (v.map_add_le (v.map_add_le
    (v.map_add_le h1 h2) h3) h4) h5) h6) h7

end Dubon2026.SourceEllipticFunctionField
