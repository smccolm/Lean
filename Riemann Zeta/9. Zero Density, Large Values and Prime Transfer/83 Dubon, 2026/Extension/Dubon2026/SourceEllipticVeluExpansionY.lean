import Dubon2026.SourceEllipticVeluYTermExpansion

/-! Summing the literal y-correction expansions gives precisely the T and W
coefficients used by the explicit quotient. This is the last finite-sum input
to the quotient error estimate on the DUB-17/18 odd quotient-map chain. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The actual finite y-sum has the indicated aggregate coefficients and fourth-order remainder. -/
theorem infinityValuation_genericVeluY_remainder (S : Finset (F × F)) :
    let c := algebraMap F W.toAffine.FunctionField
    let x := genericX W.toAffine
    let y := genericY W.toAffine
    infinityValuation W.toAffine (genericVeluY W S - y +
      c (veluTSum W S) * y / x ^ 2 + c (W.a₁ * veluTSum W S) / x +
      2 * c (veluWSum W S) * y / x ^ 3) ≤ WithZero.exp (-4) := by
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  let y := genericY W.toAffine
  have he : genericVeluY W S - y + c (veluTSum W S) * y / x ^ 2 +
      c (W.a₁ * veluTSum W S) / x + 2 * c (veluWSum W S) * y / x ^ 3 =
      -(∑ P ∈ S, ((c (veluU W P.1 P.2) * (2 * y + c W.a₁ * x + c W.a₃) / (x - c P.1) ^ 3 +
        c (veluT W P.1 P.2) * (c W.a₁ * (x - c P.1) + y - c P.2) / (x - c P.1) ^ 2 +
        c (W.a₁ * veluU W P.1 P.2 - veluGx W P.1 P.2 * veluGy W P.1 P.2) / (x - c P.1) ^ 2) -
        (c (veluT W P.1 P.2) * y / x ^ 2 + c (W.a₁ * veluT W P.1 P.2) / x +
          2 * c (veluW W P.1 P.2) * y / x ^ 3))) := by
    simp only [genericVeluY, veluTSum, veluWSum, map_sum, map_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    dsimp only [c, x, y]
    ring
  change infinityValuation W.toAffine _ ≤ _
  rw [he, Valuation.map_neg]
  exact Valuation.map_sum_le _ fun P _ => infinityValuation_veluY_term_remainder W P

end Dubon2026.SourceEllipticFunctionField
