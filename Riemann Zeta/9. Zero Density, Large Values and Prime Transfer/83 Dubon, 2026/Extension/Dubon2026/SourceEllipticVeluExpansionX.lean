import Dubon2026.SourceEllipticReciprocalPowers
import Dubon2026.SourceEllipticVeluInfinityY

/-! The first two coefficients of the literal finite Velu x-correction.
The reciprocal remainder estimates give a remainder of order at least six.
This is used to prove the explicit odd quotient equation on the DUB-17/18
quotient-map dependency, without separately classifying its five coefficients. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The exact two-term expansion of each x-correction has a sixth-order remainder. -/
theorem infinityValuation_veluX_term_remainder (P : F × F) :
    let c := algebraMap F W.toAffine.FunctionField
    let x := genericX W.toAffine
    infinityValuation W.toAffine
      ((c (veluT W P.1 P.2) / (x - c P.1) + c (veluU W P.1 P.2) / (x - c P.1) ^ 2) -
        (c (veluT W P.1 P.2) / x + c (veluW W P.1 P.2) / x ^ 2)) ≤ WithZero.exp (-6) := by
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  have he : (c (veluT W P.1 P.2) / (x - c P.1) + c (veluU W P.1 P.2) / (x - c P.1) ^ 2) -
      (c (veluT W P.1 P.2) / x + c (veluW W P.1 P.2) / x ^ 2) =
      c (veluT W P.1 P.2) * ((x - c P.1)⁻¹ - x⁻¹ - c P.1 / x ^ 2) +
      c (veluU W P.1 P.2) * (((x - c P.1)⁻¹) ^ 2 - (x⁻¹) ^ 2) := by
    simp only [veluW, map_add, map_mul, div_eq_mul_inv, ← inv_pow]
    ring
  change infinityValuation W.toAffine _ ≤ _
  rw [he]
  exact (infinityValuation W.toAffine).map_add_le
    (infinityValuation_constant_mul_le W.toAffine _ (infinityValuation_inv_kernel_second_remainder W.toAffine P.1))
    (infinityValuation_constant_mul_le W.toAffine _ (infinityValuation_inv_kernel_square_sub W.toAffine P.1))

/-- The literal x-coordinate has the actual aggregate T and W coefficients at infinity. -/
theorem infinityValuation_genericVeluX_remainder (S : Finset (F × F)) :
    let c := algebraMap F W.toAffine.FunctionField
    let x := genericX W.toAffine
    infinityValuation W.toAffine (genericVeluX W S - x -
      c (veluTSum W S) / x - c (veluWSum W S) / x ^ 2) ≤ WithZero.exp (-6) := by
  let c := algebraMap F W.toAffine.FunctionField
  let x := genericX W.toAffine
  have he : genericVeluX W S - x - c (veluTSum W S) / x - c (veluWSum W S) / x ^ 2 =
      ∑ P ∈ S, ((c (veluT W P.1 P.2) / (x - c P.1) + c (veluU W P.1 P.2) / (x - c P.1) ^ 2) -
        (c (veluT W P.1 P.2) / x + c (veluW W P.1 P.2) / x ^ 2)) := by
    simp only [genericVeluX, Xv, veluTSum, veluWSum, map_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_div]
    dsimp only [c, x]
    ring
  change infinityValuation W.toAffine _ ≤ _
  rw [he]
  exact Valuation.map_sum_le _ fun P _ => infinityValuation_veluX_term_remainder W P

end Dubon2026.SourceEllipticFunctionField
