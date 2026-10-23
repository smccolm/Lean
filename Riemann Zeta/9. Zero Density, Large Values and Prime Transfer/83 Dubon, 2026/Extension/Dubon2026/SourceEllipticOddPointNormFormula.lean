import Dubon2026.SourceEllipticPointIdealClass

/-! The actual additive odd quotient point norm agrees with the literal
finite Velu formulas at every affine point outside the kernel denominator.
The proof consumes the actual extended ideal norm, not an independently
chosen homomorphism. This closes the affine-formula comparison required
before the exact cyclic kernel on the DUB-17/18 dependency chain. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
variable {x y : F}

/-- The literal odd quotient coordinates are nonsingular at each actual affine point off the kernel. -/
theorem odd_veluAffine_nonsingular (h : W.toAffine.Equation x y)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.Nonsingular
      (veluAffineX W (oddOrderSummingSet W Q n) x)
      (veluAffineY W (oddOrderSummingSet W Q n) x y) := by
  letI := odd_quotient_isElliptic W Q hQ
  exact equation_iff_nonsingular.mp (odd_veluAffine_equation W h hQ hd)

variable [IsAlgClosed F]

/-- The actual additive norm map has the literal affine Velu coordinates outside the kernel. -/
theorem oddPointNorm_some (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    oddPointNorm W hQ (Point.some x y h) =
      Point.some (veluAffineX W (oddOrderSummingSet W Q n) x)
        (veluAffineY W (oddOrderSummingSet W Q n) x y)
        (odd_veluAffine_nonsingular W h.left hQ hd) := by
  letI := isDedekindDomain_of_isAlgClosed' (W := W.toAffine)
  letI := isDedekindDomain_oddCoordinate W hQ
  letI := isDedekindDomain_oddIntermediateRing W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := moduleFinite_oddIntermediateRing W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  apply (oddPointNorm_eq_iff W hQ _ _).mpr
  apply Additive.toMul.injective
  change oddClassNorm W hQ (Additive.toMul (Point.some x y h).toClass) = _
  rw [toMul_toClass_some_eq_mk0, toMul_toClass_some_eq_mk0]
  change extendedClassNorm (R := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing)
    (oddSourceToIntermediate W hQ) (oddSourceToIntermediate_injective W hQ)
    (ClassGroup.mk0 (nonzeroPointIdeal W.toAffine x y)) = _
  rw [extendedClassNorm_mk0]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  rw [coe_idealRelNorm, extendedIdeal_coe, nonzeroPointIdeal_coe, nonzeroPointIdeal_coe]
  exact relNorm_map_XYIdeal_odd W h.left hQ hd

/-- An affine point away from the kernel has a nonzero image under the actual additive norm map. -/
theorem oddPointNorm_some_ne_zero (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    oddPointNorm W hQ (Point.some x y h) ≠ 0 := by
  rw [oddPointNorm_some W h hQ hd]
  exact Point.some_ne_zero _

end Dubon2026.SourceEllipticFunctionField
