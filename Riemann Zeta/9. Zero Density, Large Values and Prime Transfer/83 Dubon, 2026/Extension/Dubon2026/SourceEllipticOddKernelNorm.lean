import Dubon2026.SourceEllipticOddPointNormFormula

/-! Points on the actual kernel denominator extend to the unit ideal in
the common ring, so the actual additive norm map sends them to infinity.
Together with the proved affine formula, this identifies the kernel by the
denominator polynomial. SourceEllipticOddKernelGeometry identifies those
roots with the cyclic subgroup (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}
variable {x y : F}

/-- At a root of the kernel polynomial the source point ideal extends to the unit ideal. -/
theorem map_XYIdeal_odd_eq_top (h : W.toAffine.Equation x y)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x = 0) :
    (CoordinateRing.XYIdeal W.toAffine x (C y)).map (oddSourceToIntermediate W hQ) = ⊤ := by
  letI := oddIntermediateSourceAlgebra W hQ
  letI := isLocalization_oddIntermediateRing W hQ
  let D := kernelCoordinate W (oddOrderSummingSet W Q n)
  have hm : D ∈ CoordinateRing.XYIdeal W.toAffine x (C y) := by
    rw [← ker_evalAlgHom_eq_XYIdeal h]
    change evalAlgHom (W := W.toAffine) (A := F) h D = 0
    rw [eval_kernelCoordinate, hd]
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hm)
  exact IsLocalization.map_units (oddIntermediateRing W hQ)
    (⟨D, ⟨1, pow_one D⟩⟩ : Submonoid.powers D)

/-- The actual additive norm map sends every root of the kernel denominator to infinity. -/
theorem oddPointNorm_some_eq_zero_of_kernel (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x = 0) :
    oddPointNorm W hQ (Point.some x y h) = 0 := by
  letI := isDedekindDomain_of_isAlgClosed' (W := W.toAffine)
  letI := isDedekindDomain_oddCoordinate W hQ
  letI := isDedekindDomain_oddIntermediateRing W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := moduleFinite_oddIntermediateRing W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  apply (oddPointNorm_eq_iff W hQ _ _).mpr
  rw [Point.toClass_zero]
  apply Additive.toMul.injective
  change oddClassNorm W hQ (Additive.toMul (Point.some x y h).toClass) = 1
  rw [toMul_toClass_some_eq_mk0]
  change extendedClassNorm (R := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing)
    (oddSourceToIntermediate W hQ) (oddSourceToIntermediate_injective W hQ)
    (ClassGroup.mk0 (nonzeroPointIdeal W.toAffine x y)) = 1
  rw [extendedClassNorm_mk0]
  have hi : extendedIdeal (oddSourceToIntermediate W hQ) (oddSourceToIntermediate_injective W hQ)
      (nonzeroPointIdeal W.toAffine x y) = 1 := by
    apply Subtype.ext
    rw [extendedIdeal_coe, nonzeroPointIdeal_coe]
    simpa only [OneMemClass.coe_one, Ideal.one_eq_top] using map_XYIdeal_odd_eq_top W h.left hQ hd
  rw [hi, map_one, map_one]

/-- The exact affine kernel of the actual additive norm map is the zero set of the actual kernel polynomial. -/
theorem oddPointNorm_some_eq_zero_iff (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf Q = 2 * n + 1) :
    oddPointNorm W hQ (Point.some x y h) = 0 ↔
      (hP (oddOrderSummingSet W Q n) Prod.fst).eval x = 0 := by
  constructor
  · intro hz
    by_contra hd
    exact oddPointNorm_some_ne_zero W h hQ hd hz
  · exact oddPointNorm_some_eq_zero_of_kernel W h hQ

end Dubon2026.SourceEllipticFunctionField
