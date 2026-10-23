import Dubon2026.SourceEllipticFunctionDegree
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Localization.NormTrace

/-! Norm-degree transport for the actual elliptic function field. Adapted from
TauCeti Affine/FunctionField/Norm.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba, retaining its AINTLIB provenance.
Native localization and the already proved quadratic field degree supply the
norm computation needed for the infinity valuation. That valuation identifies
the coefficients of the actual odd quotient relation on the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped RatFunc

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- The actual affine coordinate ring is finite over its polynomial x-ring. -/
theorem finite_polynomial_coordinateRing : Module.Finite F[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

/-- The actual polynomial x-ring embeds faithfully in the coordinate ring. -/
theorem faithful_polynomial_coordinateRing : FaithfulSMul F[X] W.CoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective F[X] W.CoordinateRing).mpr
    (AdjoinRoot.of.injective_of_degree_ne_zero (by simp [Affine.degree_polynomial]))

attribute [local instance] faithfulSMul_polynomial finiteDimensional_functionField
  finite_polynomial_coordinateRing faithful_polynomial_coordinateRing

/-- The degree of the actual field norm of a coordinate-ring element is its polynomial norm degree. -/
theorem intDegree_norm_coordinateRing (u : W.CoordinateRing) :
    (Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u)).intDegree =
      (Algebra.norm F[X] u).natDegree := by
  rw [Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing),
    RatFunc.intDegree_polynomial]

/-- A polynomial coordinate has actual field norm equal to its square. -/
theorem norm_polynomial_coordinate (d : F[X]) :
    Algebra.norm (RatFunc F) (algebraMap F[X] W.FunctionField d) =
      (algebraMap F[X] (RatFunc F) d) ^ 2 := by
  rw [IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    Algebra.norm_algebraMap, finrank_functionField W (RatFunc F)]

/-- A common polynomial denominator subtracts twice its degree from the actual norm degree. -/
theorem intDegree_norm_of_mul_eq {f : W.FunctionField} (hf : f ≠ 0)
    {u : W.CoordinateRing} {d : F[X]} (hd : d ≠ 0)
    (h : f * algebraMap F[X] W.FunctionField d = algebraMap W.CoordinateRing W.FunctionField u) :
    (Algebra.norm (RatFunc F) f).intDegree =
      (Algebra.norm F[X] u).natDegree - 2 * d.natDegree := by
  have hNf : Algebra.norm (RatFunc F) f ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := RatFunc F)).mpr hf
  have hdR : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hnorm := congrArg (Algebra.norm (RatFunc F)) h
  rw [map_mul, norm_polynomial_coordinate] at hnorm
  have he := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_mul hNf (pow_ne_zero _ hdR), ← map_pow,
    RatFunc.intDegree_polynomial, natDegree_pow, intDegree_norm_coordinateRing] at he
  omega

end Dubon2026.SourceEllipticFunctionField
