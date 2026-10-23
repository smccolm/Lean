import Dubon2026.SourceEllipticOddIntermediateLocalization

/-! Evaluation on the actual kernel localization at an affine point where
the kernel polynomial is nonzero, using the native localization lift. The
subsequent point-ideal and relative-norm comparisons use this map to prove
the odd quotient formula and cyclic kernel on DUB-17/18, without a separate
point-place classification. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))
variable {x y : F} (h : W.toAffine.Equation x y)

/-- Evaluation of the actual kernel coordinate is evaluation of the actual kernel polynomial. -/
theorem eval_kernelCoordinate : evalAlgHom (W := W.toAffine) (A := F) h (kernelCoordinate W S) = (hP S Prod.fst).eval x := by
  have he : (evalAlgHom (W := W.toAffine) (A := F) h).comp (IsScalarTower.toAlgHom F F[X] W.toAffine.CoordinateRing) =
      aeval x := Polynomial.algHom_ext (by
        rw [aeval_X]
        exact evalAlgHom_of_X (W := W.toAffine) (A := F) h)
  change ((evalAlgHom (W := W.toAffine) (A := F) h).comp (IsScalarTower.toAlgHom F F[X] W.toAffine.CoordinateRing)) (hP S Prod.fst) = _
  rw [he]
  rfl

/-- Evaluation sends every inverted kernel-denominator power to a unit. -/
theorem eval_kernel_powers_isUnit (hd : (hP S Prod.fst).eval x ≠ 0)
    (d : Submonoid.powers (kernelCoordinate W S)) : IsUnit (evalAlgHom (W := W.toAffine) (A := F) h d) := by
  obtain ⟨k, hk⟩ := d.property
  rw [← hk, map_pow, eval_kernelCoordinate]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero k hd)

/-- Actual affine-point evaluation on the actual kernel localization. -/
noncomputable def kernelLocalEval (hd : (hP S Prod.fst).eval x ≠ 0) : kernelLocalRing W S →+* F := by
  letI := isLocalization_kernelLocalRing W S
  exact IsLocalization.lift (eval_kernel_powers_isUnit W S h hd)

/-- Localized evaluation agrees with ordinary coordinate-ring evaluation on each original function. -/
theorem kernelLocalEval_algebraMap (hd : (hP S Prod.fst).eval x ≠ 0) (z : W.toAffine.CoordinateRing) :
    kernelLocalEval W S h hd (algebraMap W.toAffine.CoordinateRing (kernelLocalRing W S) z) = evalAlgHom (W := W.toAffine) (A := F) h z := by
  letI := isLocalization_kernelLocalRing W S
  exact IsLocalization.lift_eq _ _

/-- Localized evaluation fixes the original coefficient field. -/
theorem kernelLocalEval_constant (hd : (hP S Prod.fst).eval x ≠ 0) (a : F) :
    kernelLocalEval W S h hd (algebraMap F (kernelLocalRing W S) a) = a := by
  rw [IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing (kernelLocalRing W S),
    kernelLocalEval_algebraMap, AlgHom.commutes]
  rfl

/-- Actual localized evaluation is onto the original coefficient field. -/
theorem kernelLocalEval_surjective (hd : (hP S Prod.fst).eval x ≠ 0) :
    Function.Surjective (kernelLocalEval W S h hd) :=
  fun a => ⟨algebraMap F (kernelLocalRing W S) a, kernelLocalEval_constant W S h hd a⟩

end Dubon2026.SourceEllipticFunctionField
