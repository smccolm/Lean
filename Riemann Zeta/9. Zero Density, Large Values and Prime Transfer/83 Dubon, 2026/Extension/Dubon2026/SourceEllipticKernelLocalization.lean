import Dubon2026.SourceEllipticOddIntermediateRing
import Mathlib.RingTheory.Localization.AsSubring

/-! The original coordinate ring with the actual kernel denominator inverted
inside its actual function field. SourceEllipticOddIntermediateLocalization
identifies it with the common integral closure, supplying the point-map formula
and ideal-norm comparison on the DUB-17/18 dependency. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open scoped nonZeroDivisors

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The actual finite kernel polynomial in the original affine coordinate ring. -/
noncomputable def kernelCoordinate : W.toAffine.CoordinateRing :=
  algebraMap F[X] W.toAffine.CoordinateRing (hP S Prod.fst)

/-- The kernel coordinate maps to the actual generic kernel denominator. -/
theorem kernelCoordinate_image :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (kernelCoordinate W S) =
      aeval (genericX W.toAffine) (hP S Prod.fst) :=
  (IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField _).symm.trans
    (algebraMap_eq_aeval_genericX W.toAffine _)

/-- The actual kernel coordinate is nonzero. -/
theorem kernelCoordinate_ne_zero : kernelCoordinate W S ≠ 0 := by
  intro h
  have he := kernelCoordinate_image W S
  rw [h, map_zero] at he
  exact generic_kernel_denominator_ne_zero W S he.symm

/-- Powers of the actual kernel denominator are nonzero divisors. -/
theorem kernelCoordinate_powers_le : Submonoid.powers (kernelCoordinate W S) ≤ W.toAffine.CoordinateRing⁰ := by
  rintro z ⟨k, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero k (kernelCoordinate_ne_zero W S))

/-- The actual localization away from the kernel denominator, inside the original field. -/
noncomputable def kernelLocalRing : Subalgebra W.toAffine.CoordinateRing W.toAffine.FunctionField :=
  Localization.subalgebra.ofField W.toAffine.FunctionField (Submonoid.powers (kernelCoordinate W S))
    (kernelCoordinate_powers_le W S)

/-- The specified subalgebra is the localization at powers of the actual kernel denominator. -/
theorem isLocalization_kernelLocalRing :
    IsLocalization (Submonoid.powers (kernelCoordinate W S)) (kernelLocalRing W S) := by
  unfold kernelLocalRing
  infer_instance

/-- The actual inverse kernel denominator belongs to this localization. -/
theorem inverse_kernel_mem_local :
    (aeval (genericX W.toAffine) (hP S Prod.fst))⁻¹ ∈ kernelLocalRing W S := by
  rw [← kernelCoordinate_image]
  change ∃ (a s : W.toAffine.CoordinateRing) (_ : s ∈ Submonoid.powers (kernelCoordinate W S)),
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (kernelCoordinate W S))⁻¹ =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a *
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField s)⁻¹
  exact ⟨1, kernelCoordinate W S, ⟨1, pow_one _⟩, by simp⟩

/-- Inverting precisely the actual kernel denominator generates this localization. -/
theorem kernelLocalRing_le (T : Subalgebra W.toAffine.CoordinateRing W.toAffine.FunctionField)
    (hinv : (aeval (genericX W.toAffine) (hP S Prod.fst))⁻¹ ∈ T) : kernelLocalRing W S ≤ T := by
  intro z hz
  change ∃ (a s : W.toAffine.CoordinateRing) (_ : s ∈ Submonoid.powers (kernelCoordinate W S)),
    z = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a *
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField s)⁻¹ at hz
  obtain ⟨a, s, ⟨k, rfl⟩, rfl⟩ := hz
  rw [map_pow, ← inv_pow, kernelCoordinate_image]
  exact T.mul_mem (T.algebraMap_mem a) (T.pow_mem hinv k)

end Dubon2026.SourceEllipticFunctionField
