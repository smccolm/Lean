import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! Injectivity for the source integral generic-fibre tensor map.
Native module localization reduces injectivity of the extended linear map
to the already faithful integral map. No coordinate-algebra tensor
presentation or new general localization construction is required.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable (R K : Type*) [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A faithful integral linear map into a fraction-field vector space remains faithful after the literal scalar-extension tensor. -/
theorem sourceFraction_liftBaseChange_injective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.liftBaseChange K) := by
  let j := TensorProduct.mk R K M 1
  letI : IsLocalizedModule (nonZeroDivisors R) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K j).mpr
      (TensorProduct.isBaseChange R M K)
  apply IsLocalizedModule.injective_of_map_eq (nonZeroDivisors R) j
    (g := (f.liftBaseChange K).restrictScalars R)
  intro x y h
  change f.liftBaseChange K ((1 : K) ⊗ₜ[R] x) =
    f.liftBaseChange K ((1 : K) ⊗ₜ[R] y) at h
  have he : f x = f y := by
    simpa only [LinearMap.liftBaseChange_one_tmul] using h
  exact congrArg j (hf he)

end
end Dubon2026
