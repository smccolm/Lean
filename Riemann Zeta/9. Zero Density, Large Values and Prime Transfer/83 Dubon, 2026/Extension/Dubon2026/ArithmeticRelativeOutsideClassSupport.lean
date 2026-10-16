import Dubon2026.ArithmeticClassesModOutsideH1
import Dubon2026.ArithmeticPrimePowerLocalRestrictions

/-! # Actual outside support at relative finite arithmetic stages

The same exceptional integer defines the support over every finite base
inside the fixed arithmetic union. Unramifiedness and support stability
are derived from the actual embeddings, supplying the quotient comparison
for DUB-17's normalized finite class system.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Every finite intermediate field in the actual arithmetic union is absolutely unramified outside the original exceptional support. -/
theorem rationalArithmeticIntermediateClassSupport_unramified
    (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
    (w : HeightOneSpectrum (𝓞 H))
    (hw : w ∉ originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
      (originalIntegerMap_ne_zero (L := H) a ha)) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  have hwa : algebraMap (𝓞 ℚ) (𝓞 H) a ∉ w.asIdeal := by
    simpa only [mem_originalExceptionalIntegerSupport] using hw
  have hi := originalUnramifiedUnion_finite_ramification a ha H w hwa
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ) (p := w.asIdeal) w.ne_bot).mpr hi
  haveI : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv
      (show ℤ ≃ₐ[ℤ] 𝓞 ℚ from { Rat.ringOfIntegersEquiv.symm with
        commutes' := fun r => map_intCast Rat.ringOfIntegersEquiv.symm r })
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime w.asIdeal)

/-- The unchanged rational exceptional support is stable under every relative stage automorphism. -/
theorem rationalArithmeticIntermediateRelativeClassSupport_stable
    (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    ∀ (σ : Gal(H/F)) w,
      w ∈ originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha) ↔
      numberFieldGaloisPlaceEquiv F H σ w ∈
        originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
          (originalIntegerMap_ne_zero (L := H) a ha) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  intro σ w
  exact originalExceptionalIntegerSupport_galoisStable H ℚ a ha (σ.restrictScalars ℚ) w

end
end Dubon2026
