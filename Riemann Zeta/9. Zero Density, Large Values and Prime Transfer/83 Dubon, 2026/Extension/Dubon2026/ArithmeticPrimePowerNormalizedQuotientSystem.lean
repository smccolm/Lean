import Dubon2026.ArithmeticRelativeOutsideClassSupport
import Dubon2026.ArithmeticPrimePowerCompletionRestrictions
import Dubon2026.OriginalFiniteNormalizedQuotientSystem

/-! # The actual arithmetic normalized finite quotient class system

Membership in the original arithmetic union discharges outside-support
unramifiedness. The proved source-normalized full-class constructor supplies
the input to the genuine quotient comparison, for each odd-primary relative
Galois stage. This is DUB-17's finite quotient input, not class/Ext duality.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every actual odd-primary relative Galois stage has a normalized finite class system on its literal original outside-unit quotient, with all support, H1, H2 and completion conditions derived. -/
theorem rationalArithmeticRelativePrimePower_normalized_quotient_system
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalFiniteNormalizedQuotientSystem F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  apply originalClassQuotient_finite_normalized_system F H _ _
    (rationalArithmeticIntermediateClassSupport_unramified a ha H)
  exact originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
    (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)

end
end Dubon2026
