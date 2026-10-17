import Dubon2026.ArithmeticAllPrimeCompletionRestrictions
import Dubon2026.OriginalFiniteNormalizedClassSystem
import Dubon2026.ArithmeticAllPrimeUniversalLocalRestrictions
import Dubon2026.OriginalCompletionClassRestrictions

/-! # The source-normalized finite class system at every allowed prime-power stage

The actual prime-power global class and proved prime-coordinate realization
give source-normalized compatibility at every original upper prime, in
every compatible closure, for every supplied normalized finite local class.
All maps retain the original cohomology, field and prime objects.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every actual allowed prime-power Galois stage has the original finite class system: one full-order global class, vanishing subgroup H1, exact subgroup H2 cardinalities and restriction generators, and all source-normalized original completion restrictions. -/
theorem rationalArithmeticRelativeAllPrimePower_finite_normalized_class_system
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalFiniteNormalizedClassSystem F H := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_finite_normalized_system_of_completion_restrictions F H
    (rationalArithmeticRelativeAllPrimePower_exists_completion_local_restrictions
      (hGal := hGal) a F H hFH q t hq hqa hdegree)

end
end Dubon2026
