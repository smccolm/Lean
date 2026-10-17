import Dubon2026.ArithmeticAllPrimeUniversalLocalRestrictions
import Dubon2026.OriginalCompletionClassRestrictions

/-! # Actual arithmetic restrictions for every normalized completion class

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

/-- Every actual prime-power Galois stage has one full-order original class compatible with every supplied original finite-completion class normalized by the actual local invariant. -/
theorem rationalArithmeticRelativeAllPrimePower_exists_completion_local_restrictions
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
    ∃ u : groupCohomology (originalIdeleClassRep F H) 2,
      addOrderOf u = Module.finrank F H ∧ OriginalCompletionClassRestrictions F H u := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_exists_completion_local_restrictions F H
    (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH)
    (rationalArithmeticRelativeStage_prime_invariant_realization (hGal := hGal) a F H hFH)
    (rationalArithmeticRelativeAllPrimePower_exists_universal_local_restrictions
      (hGal := hGal) a F H hFH q t hq hqa hdegree)

end
end Dubon2026
