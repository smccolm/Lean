import Dubon2026.ArithmeticPrimePowerLocalRestrictions
import Dubon2026.ArithmeticRelativeLocalTraceTotal
import Dubon2026.OriginalUniversalLocalRestrictions

/-! # The actual arithmetic class is compatible with every normalized local choice

The common global class and the proved canonical trace-total formula
identify its restrictions with all supplied normalized local classes.
Both ingredients are constructed at the actual odd-primary finite stage;
neither local compatibility nor an invariant certificate is an input.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every actual odd-primary Galois stage has one full-order original global class compatible with every supplied normalized original local class at every upper prime, and such local classes exist. -/
theorem rationalArithmeticRelativePrimePower_exists_universal_local_restrictions
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
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
    OriginalUniversalNormalizedLocalRestrictions F H
      (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
        (originalFinitePrimeBelow F H w)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_universal_local_restrictions F H _
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativePrimePower_exists_canonical_trace_system
      (hGalKE := hGal) a F H hFH q t hq hq2 hqa hdegree)
    (rationalArithmeticRelativeStage_local_trace_total (hGal := hGal) a F H hFH)
    (rationalArithmeticRelativePrimePower_exists_normalized_local_restrictions
      (hGal := hGal) a F H hFH q t hq hq2 hqa hdegree)

end
end Dubon2026
