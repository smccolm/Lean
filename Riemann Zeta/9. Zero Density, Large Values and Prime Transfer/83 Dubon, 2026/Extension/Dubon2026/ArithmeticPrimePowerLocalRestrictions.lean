import Dubon2026.ArithmeticRelativeAnyPrimeNormalizedTotal
import Dubon2026.OriginalCanonicalClassLocalRestrictions
import Dubon2026.ArithmeticPrimePowerCanonicalTraceSystem

/-! # One actual arithmetic class with all normalized local restrictions

The odd-primary finite-stage invariant constructor and the unconditional
all-prime local trace constructor supply the generic restriction theorem.
This retains one global class for all original upper primes, with actual
subgroup restriction and local-to-class maps throughout DUB-17's chain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every actual odd-primary Galois stage has one full-order original global class whose restrictions at all original upper primes equal normalized original local-class images. -/
theorem rationalArithmeticRelativePrimePower_exists_normalized_local_restrictions
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
    OriginalNormalizedLocalRestrictions F H
      (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
        (originalFinitePrimeBelow F H w)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_exists_normalized_local_restrictions F H _
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativePrimePower_exists_canonical_trace_system
      (hGalKE := hGal) a F H hFH q t hq hq2 hqa hdegree)
    (fun w => rationalArithmeticRelativeStage_exists_any_prime_normalized_trace
      (hGal := hGal) a F H hFH w)

end
end Dubon2026
