import Dubon2026.ArithmeticRelativeAnyPrimeNormalizedTotal
import Dubon2026.OriginalCanonicalLocalClassNormalization
import Dubon2026.ArithmeticPrimePowerCanonicalTraceSystem

/-! # Normalize the actual class invariant at every upper prime

The canonical class/trace system and the constructed joint normalization
supply an injective exact-image decomposition-subgroup invariant at every
original upper prime. This removes DUB-17's upper-prime-choice obstacle;
the required inter-stage comparisons remain separate obligations.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every original upper prime of an actual odd-primary Galois stage has an injective exact-image decomposition class invariant normalized by the same constructed local class as its actual canonical prime coordinate. -/
theorem rationalArithmeticRelativePrimePower_exists_any_prime_local_class
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalCanonicalPrimeClassNormalization F H w
      (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
        (originalFinitePrimeBelow F H w)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  exact originalIdeleClass_canonical_prime_normalization F H w
    (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH (originalFinitePrimeBelow F H w))
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativePrimePower_exists_canonical_trace_system
      (hGalKE := hGal) a F H hFH q t hq hq2 hqa hdegree)
    (rationalArithmeticRelativeStage_exists_any_prime_normalized_trace
      (hGal := hGal) a F H hFH w)

end
end Dubon2026
