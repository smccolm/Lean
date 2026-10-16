import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.ArithmeticRelativeNormalizedPrimeLift

/-! # Normalize the actual local class at any arithmetic representative

The original single-prime trace lift recovers the constructed normalized
local class. No full-decomposition assumption is required. This supplies
the same-class normalization needed at all upper primes in DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]
  (σ : rationalArithmeticGaloisGroup a)

attribute [local instance] arithmeticRelativeStageIdeleAddCommGroup arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois


/-- Every actual arithmetic representative admits a constructed original local class with reciprocal decomposition-degree invariant on its genuine trace lift. -/
theorem rationalArithmeticRelativeStage_exists_representative_normalized_local_trace :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalTraceNormalization F H
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
      (rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F (QuotientGroup.mk σ)
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk σ)
  letI := rationalArithmeticOrbit_commonRepresentative_globalTower a p hp F H hFH σ
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F (QuotientGroup.mk σ)
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H (QuotientGroup.mk σ)
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp F H hFH σ
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  exact originalSinglePrime_exists_normalized_local_lift F H
    (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
    (rationalPrimeLocalClosure p hp)

end
end Dubon2026
