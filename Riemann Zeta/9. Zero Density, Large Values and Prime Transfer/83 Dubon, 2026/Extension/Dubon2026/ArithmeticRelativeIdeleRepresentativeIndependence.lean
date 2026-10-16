import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.OriginalIdeleInvariantPrimeIndependence

/-! # Prime-choice independence of the actual relative arithmetic invariant

The original Galois action, inflation composition and closure independence
compare all upper-prime representatives over the same base prime. This
removes the full-decomposition restriction from DUB-17's normalization path.
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

attribute [local instance] arithmeticRelativeStageIdeleAddCommGroup
variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]
  (p₀ : ℕ) (hp₀ : p₀.Prime) (σ₀ : rationalArithmeticGaloisGroup a)
  (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a)

/-- Every upper-prime representative over the same original base prime gives the same actual normalized arithmetic invariant, without a full-decomposition assumption. -/
theorem rationalArithmeticRelativeStageIdeleRepresentativeInvariant_prime_independent
    (hv : (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) = (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x =
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p₀ hp₀ F H hFH σ₀ x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p₀ hp₀ F H hFH σ₀
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrimeCompletion a p₀ hp₀ H (QuotientGroup.mk σ₀)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p₀ hp₀ F H hFH σ₀
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalPrimeLocalClosure p₀ hp₀)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalPrimeLocalClosure p₀ hp₀)) := ⟨rfl⟩
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp F H hFH σ
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  exact originalFullIdeleCompletionInvariant_same_base F H
    (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
    (rationalPrimeLocalClosure p₀ hp₀) (rationalPrimeLocalClosure p hp) hv x

end
end Dubon2026
