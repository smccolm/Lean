import Dubon2026.ArithmeticRelativeStageIdelePrimeRepresentative
import Dubon2026.OriginalIdeleInvariantPrimeIndependence

/-! # Canonical prime coordinates equal the original completion invariant

For every original upper prime and compatible closure, identify the actual
canonical prime coordinate with the normalized original completion map.
The existing representative theorem and proved prime-choice independence
construct the comparison; no normalization or representative equality is
assumed. This is DUB-17's source-normalization bridge for supplied local classes.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

/-- Each specified base-prime coordinate agrees with original completion localization at every upper prime and compatible closure; this proposition alone asserts no comparison. -/
def OriginalPrimeInvariantRealization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (primeInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
      (Ω : Type) [Field Ω]
      [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
      [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
      [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
      [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
      [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
      (x : groupCohomology (originalFullIdeleRep K L) 2),
      primeInvariant v x = originalFullIdeleCompletionInvariant K L v w Ω x

attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra arithmeticRelativeStageIdeleAddCommGroup

/-- The actual canonical arithmetic prime coordinate equals the original normalized completion invariant at every upper prime and every compatible closure. -/
theorem rationalArithmeticRelativeStage_prime_invariant_realization
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H] :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalPrimeInvariantRealization F H
      (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  change OriginalPrimeInvariantRealization F H
    (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH)
  intro v w hw Ω _ _ _ _ _ _ _ _ x
  obtain ⟨p, hp, σ, hv, hi⟩ :=
    rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative a F H hFH v
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp F H hFH σ
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  exact (congrArg (fun f => f x) hi).trans
    (originalFullIdeleCompletionInvariant_same_base F H v
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) w
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
      Ω (rationalPrimeLocalClosure p hp) hv x)

end
end Dubon2026
