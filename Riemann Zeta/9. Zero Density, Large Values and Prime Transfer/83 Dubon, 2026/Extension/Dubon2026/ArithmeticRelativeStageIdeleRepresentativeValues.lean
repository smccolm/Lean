import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport

/-! # Values of the actual single-prime arithmetic class at other representatives

Use full-decomposition uniqueness and closure independence at the same
base prime; use actual localization support at every other base prime.
These are the two cases needed to assemble DUB-17's canonical total.
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

/-- Over the same original base prime, full decomposition identifies the upper prime and the actual normalized arithmetic value is independent of the representative and compatible closure. -/
theorem rationalArithmeticRelativeStageIdeleRepresentativeInvariant_same_base
    (hw : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      OriginalFiniteDecompositionGroup F H (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) = ⊤)
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
  exact originalFullDecomposition_invariant_same_base F H
    (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
    (rationalPrimeLocalClosure p₀ hp₀) (rationalPrimeLocalClosure p hp) hw hv x

/-- An actual arithmetic idele class supported at the specified original upper prime has zero normalized value at every other original base prime. -/
theorem rationalArithmeticRelativeStageIdeleRepresentativeInvariant_other_base
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (hs : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H), t ≠ (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) →
        originalFullIdeleAdicH2 F H t x = 0)
    (hv : (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) ≠ (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀))) :
    rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp F H hFH σ
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ)) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p₀ hp₀ F H hFH σ₀
  have hb := originalFinitePrimeBelow_eq_of_liesOver F H (rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀))
  exact originalFullIdeleInvariant_eq_zero_of_other_base F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)) (rationalPrimeLocalClosure p hp)
    x hs (fun h => hv (h.trans hb))

end
end Dubon2026
