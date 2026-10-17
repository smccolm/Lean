import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.OriginalNormalizedIdeleLiftWitness

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
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


/-- The actual orbit-selected full-decomposition prime supplies an original finite-stage idele H2 class with reciprocal global degree and no other finite localization. -/
theorem rationalArithmeticRelativeStageIdeleRepresentativeInvariant_exists_normalized_lift
    (n : ℕ)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = n)
    (hw : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      OriginalFiniteDecompositionGroup F H
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)) = ⊤) :
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x =
        (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
        ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
          t ≠ rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ) →
            originalFullIdeleAdicH2 F H t x = 0) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
        ∃ y : groupCohomology (originalAdicUnitRep F H
            (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))) 2,
          x = originalFullDecompositionIdeleH2Lift F H
            (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)) hw y) := by
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
  obtain ⟨x, hx, hs, hy⟩ := originalFullDecomposition_exists_normalized_idele_lift F H
    (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
    (rationalPrimeLocalClosure p hp) hw
  refine ⟨x, ?_, hs, hy⟩
  exact hx.trans (congrArg (fun k : ℕ => (↑((1 : ℚ) / k) : AddCircle (1 : ℚ))) hdegree)

end
end Dubon2026
