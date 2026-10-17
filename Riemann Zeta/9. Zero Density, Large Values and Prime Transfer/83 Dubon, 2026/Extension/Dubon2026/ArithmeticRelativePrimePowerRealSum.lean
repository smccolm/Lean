import Dubon2026.ArithmeticPrimePowerOriginalPrimeSum
import Dubon2026.ArithmeticRelativeStageReciprocity

/-! # The literal relative-stage finite total with its real correction

Native finite support and annihilator-preserving inflation specialize the
proved all-prime original sum to the same actual relative stage. This is
the arithmetic sum used by DUB-17's original principal-kernel test.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois orbitUnitComparisonGlobalGalois
  arithmeticGlobalUnitContinuousSMul orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The real term is the invariant of genuine field corestriction of
the same original finite-stage inflation. -/
def rationalArithmeticRelativeStageRealInvariant
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) : AddCircle (1 : ℚ) :=
  originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a
    (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
      (Submodule.Quotient.mk (rationalArithmeticRelativeStageInflation a F H hFH y))))

/-- The actual relative-stage prime-power class has finite-place finsum
plus the real invariant of its genuine field corestriction equal to zero. -/
theorem rationalArithmeticRelativeStage_prime_power_finsum_add_real_zero
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
      letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
      letI : IsGalois F H := hGal
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      q ^ (r + 1) • (Submodule.Quotient.mk z : GaloisUnitContinuousH2 (K := F) (Ω := H)) = 0) :
    (∑ᶠ w, rationalArithmeticOriginalPrimeInvariant a F
      (rationalArithmeticRelativeStageInflation a F H hFH y) w) +
      rationalArithmeticRelativeStageRealInvariant a F H hFH y = 0 := by
  obtain ⟨T, hT⟩ := rationalArithmeticRelativePrimeInvariant_exists_support a F H hFH y
  have hs := rationalArithmeticOriginalPrimeInvariant_prime_power_sum_add_real_zero a F q r hq hqa
    (rationalArithmeticRelativeStageInflation a F H hFH y)
    (rationalArithmeticRelativeStageInflation_nsmul_eq_zero a F H hFH (q ^ (r + 1)) y hy) T hT
  have he : (∑ᶠ w, rationalArithmeticOriginalPrimeInvariant a F
      (rationalArithmeticRelativeStageInflation a F H hFH y) w) =
      ∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticRelativeStageInflation a F H hFH y) w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    by_contra h
    exact hw (hT w h)
  exact (congrArg (fun v => v + rationalArithmeticRelativeStageRealInvariant a F H hFH y) he).trans hs

end
end Dubon2026
