import Dubon2026.ArithmeticOrbitRelativeStageLocalizationInvariant
import Dubon2026.OriginalGlobalCompletionInvariantVanishing
import Dubon2026.ArithmeticOrbitCompletionInvariantTerm
import Dubon2026.ArithmeticRelativeStageCocycles

/-! # Actual relative-stage reciprocity

Retain the original finite extension and its literal arithmetic-union
inflation using only Galoisness over its base. This removes the extra
rational-normality assumption from the auxiliary cyclic stage required
by DUB-17's full-order class transfer.
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
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

attribute [local instance] arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete

/-- Every original finite-stage cocycle has a finite set of genuine lower primes supporting each individual completion-localized invariant, uniformly in the rational prime and coset. -/
theorem rationalArithmeticOrbitRelativeStage_invariant_exists_support
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      ∀ (p : ℕ) (hp : p.Prime)
        (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F),
      rationalArithmeticOrbitPrime a p hp F c ∉ T →
      rationalArithmeticOrbitCompletionUnitInvariant a p hp F c
        (rationalArithmeticRelativeStageInflation a F H hFH y) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  classical
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  obtain ⟨S, hS⟩ := originalGlobalAdicH2_exists_finite_support F H
    (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val)
  refine ⟨S.image (originalFinitePrimeBelow F H), ?_⟩
  intro p hp c hc
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H hFH c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
  change rationalArithmeticOrbitCompletionUnitInvariant a p hp F c
    (continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) z) = 0
  have hbelow : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p hp F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH c] using
      rationalArithmeticOrbitPrime_under a p hp F H hFH (QuotientGroup.mk c.out)
  have hout : rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out) ∉ S := by
    intro hw
    exact hc (Finset.mem_image.mpr ⟨_, hw, hbelow⟩)
  exact (rationalArithmeticOrbitCompletionUnitInvariant_eq a p hp F c
      (continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) z)).trans
    ((rationalArithmeticOrbitRelativeStage_localization_invariant a p hp F H hFH hGal c z).trans
      (originalGlobalCompletionInvariant_eq_zero_of_adic F H
        (rationalArithmeticOrbitPrime a p hp F c)
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) (rationalPrimeLocalClosure p hp)
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val) (hS _ hout)))

end
end Dubon2026
