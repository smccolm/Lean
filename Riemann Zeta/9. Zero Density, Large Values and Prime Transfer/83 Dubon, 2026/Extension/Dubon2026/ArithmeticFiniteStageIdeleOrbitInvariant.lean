import Dubon2026.ArithmeticFiniteStageIdeleCohomology
import Dubon2026.ArithmeticOrbitFiniteStageLocalizationInvariant
import Dubon2026.ArithmeticOrbitCompletionInvariantTerm
import Dubon2026.OriginalFullIdeleCompletionInvariant

/-! # The actual finite-stage full-idele invariant at its original prime

All scalar towers and lying-over relations are the ones already proved
for the same finite arithmetic stage and coset. The normalized full-idele
coordinate has exactly the original global invariant on a principal
class. This is the termwise comparison required to descend DUB-17's
proved original-prime reciprocity sum through the class quotient.
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
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

attribute [local instance] arithmeticFiniteStageIdeleAddCommGroup arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

/-- The actual normalized full-idele completion invariant at the original coset-induced prime. -/
def rationalArithmeticFiniteStageIdeleOrbitInvariant :
    rationalArithmeticFiniteStageIdeleH2 a F H hFH →+ AddCircle (1 : ℚ) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H.toIntermediateField hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H.toIntermediateField hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H.toIntermediateField (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H.toIntermediateField hFH c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  exact originalFullIdeleCompletionInvariant F H (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))
    (rationalPrimeLocalClosure p hp)

/-- The actual principal image has precisely the same original global completion invariant used by the proved prime reciprocity sum. -/
theorem rationalArithmeticFiniteStageIdeleOrbitInvariant_principal
    (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    rationalArithmeticFiniteStageIdeleOrbitInvariant a p hp F H hFH c
      (rationalArithmeticFiniteStagePrincipalClass a F H hFH y) =
      rationalArithmeticOrbitCompletionUnitInvariant a p hp F c
        (rationalArithmeticFiniteStageInflation a F H hFH y) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H.toIntermediateField hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H.toIntermediateField hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H.toIntermediateField (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H.toIntermediateField hFH c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  have hi := originalFullIdeleCompletionInvariant_principal F H
    (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))
    (rationalPrimeLocalClosure p hp) (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val)
  have hg := rationalArithmeticOrbitFiniteStage_localization_invariant a p hp F H.toIntermediateField hFH c z
  have ht := rationalArithmeticOrbitCompletionUnitInvariant_eq a p hp F c
    (rationalArithmeticFiniteStageInflation a F H hFH y)
  exact hi.trans (hg.symm.trans ht.symm)

/-- Original idele localization vanishing kills the same normalized finite-stage coordinate. -/
theorem rationalArithmeticFiniteStageIdeleOrbitInvariant_eq_zero_of_adic
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH)
    (hx : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      originalFullIdeleAdicH2 F H
        (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))
        (x : groupCohomology (originalFullIdeleRep F H) 2) = 0) :
    rationalArithmeticFiniteStageIdeleOrbitInvariant a p hp F H hFH c x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H.toIntermediateField hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H.toIntermediateField (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H.toIntermediateField hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H.toIntermediateField (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H.toIntermediateField hFH c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  exact originalFullIdeleCompletionInvariant_eq_zero_of_adic F H
    (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out))
    (rationalPrimeLocalClosure p hp) x hx

end
end Dubon2026
