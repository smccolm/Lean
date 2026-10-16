import Dubon2026.ArithmeticOrbitCompletionFiniteStage
import Dubon2026.ArithmeticOrbitNormalField
import Dubon2026.OriginalGlobalCompletionH2AmbientComparison
import Dubon2026.ArithmeticOrbitTraceCompletionInvariant

/-! # Relative finite-stage localization

The auxiliary cyclic extension in DUB-17's class-generator argument is
Galois over its own base; normality over the rationals is unnecessary.
Reuse the original embedding towers and actual cocycle comparison with
exactly the relative Galois hypothesis needed by those maps.
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
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  (hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The actual finite arithmetic stage has the existing original global completion invariant, with all completion and global tower premises derived. -/
theorem rationalArithmeticOrbitRelativeStage_originalInvariant :
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
    ∀ x : GaloisUnitContinuousH2 (K := F) (Ω := H),
    originalGlobalCompletionInvariant F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) (rationalPrimeLocalClosure p hp)
      (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits F H)
        (discreteGaloisUnitAction_continuous (K := F) (Ω := H)) x) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)
        (continuousGaloisUnitBaseChangeH2 F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
          H (rationalPrimeLocalClosure p hp) x) := by
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
  intro x
  exact originalGlobalCompletionInvariant_ambient F H (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) (rationalPrimeLocalClosure p hp) x

end
end Dubon2026
