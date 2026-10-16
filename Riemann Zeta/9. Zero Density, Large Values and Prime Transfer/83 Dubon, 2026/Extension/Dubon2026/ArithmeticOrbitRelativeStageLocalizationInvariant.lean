import Dubon2026.ArithmeticOrbitRelativeGlobalInvariant
import Dubon2026.ArithmeticOrbitRelativeStageCocycle

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
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  (hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The actual inflated finite-stage cocycle has precisely the original finite-global invariant at the genuine prime selected by the same lower coset. -/
theorem rationalArithmeticOrbitRelativeStage_localization_invariant :
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
    ∀ y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H),
    localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)
      (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c
        (continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y))) =
      originalGlobalCompletionInvariant F H (rationalArithmeticOrbitPrime a p hp F c)
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) (rationalPrimeLocalClosure p hp)
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) y.val) := by
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
  intro y
  have hc : rationalArithmeticOrbitCompletionUnitCocycle a p hp F c
      (continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y) =
      continuousGaloisUnitBaseChangeCocycle F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        H (rationalPrimeLocalClosure p hp) y :=
    rationalArithmeticOrbitRelativeStage_completionCocycle a p hp F H hFH hGal c y
  have hi := rationalArithmeticOrbitRelativeStage_originalInvariant a p hp F H hFH hGal c (Submodule.Quotient.mk y)
  have hm := congrArg
    (fun z : continuousRepresentationCocyclesTwo
        (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp)) =>
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk z : GaloisUnitContinuousH2
          (K := rationalArithmeticOrbitPrimeCompletion a p hp F c) (Ω := rationalPrimeLocalClosure p hp))) hc
  exact hm.trans hi.symm

end
end Dubon2026
