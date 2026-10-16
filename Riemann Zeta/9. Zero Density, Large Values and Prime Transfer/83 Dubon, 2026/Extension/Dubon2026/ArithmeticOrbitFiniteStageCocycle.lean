import Dubon2026.ArithmeticOrbitFiniteStageInflationTower
import Dubon2026.ArithmeticOrbitNormalField
import Dubon2026.ArithmeticOrbitCompletionUnitBaseChange
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # The actual stage inflation and original localization cocycles compose

All literal global and completed scalar towers are derived from the same
lower representative. Reuse the existing continuous cocycle composition
theorem to identify the inflated arithmetic-union cocycle with direct
stage localization, the map equality required by DUB-17's invariant sum.
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
  [FiniteDimensional ℚ F] [IsGalois ℚ H] (hFH : F ≤ H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The actual original completion localization of a stage-inflated cocycle equals direct localization of the same stage cocycle. -/
theorem rationalArithmeticOrbitFiniteStage_completionCocycle :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
    letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
    letI : Algebra H (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
    letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H hFH c
    letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
    ∀ y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H),
    rationalArithmeticOrbitCompletionUnitCocycle a p hp F c
      (continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y) =
      continuousGaloisUnitBaseChangeCocycle F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        H (rationalPrimeLocalClosure p hp) y := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  intro y
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : SMul H (rationalPrimeLocalClosure p hp) :=
    (arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)).toSMul
  let hUnion : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hStage : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  let hSame : IsScalarTower F F (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  let hCompletion := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  let hGlobal := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H hFH c
  let hInflation := rationalArithmeticOrbitFiniteStage_inflationTower a p hp F H c
  exact @continuousGaloisUnitBaseChangeCocycle_comp F F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    H (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp)
    _ _ _ _ _ _
    (Algebra.id F) (arithmeticOrbitCompletionGlobalAlgebra a p hp F c)
    (arithmeticOrbitCompletionGlobalAlgebra a p hp F c)
    (IntermediateField.inclusion hFH).toAlgebra F.toAlgebra (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    F.toAlgebra (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (arithmeticOrbitCompletionClosureAlgebra a p hp F c)
    H.toAlgebra (arithmeticOrbitUpperAlgebra a p hp F c)
    (arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out))
    hSame hStage hCompletion hUnion hCompletion hGlobal hInflation
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance y

end
end Dubon2026
