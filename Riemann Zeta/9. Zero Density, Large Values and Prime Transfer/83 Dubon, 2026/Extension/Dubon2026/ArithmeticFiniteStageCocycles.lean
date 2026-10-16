import Dubon2026.ArithmeticOrbitNormalField
import Dubon2026.ArithmeticOrbitFieldBaseChange
import Dubon2026.ContinuousGaloisUnitBaseChange

/-! # The literal original cocycles at a finite arithmetic stage

Retain the genuine finite Galois stage, canonical field inclusion and
discrete unit coefficients in a named source type. Its inflation is the
existing continuous base-change map. This separates the fixed global
source data from the varying local-prime structures in DUB-17's support
argument; no cohomology class or support condition is postulated.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The actual continuous unit two-cocycles of the specified original finite Galois arithmetic stage. -/
def rationalArithmeticFiniteStageCocycles : Type := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  exact ↥(continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H))

/-- Retain the original arithmetic-union unit coefficients with their discrete topology. -/
local instance arithmeticFiniteStageUpperTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The specified original arithmetic-union coefficient topology is discrete. -/
local instance arithmeticFiniteStageUpperDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩

/-- Inflate the actual original finite-stage cocycle into the same original arithmetic union. -/
def rationalArithmeticFiniteStageInflation (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  exact continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y

/-- The named inflation is definitionally the original continuous base-change cocycle, with the same actual source and values. -/
theorem rationalArithmeticFiniteStageInflation_eq (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
    letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    rationalArithmeticFiniteStageInflation a F H hFH y =
      continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y := rfl

end
end Dubon2026
