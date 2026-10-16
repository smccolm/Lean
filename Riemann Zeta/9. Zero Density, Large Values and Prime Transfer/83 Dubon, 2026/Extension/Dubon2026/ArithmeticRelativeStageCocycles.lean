import Dubon2026.ArithmeticOrbitNormalField
import Dubon2026.ArithmeticOrbitFieldBaseChange
import Dubon2026.ContinuousGaloisUnitBaseChange

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
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (H : IntermediateField ℚ (rationalUnramifiedExtension a))
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual continuous unit two-cocycles of the specified original finite Galois arithmetic stage. -/
def rationalArithmeticRelativeStageCocycles : Type := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  exact ↥(continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H))

/-- Retain the original arithmetic-union unit coefficients with their discrete topology. -/
local instance arithmeticRelativeStageUpperTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⊥
/-- The specified original arithmetic-union coefficient topology is discrete. -/
local instance arithmeticRelativeStageUpperDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := ⟨rfl⟩

/-- Inflate the actual original finite-stage cocycle into the same original arithmetic union. -/
def rationalArithmeticRelativeStageInflation (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : IsGalois F H := hGal
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  exact continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y

/-- The named inflation is definitionally the original continuous base-change cocycle, with the same actual source and values. -/
theorem rationalArithmeticRelativeStageInflation_eq (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsGalois F H := hGal
    letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    rationalArithmeticRelativeStageInflation a F H hFH y =
      continuousGaloisUnitBaseChangeCocycle F F H (rationalUnramifiedExtension a) y := rfl

end
end Dubon2026
