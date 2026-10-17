import Dubon2026.ArithmeticSourceRelationTowerSquare
import Dubon2026.ArithmeticSourceRelationContinuousFiniteMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceContinuousDiagramUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceContinuousDiagramFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceContinuousDiagramHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The literal finite relation presentation maps to the original source
presentation through the canonical relation and identity-on-values tower maps. -/
def arithmeticSourceRelationFiniteDiagram
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :
    (Rep.resFunctor (AlgEquiv.restrictNormalHom r.stage :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ))).mapShortComplex.obj
        (originalRelationShortComplex (arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r)) ⟶
      arithmeticSourceRelationPresentation Ω a P B := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let τ : Gal(r.stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  exact (Rep.resFunctor π).mapShortComplex.map (originalRelationGroupChangeSequenceMap τ B) ≫
    arithmeticFiniteRelationTowerDiagram ℚ Ω a P r.stage r.le_stage B

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The constructed finite relation values give the exact coefficient square
of the actual finite-to-source presentation diagram. -/
theorem arithmeticSourceRelationFiniteDiagram_square
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
      AlgEquiv.restrictNormalHom r.stage
    (Rep.resFunctor π).map (arithmeticSourceClassRelationStageHom Ω a ha P B c r) ≫
      coefficientRepresentationColimitOf _
        (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage =
      (arithmeticSourceRelationFiniteDiagram Ω a ha P B c r).τ₁ ≫ r.relation := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let τ : Gal(r.stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  have h := arithmeticSourceClassRelationData_finite_square Ω a ha P B c r
  change (Rep.resFunctor π).map (arithmeticSourceClassRelationStageHom Ω a ha P B c r) ≫
      coefficientRepresentationColimitOf _
        (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage =
    ((Rep.resFunctor π).map (originalRelationGroupChange τ B) ≫
      arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage
        (originalRelationModule B)) ≫ r.relation
  simpa only [Category.assoc] using h

end
end Dubon2026
