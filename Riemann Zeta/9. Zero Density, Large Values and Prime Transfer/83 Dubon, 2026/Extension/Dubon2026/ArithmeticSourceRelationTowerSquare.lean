import Dubon2026.ArithmeticSourceClassScalarStage
import Dubon2026.ArithmeticFiniteStageTowerComparison

/-! # The constructed source relation has the exact arithmetic tower square

The finite representative's literal colimit values supply the square, and
the tower coefficient comparison acts as the identity. This discharges the
coefficient-compatibility input of DUB-17's finite-to-source obstruction
comparison; no morphism-square certificate is assumed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceTowerSquareUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceTowerSquareFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceTowerSquareHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The actual finite-value identity of the constructed source representative
is exactly the commuting coefficient square through the original tower. -/
theorem arithmeticSourceClassRelationData_finite_square
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B))
    (r : ArithmeticSourceClassRelationData Ω a ha P B c) :
    letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
    letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
    letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
    letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
    letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
      AlgEquiv.restrictNormalHom r.stage
    let τ : Gal(r.stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
    let j := coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
    (Rep.resFunctor π).map η ≫ j =
      (Rep.resFunctor π).map (originalRelationGroupChange τ B) ≫
        arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage
          (originalRelationModule B) ≫ r.relation := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let τ : Gal(r.stage/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
  change (Rep.resFunctor π).map η ≫ j =
      (Rep.resFunctor π).map (originalRelationGroupChange τ B) ≫
        arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage
          (originalRelationModule B) ≫ r.relation
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact r.finiteRelation_values z

end
end Dubon2026
