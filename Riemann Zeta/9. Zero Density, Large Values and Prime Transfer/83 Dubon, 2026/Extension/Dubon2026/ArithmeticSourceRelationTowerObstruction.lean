import Dubon2026.ArithmeticSourceRelationTowerSquare
import Dubon2026.ArithmeticFiniteStageTowerComparison
import Dubon2026.OriginalRelationObstructionTower

/-! # The descended obstruction returns to the original source presentation

Compose the actual finite-value square with both proved connecting
naturality identities. The resulting same-representative comparison is
needed for DUB-17's continuous cup and normalized local invariant argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceTowerObstructionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceTowerObstructionFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceTowerObstructionHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

omit [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] in
/-- The finite obstruction of the constructed source representative has
exactly the original source-stage connecting image after literal inflation
and the identity-on-values tower comparison. No square or naturality premise
is left to the arithmetic caller. -/
theorem arithmeticSourceClassRelationData_obstruction_tower
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
    let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
    let j := coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
    let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
    let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
    let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage B
    originalRelationExtensionObstruction BN C η ≫ groupCohomology.map π j 2 =
      groupCohomology.map π (𝟙 (Rep.res π BN)) 1 ≫
        groupCohomology.map (MonoidHom.id _) β 1 ≫
          groupCohomology.δ (originalRelationGroupChange_shortExact σ B) 1 2 rfl ≫
            (groupCohomology.functor ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) 2).map
              r.relation := by
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
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage B
  have hs := arithmeticSourceClassRelationData_finite_square Ω a ha P B c r
  change originalRelationExtensionObstruction BN C η ≫ groupCohomology.map π j 2 =
      groupCohomology.map π (𝟙 (Rep.res π BN)) 1 ≫
        groupCohomology.map (MonoidHom.id _) β 1 ≫
          groupCohomology.δ (originalRelationGroupChange_shortExact σ B) 1 2 rfl ≫
            (groupCohomology.functor ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) 2).map
              r.relation
  exact originalRelation_obstruction_tower_presentation π τ B C D
    (arithmeticSourceRelationPresentation Ω a P B) (originalRelationGroupChange_shortExact σ B)
    (arithmeticFiniteRelationTowerDiagram ℚ Ω a P r.stage r.le_stage B)
    η j r.relation hs

end
end Dubon2026
