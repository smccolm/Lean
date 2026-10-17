import Dubon2026.ArithmeticSourceRelationTowerObstruction
import Dubon2026.ArithmeticFiniteH1SourcePullback
import Dubon2026.ArithmeticSourceRelationCup

/-! # The actual source cup realizes its descended finite obstruction

Inflate each finite H1 input continuously and apply the proved tower
comparison to the same source-cocycle relation data. This removes the
finite/global presentation gap in DUB-17's duality chain. Comparison with
normalized local invariants remains a separate mathematical obligation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceFiniteCupUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceFiniteCupFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceFiniteCupHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Each finite obstruction of the same constructed source relation is
the actual source cup on a continuous inflation of its finite H1 input,
after the literal full-class and continuous-to-algebraic comparisons. -/
theorem arithmeticSourceClassRelationData_finite_obstruction_cup [Finite B]
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
    let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
    let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
    let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
    let j := coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
    ∀ y : groupCohomology BN 1,
      ∃ x : arithmeticSourceRelationContinuousH1 Ω a P B,
        arithmeticSourceRelationCupClass Ω a ha P B c x =
          groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y) := by
  letI : Algebra P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra
  letI : Module P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toModule
  letI : SMul P r.stage := (IntermediateField.inclusion r.le_stage).toAlgebra.toSMul
  letI : IsScalarTower ℚ P r.stage := IsScalarTower.of_algHom (IntermediateField.inclusion r.le_stage)
  letI : IsScalarTower P r.stage (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(r.stage/ℚ) :=
    AlgEquiv.restrictNormalHom r.stage
  let BN := arithmeticSourceClassRelationStageCoefficient Ω a ha P B c r
  let η := arithmeticSourceClassRelationStageHom Ω a ha P B c r
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha r.stage
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) r.stage
  let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res σ B
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P r.stage r.le_stage B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  change ∀ y : groupCohomology BN 1,
      ∃ x : arithmeticSourceRelationContinuousH1 Ω a P B,
        arithmeticSourceRelationCupClass Ω a ha P B c x =
          groupCohomology.map π j 2 ((originalRelationExtensionObstruction BN C η).hom y)
  intro y
  obtain ⟨x, hx⟩ := arithmeticFiniteStageH1_exists_source_pullback Ω a P r.stage r.le_stage B y
  refine ⟨x, ?_⟩
  rw [arithmeticSourceClassRelationData_cup_toAlgebraic Ω a ha P B c r]
  have ht := arithmeticSourceClassRelationData_obstruction_tower Ω a ha P B c r
  have he := congrArg (fun m : groupCohomology BN 1 ⟶ groupCohomology D 2 => m.hom y) ht
  change groupCohomology.map (MonoidHom.id _) r.relation 2
      (groupCohomology.δ (originalRelationGroupChange_shortExact σ B) 1 2 rfl
        (continuousH1ToAlgebraic A hA x)) = _
  change continuousH1ToAlgebraic A hA x =
    groupCohomology.map (MonoidHom.id _) β 1
      (groupCohomology.map π (𝟙 (Rep.res π BN)) 1 y) at hx
  rw [hx]
  exact he.symm

end
end Dubon2026
