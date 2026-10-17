import Dubon2026.ArithmeticOriginalStageClassCocycleImage
import Dubon2026.ContinuousH2GroupCoefficientComparison
import Dubon2026.ArithmeticSourceRelationContinuousCupMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance originalStageContinuousRepresentativeUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance originalStageContinuousRepresentativeFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance originalStageContinuousRepresentativeIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'


variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticOriginalStageContinuousClassRepresentativeLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology



variable [TopologicalSpace (arithmeticOriginalStageClassRep Ω a ha L)]
  [DiscreteTopology (arithmeticOriginalStageClassRep Ω a ha L)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticOriginalStageContinuousClassRepresentativeLocalInstance2 : @ContinuousSMul ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual continuous class H2 at the finite scalar stage. -/
abbrev arithmeticOriginalStageContinuousClassH2 :=
  ContinuousRepresentationH2 (arithmeticOriginalStageClassRep Ω a ha L) continuous_of_discreteTopology

/-- Inflate the actual finite continuous class through the same restriction
and original class-colimit inclusion used by the scalar obstruction. -/
def arithmeticOriginalStageContinuousClassH2Inflation
    (x : arithmeticOriginalStageContinuousClassH2 Ω a ha L) :
    arithmeticSourceRelationContinuousH2 Ω a ha := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra L.val U :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val U :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  let π : Gal(U/ℚ) →* Gal(L.val/ℚ) := AlgEquiv.restrictNormalHom L.val
  let hπ := originalScalarStageRestriction_continuous Ω a L
  let C := arithmeticOriginalStageClassRep Ω a ha L
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  let hC : Continuous (fun z : Gal(L.val/ℚ) × C => C.ρ z.1 z.2) := continuous_of_discreteTopology
  let hD := arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha
  let j := arithmeticOriginalStageClassToColimit Ω a ha L
  exact continuousCoefficientH2Map (Rep.res π C) D j.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply j)
    (restrictedCoefficientAction_continuous C π hπ hC) hD
    (continuousRepresentationH2Restriction C hC π hπ x)

/-- The scalar-stage continuous class has a finite cocycle representative
preserving both its original algebraic class and its exact continuous image
at the literal arithmetic image field. -/
theorem arithmeticOriginalStageContinuousClassH2_exists_finite_representative
    (x : arithmeticOriginalStageContinuousClassH2 Ω a ha L) :
    ∃ c : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L),
      groupCohomology.H2π _ c = continuousH2ToAlgebraic
        (arithmeticOriginalStageClassRep Ω a ha L) continuous_of_discreteTopology x ∧
      arithmeticOriginalStageContinuousClassH2Inflation Ω a ha L x =
        Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha
          (originalUnramifiedStageInUnion a L)
          (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L c)) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    refine ⟨c.val, rfl, ?_⟩
    change Submodule.Quotient.mk (arithmeticOriginalStageClassContinuousTwoCocycle Ω a ha L c.val) = _
    exact congrArg (continuousRepresentationCoboundariesTwo
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)).mkQ
        (arithmeticOriginalStageClassTwoCocycleToImage_continuous Ω a ha L c.val).symm

end
end Dubon2026
