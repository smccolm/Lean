import Dubon2026.ArithmeticSourceIdeleContinuousCup
import Dubon2026.ArithmeticOriginalStageContinuousClassRepresentative

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceIdeleScalarRepresentativeUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance sourceIdeleScalarRepresentativeFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance sourceIdeleScalarRepresentativeIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarRepresentativeLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


variable [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarRepresentativeLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology



variable (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
  [scalarTopology : TopologicalSpace (arithmeticOriginalStageClassRep Ω a ha L)]
  [scalarDiscrete : DiscreteTopology (arithmeticOriginalStageClassRep Ω a ha L)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleScalarRepresentativeLocalInstance3 : @ContinuousSMul ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul _ _ continuous_of_discreteTopology


/-- The exact scalar-stage continuous class representative also retains
the specified actual source-idele H2 image, using the supplied continuous
comparison. The source-cup theorem provides this comparison without a premise. -/
theorem arithmeticSourceIdeleH2_exists_scalar_class_representative
    (u : arithmeticSourceIdeleContinuousH2 Ω a ha)
    (x : arithmeticOriginalStageContinuousClassH2 Ω a ha L)
    (hux : arithmeticSourceIdeleContinuousH2ToClasses Ω a ha u =
      arithmeticOriginalStageContinuousClassH2Inflation Ω a ha L x) :
    ∃ s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L),
      groupCohomology.H2π _ s = continuousH2ToAlgebraic
        (arithmeticOriginalStageClassRep Ω a ha L) continuous_of_discreteTopology x ∧
      arithmeticSourceIdeleContinuousH2ToClasses Ω a ha u =
        Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha
          (originalUnramifiedStageInUnion a L)
          (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)) := by
  have hscalar := @arithmeticOriginalStageContinuousClassH2_exists_finite_representative
    Ω omegaField omegaAlgebra a ha stageDecidableEq targetTopology targetDiscrete L scalarTopology scalarDiscrete x
  let s := hscalar.choose
  have hs := hscalar.choose_spec.1
  have his := hscalar.choose_spec.2
  exact ⟨s, hs, hux.trans his⟩

end
end Dubon2026
