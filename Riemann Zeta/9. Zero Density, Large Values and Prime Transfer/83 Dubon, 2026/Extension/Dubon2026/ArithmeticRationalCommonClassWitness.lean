import Dubon2026.ArithmeticClassStageCommonEquality
import Dubon2026.ArithmeticSourceRelationContinuousCupMaps

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance rationalCommonClassWitnessUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance rationalCommonClassWitnessFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance rationalCommonClassWitnessIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticRationalCommonClassWitnessLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology



/-- The proved common-field witness for the exact rational arithmetic
continuous H2 quotient used by the source cup. This specialization retains
both finite cocycles and every field inclusion in the generic theorem. -/
theorem rationalArithmeticClassStagesContinuousH2_eq_exists_common_finite_witness
    (E D : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep ℚ Ω a ha E))
    (d : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep ℚ Ω a ha D))
    (hcd : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha E c) :
      arithmeticSourceRelationContinuousH2 Ω a ha) =
      Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha D d)) :
    ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEM : E ≤ M, ∃ hDM : D ≤ M,
        groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E M hEM c) =
          groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha D M hDM d) := by
  exact @arithmeticClassStagesContinuousH2_eq_exists_common_finite_witness
    ℚ Ω Rat.instField omegaField Rat.numberField omegaAlgebra a ha stageDecidableEq
      targetTopology targetDiscrete E D c d hcd

end
end Dubon2026
