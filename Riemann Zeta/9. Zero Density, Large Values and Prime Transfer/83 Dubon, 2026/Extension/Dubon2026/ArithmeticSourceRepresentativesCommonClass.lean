import Dubon2026.ArithmeticSourceIdeleContinuousCup
import Dubon2026.ArithmeticOriginalStageClassCocycleImage
import Dubon2026.ArithmeticRationalCommonClassWitness

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceRepresentativesCommonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance sourceRepresentativesCommonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance sourceRepresentativesCommonIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceRepresentativesCommonClassLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


variable [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceRepresentativesCommonClassLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology



/-- The actual source and scalar representatives with their retained
continuous images acquire a common finite comparison field. Representative
choice and scalar-obstruction construction are discharged by the caller;
the finite equality is derived from the proved continuous descent theorem. -/
theorem arithmeticSourceIdeleRepresentatives_exists_common_finite_class
    (u : arithmeticSourceIdeleContinuousH2 Ω a ha)
    (w : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω a ha))
    (hw : Submodule.Quotient.mk w = u)
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E))
    (hclass : arithmeticSourceIdeleContinuousH2ToClasses Ω a ha (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha E
        (groupCohomology.mapCocycles₂
            (A := ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)
            (B := arithmeticClassesModOutsideStageRep ℚ Ω a ha E)
            (MonoidHom.id Gal(E/ℚ))
          (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
            arithmeticSourceClassStageComparison ℚ Ω a ha E) d)))
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L))
    (his : arithmeticSourceIdeleContinuousH2ToClasses Ω a ha u =
      Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha
        (originalUnramifiedStageInUnion a L)
        (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s))) :
    ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEM : E ≤ M, ∃ hLM : originalUnramifiedStageInUnion a L ≤ M,
        groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E M hEM
          (groupCohomology.mapCocycles₂
            (A := ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)
            (B := arithmeticClassesModOutsideStageRep ℚ Ω a ha E)
            (MonoidHom.id Gal(E/ℚ))
            (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
              arithmeticSourceClassStageComparison ℚ Ω a ha E) d)) =
        groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
          (originalUnramifiedStageInUnion a L) M hLM
          (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)) := by
  have hmap := congrArg (@arithmeticSourceIdeleContinuousH2ToClasses
    Ω omegaField omegaAlgebra a ha stageDecidableEq
      sourceTopology sourceDiscrete targetTopology targetDiscrete) hw
  have hglobal := hclass.symm.trans (hmap.trans his)
  exact @rationalArithmeticClassStagesContinuousH2_eq_exists_common_finite_witness
    Ω omegaField omegaAlgebra a ha stageDecidableEq targetTopology targetDiscrete
    E (originalUnramifiedStageInUnion a L)
    (groupCohomology.mapCocycles₂
            (A := ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)
            (B := arithmeticClassesModOutsideStageRep ℚ Ω a ha E)
            (MonoidHom.id Gal(E/ℚ))
      (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
        arithmeticSourceClassStageComparison ℚ Ω a ha E) d)
    (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s) hglobal

end
end Dubon2026
