import Dubon2026.ArithmeticSourceIdeleContinuousFiniteRepresentative
import Dubon2026.ArithmeticSourceRepresentativesCommonClass
import Dubon2026.ArithmeticOriginalStageContinuousClassRepresentative
import Dubon2026.ArithmeticSourceIdeleH2Representative
import Dubon2026.ArithmeticSourceIdeleScalarRepresentative

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceIdeleCommonClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance sourceIdeleCommonClassFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance sourceIdeleCommonClassIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteClassWitnessLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


variable [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteClassWitnessLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology



variable (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
  [scalarTopology : TopologicalSpace (arithmeticOriginalStageClassRep Ω a ha L)]
  [scalarDiscrete : DiscreteTopology (arithmeticOriginalStageClassRep Ω a ha L)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteClassWitnessLocalInstance3 : @ContinuousSMul ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticOriginalStageClassRep Ω a ha L)
    (arithmeticOriginalStageClassRep Ω a ha L).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Equality of the actual continuous source-idele image and a finite
original class constructs original representatives with equal finite H2
images in one arithmetic field. The scalar-cup application discharges the
continuous equality using its proved source relation comparison. -/
theorem arithmeticSourceIdeleH2_exists_common_finite_class
    (u : arithmeticSourceIdeleContinuousH2 Ω a ha)
    (x : arithmeticOriginalStageContinuousClassH2 Ω a ha L)
    (hux : arithmeticSourceIdeleContinuousH2ToClasses Ω a ha u =
      arithmeticOriginalStageContinuousClassH2Inflation Ω a ha L x) :
    ∃ w : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω a ha),
      (Submodule.Quotient.mk w : arithmeticSourceIdeleContinuousH2 Ω a ha) = u ∧
      ∃ E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E),
          (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
            (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
              (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) E).hom
                (d (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) = w.val (g, h)) ∧
          ∃ s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L),
            groupCohomology.H2π _ s = continuousH2ToAlgebraic
              (arithmeticOriginalStageClassRep Ω a ha L) continuous_of_discreteTopology x ∧
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
  have hwExists := @arithmeticSourceIdeleH2_exists_cocycle
    Ω omegaField omegaAlgebra a ha stageDecidableEq sourceTopology sourceDiscrete u
  refine hwExists.elim ?_
  intro w hw
  refine ⟨w, hw, ?_⟩
  have hsource := @arithmeticSourceIdeleContinuousH2_exists_finite_class_representative
    Ω omegaField omegaAlgebra a ha stageDecidableEq sourceTopology sourceDiscrete targetTopology targetDiscrete w
  refine hsource.elim ?_
  intro E hE
  refine hE.elim ?_
  intro d hd
  refine ⟨E, d, hd.1, ?_⟩
  have hscalar := @arithmeticSourceIdeleH2_exists_scalar_class_representative
    Ω omegaField omegaAlgebra a ha stageDecidableEq sourceTopology sourceDiscrete
      targetTopology targetDiscrete L scalarTopology scalarDiscrete u x hux
  refine hscalar.elim ?_
  intro s hs
  refine ⟨s, hs.1, ?_⟩
  exact @arithmeticSourceIdeleRepresentatives_exists_common_finite_class
    Ω omegaField omegaAlgebra a ha stageDecidableEq sourceTopology sourceDiscrete
      targetTopology targetDiscrete u w hw E d hd.2 L s hs.2

end
end Dubon2026
