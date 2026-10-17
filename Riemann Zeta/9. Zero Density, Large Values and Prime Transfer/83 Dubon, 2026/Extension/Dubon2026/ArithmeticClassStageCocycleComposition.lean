import Dubon2026.ArithmeticClassStageCocycleTransition
import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticClassStageCocycleCompositionLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- The original finite coefficient inclusion and surjective Galois
restriction make continuous inflation injective on actual two-cocycles. -/
theorem arithmeticClassStageContinuousTwoCocycle_injective
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Function.Injective (arithmeticClassStageContinuousTwoCocycle K Ω a ha E) := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  intro c d hcd
  apply Subtype.ext
  funext st
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
    (originalUnramifiedGaloisUnion (Ω := Ω) a) st.1
  obtain ⟨h, hh⟩ := AlgEquiv.restrictNormalHom_surjective
    (originalUnramifiedGaloisUnion (Ω := Ω) a) st.2
  apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha E
  have hv := congrArg (fun z : continuousRepresentationCocyclesTwo
    (arithmeticClassesModOutsideColimitRep K Ω a ha) => z.val (g, h)) hcd
  change (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom
      (c (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) =
    (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom
      (d (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) at hv
  simpa only [hg, hh] using hv

/-- Successive literal finite cocycle transitions agree with the direct
transition. This allows equality descended above a common stage to be
stated directly for the two original finite representatives. -/
theorem arithmeticClassStageTwoCocycleTransition_comp
    (E F M : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFM : F ≤ M)
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E)) :
    arithmeticClassStageTwoCocycleTransition K Ω a ha F M hFM
      (arithmeticClassStageTwoCocycleTransition K Ω a ha E F hEF c) =
        arithmeticClassStageTwoCocycleTransition K Ω a ha E M (hEF.trans hFM) c := by
  apply arithmeticClassStageContinuousTwoCocycle_injective K Ω a ha M
  exact (arithmeticClassStageContinuousTwoCocycle_transition K Ω a ha F M hFM _).trans
    ((arithmeticClassStageContinuousTwoCocycle_transition K Ω a ha E F hEF c).trans
      (arithmeticClassStageContinuousTwoCocycle_transition K Ω a ha E M (hEF.trans hFM) c).symm)

end
end Dubon2026
