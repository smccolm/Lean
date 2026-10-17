import Dubon2026.ArithmeticClassesModOutsideColimit
import Dubon2026.ContinuousRepresentationCohomology

/-! # The literal continuous inflation of a finite arithmetic class cocycle

This fixes the finite representative whose continuous coboundary will be
descended when comparing the source-induced class with the enlarged scalar
obstruction. All field restrictions and coefficient inclusions are original.
-/
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
local instance arithmeticClassStageContinuousCocycleLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Inflate the same finite class two-cocycle along the actual arithmetic
restriction and literal coefficient-stage inclusion, with continuity proved. -/
def arithmeticClassStageContinuousTwoCocycle
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E)) :
    continuousRepresentationCocyclesTwo (arithmeticClassesModOutsideColimitRep K Ω a ha) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(E/K) :=
    AlgEquiv.restrictNormalHom E
  let j := coefficientRepresentationColimitOf (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E
  refine ⟨groupCohomology.mapCocycles₂ π j c, ?_⟩
  have hπ := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField
  exact (continuous_of_discreteTopology : Continuous (fun z : Gal(E/K) × Gal(E/K) =>
    j.hom (c z))).comp (hπ.prodMap hπ)

/-- The continuous representative retains every original finite class value. -/
theorem arithmeticClassStageContinuousTwoCocycle_apply
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E))
    (g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) :
    (arithmeticClassStageContinuousTwoCocycle K Ω a ha E c).val (g, h) =
      (coefficientRepresentationColimitOf (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom
          (c (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) := rfl

end
end Dubon2026
