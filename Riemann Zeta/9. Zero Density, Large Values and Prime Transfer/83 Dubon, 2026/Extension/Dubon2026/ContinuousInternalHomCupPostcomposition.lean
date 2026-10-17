import Dubon2026.OriginalInternalHomEvaluation
import Dubon2026.ContinuousCohomologyCup
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Source idele-to-class evaluation cup comparison

Postcomposition by the actual source quotient carries the original
evaluation cup to the class evaluation cup. This is the required
source-induced idele image statement on DUB-17's normalized pairing chain;
it does not claim surjectivity on arbitrary full-class H2.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A J C : Rep.{0} ℤ G)
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace J] [DiscreteTopology J]
  [TopologicalSpace C] [DiscreteTopology C]
  [TopologicalSpace ((Rep.ihom A).obj J)] [DiscreteTopology ((Rep.ihom A).obj J)]
  [TopologicalSpace ((Rep.ihom A).obj C)] [DiscreteTopology ((Rep.ihom A).obj C)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hJ : Continuous (fun z : G × J => J.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (hU : Continuous (fun z : G × (Rep.ihom A).obj J => ((Rep.ihom A).obj J).ρ z.1 z.2))
  (hV : Continuous (fun z : G × (Rep.ihom A).obj C => ((Rep.ihom A).obj C).ρ z.1 z.2))

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance continuousInternalHomCupPostcompositionLocalInstance1 : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance continuousInternalHomCupPostcompositionLocalInstance2 : @ContinuousSMul ℤ J J.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ J J.hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance continuousInternalHomCupPostcompositionLocalInstance3 : @ContinuousSMul ℤ C C.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ C C.hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance continuousInternalHomCupPostcompositionLocalInstance4 : @ContinuousSMul ℤ ((Rep.ihom A).obj J) ((Rep.ihom A).obj J).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.ihom A).obj J) ((Rep.ihom A).obj J).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance continuousInternalHomCupPostcompositionLocalInstance5 : @ContinuousSMul ℤ ((Rep.ihom A).obj C) ((Rep.ihom A).obj C).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.ihom A).obj C) ((Rep.ihom A).obj C).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The same evaluation cup commutes with the actual coefficient quotient
and its literal Hom postcomposition map, in continuous H2 itself. -/
theorem continuousInternalHomH1Cup_postcomposition
    (q : J ⟶ C) (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 ((Rep.ihom A).obj J) hU) :
    continuousCoefficientH2Map J C q.hom.toLinearMap continuous_of_discreteTopology
      (Rep.hom_comm_apply q) hJ hC
      (continuousH1Cup A ((Rep.ihom A).obj J) J (originalInternalHomEvaluation A J)
        (originalInternalHomEvaluation_equivariant A J) continuous_of_discreteTopology hA hU hJ x y) =
    continuousH1Cup A ((Rep.ihom A).obj C) C (originalInternalHomEvaluation A C)
      (originalInternalHomEvaluation_equivariant A C) continuous_of_discreteTopology hA hV hC x
      (continuousCoefficientH1Map ((Rep.ihom A).obj J) ((Rep.ihom A).obj C)
        ((Rep.ihom A).map q).hom.toLinearMap continuous_of_discreteTopology
        (Rep.hom_comm_apply ((Rep.ihom A).map q)) hU hV y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      rw [continuousH1Cup_mk, continuousCoefficientH2Map_mk,
        continuousCoefficientH1Map_mk, continuousH1Cup_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext gh
      change q.hom (originalInternalHomEvaluation A J (c.val gh.1)
          (((Rep.ihom A).obj J).ρ gh.1 (u.val gh.2))) =
        originalInternalHomEvaluation A C (c.val gh.1)
          (((Rep.ihom A).obj C).ρ gh.1 (((Rep.ihom A).map q).hom (u.val gh.2)))
      rw [← Rep.hom_comm_apply ((Rep.ihom A).map q)]
      rfl

end
end Dubon2026
