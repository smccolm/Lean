import Dubon2026.OriginalContravariantHomSequence
import Dubon2026.OriginalInternalHomEvaluation
import Dubon2026.ContinuousAlgebraicConnecting
import Dubon2026.ContinuousShortComplexInvariantConnecting
import Dubon2026.ContinuousConnectingCupAdjunction
import Dubon2026.OriginalInvariantHomEvaluation

/-! # Cup adjunction for the literal internal-Hom dual sequence

Evaluation and precomposition discharge every pairing compatibility in the
existing continuous adjunction. Its arithmetic consumer uses the proved
S-unit integer Ext vanishing and actual restricted relation sequence on
the path from DUB-17's source duality to reverse localization.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : ShortComplex (Rep.{0} ℤ G)) (D : Rep.{0} ℤ G)
  [TopologicalSpace X.X₁] [DiscreteTopology X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃]
  [TopologicalSpace D] [DiscreteTopology D]
  [TopologicalSpace ((Rep.ihom X.X₃).obj D)]
  [DiscreteTopology ((Rep.ihom X.X₃).obj D)]
  [TopologicalSpace ((Rep.ihom X.X₂).obj D)]
  [DiscreteTopology ((Rep.ihom X.X₂).obj D)]
  [TopologicalSpace ((Rep.ihom X.X₁).obj D)]
  [DiscreteTopology ((Rep.ihom X.X₁).obj D)]
  (hX : X.ShortExact) (hY : (originalContravariantHomShortComplex X D).ShortExact)
  (hA : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hB : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))
  (hC : Continuous (fun z : G × X.X₃ => X.X₃.ρ z.1 z.2))
  (hU : Continuous (fun z : G × (Rep.ihom X.X₃).obj D =>
    ((Rep.ihom X.X₃).obj D).ρ z.1 z.2))
  (hV : Continuous (fun z : G × (Rep.ihom X.X₂).obj D =>
    ((Rep.ihom X.X₂).obj D).ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

local instance : @ContinuousSMul ℤ X.X₁ X.X₁.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ X.X₁ X.X₁.hV2.toSMul _ _ continuous_of_discreteTopology
local instance : @ContinuousSMul ℤ X.X₂ X.X₂.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ X.X₂ X.X₂.hV2.toSMul _ _ continuous_of_discreteTopology
local instance : @ContinuousSMul ℤ X.X₃ X.X₃.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ X.X₃ X.X₃.hV2.toSMul _ _ continuous_of_discreteTopology
local instance : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
local instance : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D)
    ((Rep.ihom X.X₃).obj D).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D)
    ((Rep.ihom X.X₃).obj D).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Literal evaluation makes the original relation connecting map adjoint
to the actual dual connecting map for continuous cup products. All
pairings and their precomposition identities are constructed here. -/
theorem originalDualRelationCup_adjunction
    (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants) :
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      (continuousShortComplexInvariantConnectingMap
        (originalContravariantHomShortComplex X D) hY hU hV w) := by
  let Y := originalContravariantHomShortComplex X D
  exact continuousConnectingCup_adjunction X.X₁ X.X₂ X.X₃ Y.X₁ Y.X₂ Y.X₃ D
    X.f.hom.toLinearMap ((Rep.mono_iff_injective X.f).mp hX.mono_f)
    (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap
    ((Rep.epi_iff_surjective X.g).mp hX.epi_g) (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))).moduleCat_range_eq_ker
    Y.f.hom.toLinearMap ((Rep.mono_iff_injective Y.f).mp hY.mono_f)
    (Rep.hom_comm_apply Y.f) Y.g.hom.toLinearMap
    ((Rep.epi_iff_surjective Y.g).mp hY.epi_g) (Rep.hom_comm_apply Y.g)
    (hY.exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))).moduleCat_range_eq_ker
    (originalInternalHomEvaluation X.X₁ D) (originalInternalHomEvaluation X.X₂ D)
    (originalInternalHomEvaluation X.X₃ D)
    (originalInternalHomEvaluation_equivariant X.X₁ D)
    (originalInternalHomEvaluation_equivariant X.X₂ D)
    (originalInternalHomEvaluation_equivariant X.X₃ D)
    (fun _ _ => rfl) (fun _ _ => rfl)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    hA hB hC hU hV hD x w

include hA hB in
/-- The continuous cup against the actual dual connecting class becomes
the original algebraic relation obstruction under the literal invariant
coefficient morphism. Both comparison maps are proved from the same cocycles. -/
theorem originalDualRelationCup_toAlgebraic
    (x : ContinuousRepresentationH1 X.X₃ hC)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants) :
    continuousH2ToAlgebraic D hD
      (continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D)
        (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology hC hU hD x
        (continuousShortComplexInvariantConnectingMap
          (originalContravariantHomShortComplex X D) hY hU hV w)) =
    groupCohomology.map (MonoidHom.id G) (originalInvariantHomMorphism X.X₁ D w) 2
      (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x)) := by
  rw [← originalDualRelationCup_adjunction X D hX hY hA hB hC hU hV hD x w,
    originalInvariantHomH2Evaluation_toAlgebraic,
    continuousShortComplexConnectingMap_toAlgebraic]

end
end Dubon2026
