import Dubon2026.OriginalContravariantHomSequence
import Dubon2026.OriginalInternalHomEvaluation
import Dubon2026.ContinuousAlgebraicConnecting
import Dubon2026.ContinuousShortComplexInvariantConnecting
import Dubon2026.ContinuousConnectingCupExplicitLift
import Dubon2026.OriginalInternalHomNormQuotient
import Dubon2026.OriginalInvariantHomEvaluation

/-! # Original relation cup from the constructed free-cover lift

The source-class representative already includes the required lift. Literal
evaluation therefore identifies its cup with the original relation connecting
obstruction, without proving or assuming class-target integer Ext vanishing.
This is the exact continuous-to-algebraic edge in DUB-17 reverse localization.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
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
  (hX : X.ShortExact)
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

include hV in
/-- The cup with an actual continuous Hom cocycle equals evaluation of the
original relation connecting class whenever the specified free-cover lift
has that cocycle as boundary. -/
theorem originalRelationCup_explicit_lift
    (x : ContinuousRepresentationH1 X.X₃ hC)
    (u : continuousRepresentationCocyclesOne ((Rep.ihom X.X₃).obj D))
    (v : (Rep.ihom X.X₂).obj D)
    (w : ((Rep.ihom X.X₁).obj D).ρ.invariants)
    (hu : ∀ g, ((Rep.ihom X.X₂).obj D).ρ g v - v =
      (originalInternalHomPrecomposition D X.g).hom (u.val g))
    (hw : (originalInternalHomPrecomposition D X.f).hom v = w.val) :
    continuousInvariantRightH2Map X.X₁ ((Rep.ihom X.X₁).obj D) D
      (originalInternalHomEvaluation X.X₁ D)
      (originalInternalHomEvaluation_equivariant X.X₁ D)
      continuous_of_discreteTopology hA hD w
      (continuousShortComplexConnectingMap X hX hA hB hC x) =
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x ((continuousRepresentationCoboundariesOne ((Rep.ihom X.X₃).obj D) hU).mkQ u) := by
  let Y := originalContravariantHomShortComplex X D
  exact continuousConnectingCup_explicit_lift X.X₁ X.X₂ X.X₃ Y.X₁ Y.X₂ Y.X₃ D
    X.f.hom.toLinearMap ((Rep.mono_iff_injective X.f).mp hX.mono_f)
    (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap
    ((Rep.epi_iff_surjective X.g).mp hX.epi_g) (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))).moduleCat_range_eq_ker
    Y.f.hom.toLinearMap (Rep.hom_comm_apply Y.f)
    Y.g.hom.toLinearMap (Rep.hom_comm_apply Y.g)
    (originalInternalHomEvaluation X.X₁ D) (originalInternalHomEvaluation X.X₂ D)
    (originalInternalHomEvaluation X.X₃ D)
    (originalInternalHomEvaluation_equivariant X.X₁ D)
    (originalInternalHomEvaluation_equivariant X.X₂ D)
    (originalInternalHomEvaluation_equivariant X.X₃ D)
    (fun _ _ => rfl) (fun _ _ => rfl)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    hA hB hC hU hV hD x w u v (fun g => (hu g).symm) hw

include hA hB hV in
/-- The same actual continuous cup maps to the algebraic relation obstruction
under the literal relation morphism determined by its free-cover lift. -/
theorem originalRelationCup_explicit_lift_toAlgebraic
    (x : ContinuousRepresentationH1 X.X₃ hC)
    (u : continuousRepresentationCocyclesOne ((Rep.ihom X.X₃).obj D))
    (v : (Rep.ihom X.X₂).obj D) (φ : X.X₁ ⟶ D)
    (hu : ∀ g, ((Rep.ihom X.X₂).obj D).ρ g v - v =
      (originalInternalHomPrecomposition D X.g).hom (u.val g))
    (hφ : φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] D from v).comp X.f.hom.toLinearMap) :
    continuousH2ToAlgebraic D hD
      (continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D)
        (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology hC hU hD x ((continuousRepresentationCoboundariesOne ((Rep.ihom X.X₃).obj D) hU).mkQ u)) =
    groupCohomology.map (MonoidHom.id G) φ 2
      (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hC x)) := by
  let w : ((Rep.ihom X.X₁).obj D).ρ.invariants :=
    ⟨φ.hom.toLinearMap, originalMorphism_internalHom_invariant X.X₁ D φ⟩
  have hw : (originalInternalHomPrecomposition D X.f).hom v = w.val := hφ.symm
  have he : originalInvariantHomMorphism X.X₁ D w = φ := by
    ext z
    rfl
  rw [← originalRelationCup_explicit_lift X D hX hA hB hC hU hV hD x u v w hu hw,
    originalInvariantHomH2Evaluation_toAlgebraic,
    continuousShortComplexConnectingMap_toAlgebraic, he]

end
end Dubon2026
