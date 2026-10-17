import Dubon2026.OriginalRelationCupExplicitLift

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

include hA hB hV in
/-- The actual source-cocycle lift identifies the cup with the literal
coefficient image of the connecting class in continuous H2 itself. -/
theorem originalRelationCup_explicit_lift_continuous
    (x : ContinuousRepresentationH1 X.X₃ hC)
    (u : continuousRepresentationCocyclesOne ((Rep.ihom X.X₃).obj D))
    (v : (Rep.ihom X.X₂).obj D) (φ : X.X₁ ⟶ D)
    (hu : ∀ g, ((Rep.ihom X.X₂).obj D).ρ g v - v =
      (originalInternalHomPrecomposition D X.g).hom (u.val g))
    (hφ : φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] D from v).comp X.f.hom.toLinearMap) :
    continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
      (originalInternalHomEvaluation X.X₃ D)
      (originalInternalHomEvaluation_equivariant X.X₃ D)
      continuous_of_discreteTopology hC hU hD x
      ((continuousRepresentationCoboundariesOne ((Rep.ihom X.X₃).obj D) hU).mkQ u) =
    continuousCoefficientH2Map X.X₁ D φ.hom.toLinearMap continuous_of_discreteTopology
      (Rep.hom_comm_apply φ) hA hD
      (continuousShortComplexConnectingMap X hX hA hB hC x) := by
  let w : ((Rep.ihom X.X₁).obj D).ρ.invariants :=
    ⟨φ.hom.toLinearMap, originalMorphism_internalHom_invariant X.X₁ D φ⟩
  have hw : (originalInternalHomPrecomposition D X.f).hom v = w.val := hφ.symm
  exact (originalRelationCup_explicit_lift X D hX hA hB hC hU hV hD x u v w hu hw).symm

end
end Dubon2026
