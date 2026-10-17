import Dubon2026.ContinuousShortComplexGroupChange
import Dubon2026.ContinuousH2CoefficientRestrictionSquare

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (π : G →* H) (hπ : Continuous π)
  (X : ShortComplex (Rep.{0} R H)) (Y : ShortComplex (Rep.{0} R G))
  (d : (Rep.resFunctor π).mapShortComplex.obj X ⟶ Y)
  (hX : X.ShortExact) (hY : Y.ShortExact)
  [TopologicalSpace X.X₁] [DiscreteTopology X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂] [ContinuousSMul R X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃] [ContinuousSMul R X.X₃]
  [TopologicalSpace Y.X₁] [DiscreteTopology Y.X₁] [ContinuousSMul R Y.X₁]
  [TopologicalSpace Y.X₂] [DiscreteTopology Y.X₂] [ContinuousSMul R Y.X₂]
  [TopologicalSpace Y.X₃] [DiscreteTopology Y.X₃] [ContinuousSMul R Y.X₃]
  (hX₁ : Continuous (fun z : H × X.X₁ => X.X₁.ρ z.1 z.2))
  (hX₂ : Continuous (fun z : H × X.X₂ => X.X₂.ρ z.1 z.2))
  (hX₃ : Continuous (fun z : H × X.X₃ => X.X₃.ρ z.1 z.2))
  (hY₁ : Continuous (fun z : G × Y.X₁ => Y.X₁.ρ z.1 z.2))
  (hY₂ : Continuous (fun z : G × Y.X₂ => Y.X₂.ρ z.1 z.2))
  (hY₃ : Continuous (fun z : G × Y.X₃ => Y.X₃.ρ z.1 z.2))

variable (C : Rep.{0} R H) (D : Rep.{0} R G)
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  [TopologicalSpace D] [DiscreteTopology D] [ContinuousSMul R D]
  (hC : Continuous (fun z : H × C => C.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

/-- A literal relation diagram and coefficient square identify the original
continuous connecting obstruction with its finite-stage image. -/
theorem continuousShortComplex_obstruction_square
    (η : X.X₁ ⟶ C) (j : Rep.res π C ⟶ D) (φ : Y.X₁ ⟶ D)
    (hs : (Rep.resFunctor π).map η ≫ j = d.τ₁ ≫ φ)
    (x : ContinuousRepresentationH1 X.X₃ hX₃) :
    continuousCoefficientH2Map Y.X₁ D φ.hom.toLinearMap continuous_of_discreteTopology
      (Rep.hom_comm_apply φ) hY₁ hD
      (continuousShortComplexConnectingMap Y hY hY₁ hY₂ hY₃
        (continuousCoefficientH1Map (Rep.res π X.X₃) Y.X₃ d.τ₃.hom.toLinearMap
          continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₃)
          (restrictedCoefficientAction_continuous X.X₃ π hπ hX₃) hY₃
          (continuousRepresentationH1Restriction X.X₃ hX₃ π hπ x))) =
    continuousCoefficientH2Map (Rep.res π C) D j.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply j)
      (restrictedCoefficientAction_continuous C π hπ hC) hD
      (continuousRepresentationH2Restriction C hC π hπ
        (continuousCoefficientH2Map X.X₁ C η.hom.toLinearMap continuous_of_discreteTopology
          (Rep.hom_comm_apply η) hX₁ hC
          (continuousShortComplexConnectingMap X hX hX₁ hX₂ hX₃ x))) := by
  rw [← continuousShortComplexConnectingMap_groupChange π hπ X Y d hX hY
    hX₁ hX₂ hX₃ hY₁ hY₂ hY₃]
  exact continuousH2_coefficient_restriction_square π hπ X.X₁ C Y.X₁ D hX₁ hC hY₁ hD
    d.τ₁ η j φ hs (continuousShortComplexConnectingMap X hX hX₁ hX₂ hX₃ x)

end
end Dubon2026
