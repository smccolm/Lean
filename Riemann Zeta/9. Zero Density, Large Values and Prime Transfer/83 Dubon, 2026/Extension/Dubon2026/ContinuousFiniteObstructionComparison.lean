import Dubon2026.ContinuousH2GroupCoefficientComparison
import Dubon2026.ContinuousAlgebraicConnecting

/-! # Continuous finite obstructions retain their original algebraic class

Compose the existing same-cocycle comparisons once, before arithmetic
instantiation. This is the exact source-class bridge needed by DUB-17's
finite scalar criterion, without any forgetful-map injectivity assumption.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (π : G →* H) (hπ : Continuous π)
  (X : ShortComplex (Rep.{0} R H)) (hX : X.ShortExact)
  (C : Rep.{0} R H) (D : Rep.{0} R G)
  [TopologicalSpace X.X₁] [DiscreteTopology X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂] [ContinuousSMul R X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃] [ContinuousSMul R X.X₃]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  [TopologicalSpace D] [DiscreteTopology D] [ContinuousSMul R D]
  (hX₁ : Continuous (fun z : H × X.X₁ => X.X₁.ρ z.1 z.2))
  (hX₂ : Continuous (fun z : H × X.X₂ => X.X₂.ρ z.1 z.2))
  (hX₃ : Continuous (fun z : H × X.X₃ => X.X₃.ρ z.1 z.2))
  (hC : Continuous (fun z : H × C => C.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

/-- The actual continuous connecting obstruction has the literal algebraic
inflation of the same finite connecting class and original H1 input. -/
theorem continuousShortComplexObstruction_toAlgebraic
    (η : X.X₁ ⟶ C) (j : Rep.res π C ⟶ D)
    (x : ContinuousRepresentationH1 X.X₃ hX₃) :
    continuousH2ToAlgebraic D hD
      (continuousCoefficientH2Map (Rep.res π C) D j.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply j)
        (restrictedCoefficientAction_continuous C π hπ hC) hD
        (continuousRepresentationH2Restriction C hC π hπ
          (continuousCoefficientH2Map X.X₁ C η.hom.toLinearMap continuous_of_discreteTopology
            (Rep.hom_comm_apply η) hX₁ hC
            (continuousShortComplexConnectingMap X hX hX₁ hX₂ hX₃ x)))) =
      groupCohomology.map π j 2
        (groupCohomology.map (MonoidHom.id H) η 2
          (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hX₃ x))) := by
  rw [continuousH2_groupCoefficient_toAlgebraic, continuousH2Coefficient_toAlgebraic,
    continuousShortComplexConnectingMap_toAlgebraic]

end
end Dubon2026
