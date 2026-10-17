import Dubon2026.ContinuousFiniteObstructionComparison

/-! # The finite coefficient obstruction preserves its original class

This is the finite, before-inflation part of the existing continuous
obstruction comparison. It is instantiated at the original scalar relation
to retain the exact algebraic obstruction, avoiding a global H2 injectivity
assumption in DUB-17's source-cup comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : ShortComplex (Rep.{0} R G)) (hX : X.ShortExact) (C : Rep.{0} R G)
  [TopologicalSpace X.X₁] [DiscreteTopology X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂] [ContinuousSMul R X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃] [ContinuousSMul R X.X₃]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (hX₁ : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hX₂ : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))
  (hX₃ : Continuous (fun z : G × X.X₃ => X.X₃.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- The actual continuous coefficient image of the connecting class
forgets to the coefficient image of the original algebraic connecting class. -/
theorem continuousShortComplexCoefficientObstruction_toAlgebraic
    (η : X.X₁ ⟶ C) (x : ContinuousRepresentationH1 X.X₃ hX₃) :
    continuousH2ToAlgebraic C hC
      (continuousCoefficientH2Map X.X₁ C η.hom.toLinearMap continuous_of_discreteTopology
        (Rep.hom_comm_apply η) hX₁ hC
        (continuousShortComplexConnectingMap X hX hX₁ hX₂ hX₃ x)) =
      groupCohomology.map (MonoidHom.id G) η 2
        (groupCohomology.δ hX 1 2 rfl (continuousH1ToAlgebraic X.X₃ hX₃ x)) := by
  rw [continuousH2Coefficient_toAlgebraic, continuousShortComplexConnectingMap_toAlgebraic]

end
end Dubon2026
