import Dubon2026.ContinuousTrivialDualCoordinates

/-! # Split-module right annihilators reduce to the actual scalar cup

The original dual coordinates and cup naturality transfer the scalar right
annihilator result to the split finite module required by DUB-17 local duality.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G ι : Type} [Field k] [Finite k] [Group G] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))


include b htrivial in
/-- Scalar right nondegeneracy forces the original split-module right
annihilator to vanish. Every original dual basis coordinate is derived from
an actual scalar cup test, and coordinate boundaries reconstruct the class. -/
theorem continuousTrivialCharacterDualH1Cup_right_zero
    (hbase : Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : G →* k)) χ hχ
      (coefficientCharacterAction_continuous (1 : G →* k) continuous_const)).flip)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup A χ hχ hA x y = 0) : y = 0 := by
  apply continuousScalarH1_eq_zero_of_coordinates (characterDualCoefficientRep A χ) χ b.dualBasis
    (trivialCoefficient_characterDual_scalar A χ htrivial)
    (finiteCharacterDualAction_continuous A χ hA hχ) hχ y
  intro i
  have hz : continuousCoefficientH1Map (characterDualCoefficientRep A χ)
      (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)
      (characterDualCoefficientMap (coefficientCharacterRep (1 : G →* k)) A χ
        (LinearMap.toSpanSingleton k A (b i))) continuous_of_discreteTopology
      (characterDualCoefficientMap_equivariant (coefficientCharacterRep (1 : G →* k)) A χ
        (LinearMap.toSpanSingleton k A (b i)) (trivialCoefficientBasisVector_equivariant A b htrivial i))
      (finiteCharacterDualAction_continuous A χ hA hχ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : G →* k)) χ
        (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) hχ) y = 0 := by
    apply hbase
    apply LinearMap.ext
    intro x
    rw [map_zero, LinearMap.zero_apply]
    exact (continuousCharacterDualH1Cup_naturality
      (coefficientCharacterRep (1 : G →* k)) χ hχ
      (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) A hA
      (LinearMap.toSpanSingleton k A (b i)) (trivialCoefficientBasisVector_equivariant A b htrivial i)
      x y).trans (hy _)
  rw [continuousCharacterDualBasisCoordinate_evaluation A χ hχ b htrivial hA i y,
    hz, map_zero]

end
end Dubon2026
