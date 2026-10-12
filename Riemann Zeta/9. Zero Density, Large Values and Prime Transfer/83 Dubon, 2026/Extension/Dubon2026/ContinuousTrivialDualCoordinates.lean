import Dubon2026.TrivialCharacterDualCoordinates
import Dubon2026.ContinuousCharacterDualCupNaturality

/-! # Actual split dual H1 coordinates are scalar dual tests

The coefficient identity descends to the original continuous H1 quotient.
It identifies each dual basis coordinate with actual precomposition and
evaluation, the remaining coordinate step for DUB-17's split right annihilator.
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

/-- Each original dual H1 coordinate is exactly evaluation of the original
scalar dual test obtained by precomposition with the same basis-vector inclusion. -/
theorem continuousCharacterDualBasisCoordinate_evaluation (i : ι)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousCoefficientH1Map (characterDualCoefficientRep A χ) (coefficientCharacterRep χ)
      (b.dualBasis.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant (characterDualCoefficientRep A χ) χ b.dualBasis
        (trivialCoefficient_characterDual_scalar A χ htrivial) i)
      (finiteCharacterDualAction_continuous A χ hA hχ) (coefficientCharacterAction_continuous χ hχ) y =
    continuousCoefficientH1Map (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)
      (coefficientCharacterRep χ) (characterDualTrivialLineEquiv χ).toLinearMap
      continuous_of_discreteTopology (characterDualTrivialLineEquiv_equivariant χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : G →* k)) χ
        (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) hχ)
      (coefficientCharacterAction_continuous χ hχ)
      (continuousCoefficientH1Map (characterDualCoefficientRep A χ)
        (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)
        (characterDualCoefficientMap (coefficientCharacterRep (1 : G →* k)) A χ
          (LinearMap.toSpanSingleton k A (b i))) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant (coefficientCharacterRep (1 : G →* k)) A χ
          (LinearMap.toSpanSingleton k A (b i)) (trivialCoefficientBasisVector_equivariant A b htrivial i))
        (finiteCharacterDualAction_continuous A χ hA hχ)
        (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : G →* k)) χ
          (coefficientCharacterAction_continuous (1 : G →* k) continuous_const) hχ) y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoefficientH1Map_mk, continuousCoefficientH1Map_mk, continuousCoefficientH1Map_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact (characterDualBasisCoordinate_evaluation A χ b i (c.val g)).symm

end
end Dubon2026
