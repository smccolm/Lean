import Dubon2026.TraceZeroCharacterCohomologyCup
import Dubon2026.ContinuousCharacterBidualCup

/-! # The original matrix trace cup and the actual character-dual cup

The existing coefficient trace duality induces the genuine continuous H1
identification. The original trace cup has the reversed order of the dual cup;
the proved degree-one skew identity supplies its exact negative sign. This is
the coefficient-to-deformation bridge for DUB-17's local Selmer pairing.
-/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] characterDualSequenceContinuousSMul

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (hn : (Fintype.card ι : k) ≠ 0)
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)]

/-- The actual continuous twisted trace-zero classes are the original
character-dual classes, using the proved literal matrix trace identification. -/
def matrixTraceZeroCharacterDualH1Equiv :
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ) ≃+
    ContinuousRepresentationH1 (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)
      (finiteCharacterDualAction_continuous (matrixTraceZeroAdjointRep ρ) χ
        (matrixTraceZeroAdjointAction_continuous ρ hρ) hχ) :=
  continuousH1AdditiveCoefficientEquiv _ _
    (matrixTraceZeroCharacterDuality hn ρ χ).toLinearEquiv.toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (matrixTraceZeroCharacterDuality hn ρ χ).toIntertwiningMap.isIntertwining _ _

/-- The literal original deformation trace cup equals the negative original
character-dual cup with the actual H1 arguments exchanged. -/
theorem matrixTraceZeroCharacterH1Cup_dual
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y =
      -continuousCharacterDualH1Cup (matrixTraceZeroAdjointRep ρ) χ hχ
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (continuousTraceZeroH1GeneralEquiv ρ hρ y)
        (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x) := by
  have hp : matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y =
      continuousH1Cup (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)
        (matrixTraceZeroAdjointRep ρ) (coefficientCharacterRep χ)
        (characterDualEvaluation (matrixTraceZeroAdjointRep ρ) χ).flip
        (fun g u a => characterDualEvaluation_equivariant (matrixTraceZeroAdjointRep ρ) χ g a u)
        continuous_of_discreteTopology
        (finiteCharacterDualAction_continuous (matrixTraceZeroAdjointRep ρ) χ
          (matrixTraceZeroAdjointAction_continuous ρ hρ) hχ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (coefficientCharacterAction_continuous χ hχ)
        (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x)
        (continuousTraceZeroH1GeneralEquiv ρ hρ y) := by
    induction x using Submodule.Quotient.induction_on with
    | _ c =>
      induction y using Submodule.Quotient.induction_on with
      | _ u =>
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        apply Subtype.ext
        funext z
        exact (matrixTraceZeroCharacterDuality_apply hn ρ χ
          (c.val z.1) ((matrixTraceZeroAdjointRep ρ).ρ z.1 (u.val z.2))).symm
  exact hp.trans (continuousH1Cup_skew
    (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ)
    (matrixTraceZeroAdjointRep ρ) (coefficientCharacterRep χ)
    (characterDualEvaluation (matrixTraceZeroAdjointRep ρ) χ).flip
    (fun g u a => characterDualEvaluation_equivariant (matrixTraceZeroAdjointRep ρ) χ g a u)
    continuous_of_discreteTopology
    (finiteCharacterDualAction_continuous (matrixTraceZeroAdjointRep ρ) χ
      (matrixTraceZeroAdjointAction_continuous ρ hρ) hχ)
    (matrixTraceZeroAdjointAction_continuous ρ hρ)
    (coefficientCharacterAction_continuous χ hχ)
    (matrixTraceZeroCharacterDualH1Equiv hn ρ hρ χ hχ x)
    (continuousTraceZeroH1GeneralEquiv ρ hρ y))

end
end Dubon2026
