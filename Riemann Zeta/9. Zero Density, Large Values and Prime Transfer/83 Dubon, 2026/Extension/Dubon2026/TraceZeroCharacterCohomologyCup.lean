import Dubon2026.TraceZeroContinuousCharacterPairing
import Dubon2026.ContinuousCohomologyCup

/-! # The actual character-valued cup pairing on original trace-zero deformation classes -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ)

/-- The actual character-valued cup pairing. Its second input is the same original
trace-zero deformation H1, via the proved exact quotient comparison. -/
def matrixTraceZeroCharacterH1Cup :
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
        (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ) →ₗ[k]
      ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[k]
        ContinuousRepresentationH2 (coefficientCharacterRep χ)
          (coefficientCharacterAction_continuous χ hχ) :=
  (continuousH1Cup (matrixTraceZeroCharacterRep ρ χ) (matrixTraceZeroAdjointRep ρ)
    (coefficientCharacterRep χ) matrixTraceZeroTracePairing
    (matrixTraceZeroTracePairing_character_equivariant ρ χ)
    matrixTraceZeroTracePairing_continuous
    (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ)
    (matrixTraceZeroAdjointAction_continuous ρ hρ)
    (coefficientCharacterAction_continuous χ hχ)).compl₂
      (continuousTraceZeroH1GeneralEquiv ρ hρ).toLinearMap

/-- On the exact original continuous representatives, the pairing gives the class
of the genuine trace cup cocycle, preserving the original deformation class. -/
theorem matrixTraceZeroCharacterH1Cup_mk
    (f : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ))
    (u : continuousTraceZeroAdjointCocycles ρ) :
    matrixTraceZeroCharacterH1Cup ρ hρ χ hχ
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk
        (continuousOneCocycleCup (matrixTraceZeroCharacterRep ρ χ) (matrixTraceZeroAdjointRep ρ)
          (coefficientCharacterRep χ) matrixTraceZeroTracePairing
          (matrixTraceZeroTracePairing_character_equivariant ρ χ)
          matrixTraceZeroTracePairing_continuous (matrixTraceZeroAdjointAction_continuous ρ hρ)
          f (⟨u.val, u.property⟩ : continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ))) :
        ContinuousRepresentationH2 (coefficientCharacterRep χ)
          (coefficientCharacterAction_continuous χ hχ)) := by
  rfl

end
end Dubon2026
