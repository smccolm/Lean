import Dubon2026.TraceZeroTwistedActionContinuity
import Dubon2026.ContinuousAdjointGeneralComparison

/-! # The genuine continuous trace pairing with the original character coefficient module -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k]

/-- The original trace-zero coefficient representation with its actual scalar
character twist, as an object of the original representation category. -/
abbrev matrixTraceZeroCharacterRep (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) : Rep k G :=
  Rep.of (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ)

/-- The actual one-dimensional character coefficient representation. -/
abbrev coefficientCharacterRep (χ : G →* k) : Rep k G :=
  Rep.of (coefficientCharacterTwist (1 : Representation k G k) χ)

/-- The literal original trace pairing is jointly continuous on the actual
trace-zero matrix coefficient spaces. -/
theorem matrixTraceZeroTracePairing_continuous :
    Continuous (fun z : matrixTraceZeroSubmodule ι k × matrixTraceZeroSubmodule ι k =>
      matrixTraceZeroTracePairing z.1 z.2) := by
  exact ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).matrix_trace

omit [IsTopologicalGroup G] in
/-- The actual cyclotomic-type coefficient module has jointly continuous action
for every genuine continuous character, with its original scalar topology. -/
theorem coefficientCharacterAction_continuous (χ : G →* k) (hχ : Continuous χ) :
    Continuous (fun z : G × k => (coefficientCharacterRep χ).ρ z.1 z.2) := by
  exact (hχ.comp continuous_fst).mul continuous_snd

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k] [IsTopologicalRing k] in
/-- The literal trace pairing is equivariant into the original character module.
This identity needs no nonzero-dimension assumption or arithmetic perfectness. -/
theorem matrixTraceZeroTracePairing_character_equivariant
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (g : G)
    (X Y : matrixTraceZeroSubmodule ι k) :
    matrixTraceZeroTracePairing ((matrixTraceZeroCharacterRep ρ χ).ρ g X)
        ((matrixTraceZeroAdjointRep ρ).ρ g Y) =
      (coefficientCharacterRep χ).ρ g (matrixTraceZeroTracePairing X Y) := by
  exact matrixTraceZeroCharacterPairing_equivariant ρ χ g X Y

end
end Dubon2026
