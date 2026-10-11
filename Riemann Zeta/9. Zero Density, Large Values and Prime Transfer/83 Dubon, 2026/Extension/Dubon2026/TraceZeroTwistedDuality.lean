import Dubon2026.CoefficientCharacterTwist
import Dubon2026.TraceZeroAdjointDuality

/-! # The original trace-zero adjoint identifies its genuine character-valued dual -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Use the proved trace self-duality and the same actual character to identify
the twisted trace-zero adjoint with linear maps into the character representation. -/
def matrixTraceZeroCharacterDuality (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (χ : G →* K) :
    Representation.Equiv (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ)
      (Representation.linHom (matrixTraceZeroAdjointRepresentation ρ)
        (coefficientCharacterTwist (1 : Representation K G K) χ)) := by
  rw [← coefficientCharacterTwist_dual_eq_linHom]
  exact coefficientCharacterTwistEquiv (matrixTraceZeroAdjointTraceDuality hn ρ) χ

/-- The equivalence uses the literal trace pairing on the original matrices.
Twisting changes the action, not the underlying evaluation pairing. -/
theorem matrixTraceZeroCharacterDuality_apply (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (χ : G →* K)
    (X Y : matrixTraceZeroSubmodule ι K) :
    matrixTraceZeroCharacterDuality hn ρ χ X Y = Matrix.trace (X.val * Y.val) := by
  rfl

/-- The actual original trace pairing is character-equivariant for the untwisted
and twisted trace-zero actions, the coefficient identity needed for a Tate pairing. -/
theorem matrixTraceZeroCharacterPairing_equivariant
    (ρ : G →* GeneralLinearGroup ι K) (χ : G →* K) (g : G)
    (X Y : matrixTraceZeroSubmodule ι K) :
    Matrix.trace ((coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ g X).val *
        (matrixTraceZeroAdjointRepresentation ρ g Y).val) =
      χ g * Matrix.trace (X.val * Y.val) := by
  have he := DFunLike.congr_fun (matrixTraceZeroTracePairing_adjoint ρ g X)
    (matrixTraceZeroAdjointRepresentation ρ g Y)
  have hinv : matrixTraceZeroAdjointRepresentation ρ g⁻¹
      (matrixTraceZeroAdjointRepresentation ρ g Y) = Y := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  change Matrix.trace ((matrixTraceZeroAdjointRepresentation ρ g X).val *
      (matrixTraceZeroAdjointRepresentation ρ g Y).val) =
    Matrix.trace (X.val * (matrixTraceZeroAdjointRepresentation ρ g⁻¹
      (matrixTraceZeroAdjointRepresentation ρ g Y)).val) at he
  rw [hinv] at he
  change Matrix.trace ((χ g • (matrixTraceZeroAdjointRepresentation ρ g X).val) *
    (matrixTraceZeroAdjointRepresentation ρ g Y).val) = _
  rw [Matrix.smul_mul, Matrix.trace_smul, he]
  rfl

end
end Dubon2026
