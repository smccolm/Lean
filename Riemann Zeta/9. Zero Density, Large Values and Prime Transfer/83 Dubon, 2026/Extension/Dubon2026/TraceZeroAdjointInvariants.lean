import Dubon2026.MatrixAdjointScalarDescent
import Dubon2026.TraceZeroAdjointRepresentation

/-! # Vanishing of actual trace-zero adjoint invariants under absolute irreducibility -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

/-- Genuine scalar-extension irreducibility and nonzero original matrix dimension force the actual trace-zero adjoint invariant submodule to vanish. -/
theorem matrixTraceZeroAdjointInvariants_eq_bot
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    (matrixTraceZeroAdjointRepresentation ρ).invariants = ⊥ := by
  have hcard : Fintype.card ι ≠ 0 := by
    intro h
    apply hn
    rw [h, Nat.cast_zero]
  letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
  apply bot_unique
  intro X hX
  let Y : (matrixAdjointRepresentation ρ).invariants := ⟨X.val, by
    intro g
    exact congrArg Subtype.val (hX g)⟩
  obtain ⟨c, hc⟩ := matrixAdjointInvariant_eq_scalar_of_extension (L := L) ρ Y
  change X.val = c • (1 : Matrix ι ι K) at hc
  have ht : c * (Fintype.card ι : K) = 0 := by
    have h := X.property
    change Matrix.trace X.val = 0 at h
    rw [hc, Matrix.trace_smul, Matrix.trace_one] at h
    exact h
  have hc0 : c = 0 := (mul_eq_zero.mp ht).resolve_right hn
  change X = 0
  apply Subtype.ext
  rw [hc, hc0, zero_smul]
  rfl

end
end Dubon2026
