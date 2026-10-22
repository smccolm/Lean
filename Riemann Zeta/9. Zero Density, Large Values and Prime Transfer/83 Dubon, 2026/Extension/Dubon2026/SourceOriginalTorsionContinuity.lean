import Dubon2026.SourceOriginalPicardFieldOfDefinition
import Dubon2026.SourceOriginalTorsionGalois
import Mathlib.Topology.Algebra.MulAction

/-! DUB-17/18 -> modular residual Galois association -> continuous
original Tate action. The actual original torsion group is given its
discrete topology. Its literal arithmetic action has the same stabilizer
as the underlying original divisor class. The proved finite fields of
definition and native open-stabilizer criterion therefore prove continuity,
without a supplied continuity or finite-image hypothesis.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

/-- The original torsion group carries its natural discrete topology. -/
instance originalJZeroTorsionTopology (N n : ℕ) : TopologicalSpace (originalJZeroTorsion N n) := ⊥

/-- The chosen original torsion topology is discrete. -/
instance originalJZeroTorsionDiscrete (N n : ℕ) : DiscreteTopology (originalJZeroTorsion N n) := ⟨rfl⟩

/-- The native group action of the actual original torsion representation. -/
instance originalJZeroTorsionArithmeticAction (N : ℕ) [NeZero N] (n : ℕ) :
    DistribMulAction (Qbar ≃ₐ[ℚ] Qbar) (originalJZeroTorsion N n) :=
  DistribMulAction.compHom _ (originalJZeroTorsionGaloisRep N n)

theorem originalJZeroTorsion_isOpen_stabilizer (N : ℕ) [NeZero N] (n : ℕ)
    (x : originalJZeroTorsion N n) :
    IsOpen (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) x : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
  have he : (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) x : Set (Qbar ≃ₐ[ℚ] Qbar)) =
      (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) (x.val : originalJZero N) : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
    ext σ
    change originalJZeroTorsionGaloisRep N n σ x = x ↔ originalArithmeticPicard N σ x.val = x.val
    exact Subtype.ext_iff
  rw [he]
  exact originalJZero_isOpen_stabilizer N x.val

/-- The genuine arithmetic action is continuous on the actual discrete original torsion. -/
instance originalJZeroTorsionContinuousAction (N : ℕ) [NeZero N] (n : ℕ) :
    ContinuousSMul (Qbar ≃ₐ[ℚ] Qbar) (originalJZeroTorsion N n) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (originalJZeroTorsion_isOpen_stabilizer N n)

theorem originalJZeroTorsionGaloisRep_continuous_apply (N : ℕ) [NeZero N] (n : ℕ)
    (x : originalJZeroTorsion N n) :
    Continuous (fun σ : Qbar ≃ₐ[ℚ] Qbar => originalJZeroTorsionGaloisRep N n σ x) :=
  continuous_id.smul continuous_const

end
end Dubon2026.SourceFunctionField
