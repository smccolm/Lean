import Dubon2026.SourceOriginalHeckeArithmetic
import Dubon2026.SourceOriginalTateGalois

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular residual
Galois association -> original Tate Hecke realization. Apply the actual
Picard correspondence to every compatible torsion coordinate. Its proved
arithmetic equivariance gives commutation with the original Galois action.
Rank-two decomposition and the Frobenius and inertia identities are still
separate obligations; no such conclusion is assumed or asserted here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (p : ℕ) [Fact p.Prime]

/-- The literal Picard Hecke correspondence acting on original Tate sequences. -/
def originalTateHecke : Module.End ℤ_[p] (TateModule p (originalJZero N)) :=
  TateModule.tateMap p (originalHeckePicard Qbar N ℓ)

theorem originalTateHecke_apply (x : TateModule p (originalJZero N)) (n : ℕ) :
    ((originalTateHecke N ℓ p x : TateModule p (originalJZero N)) : ℕ → originalJZero N) n =
      originalHeckePicard Qbar N ℓ ((x : ℕ → originalJZero N) n) := rfl

theorem originalTateHecke_galois (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x : TateModule p (originalJZero N)) :
    originalTateGaloisRep N p σ (originalTateHecke N ℓ p x) =
      originalTateHecke N ℓ p (originalTateGaloisRep N p σ x) := by
  apply Subtype.ext
  funext n
  rw [originalTateGaloisRep_apply, originalTateHecke_apply,
    originalTateHecke_apply, originalTateGaloisRep_apply]
  exact originalHeckePicard_arithmetic N ℓ σ _

theorem originalTateHecke_commute (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Commute (originalTateGaloisRep N p σ) (originalTateHecke N ℓ p) := by
  apply LinearMap.ext
  intro x
  exact originalTateHecke_galois N ℓ p σ x

end
end Dubon2026.SourceFunctionField
