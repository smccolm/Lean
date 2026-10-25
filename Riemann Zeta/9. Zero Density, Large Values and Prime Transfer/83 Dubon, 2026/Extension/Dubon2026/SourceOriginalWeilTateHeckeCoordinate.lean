import Dubon2026.SourceOriginalWeilHeckeTranspose
import Dubon2026.SourceOriginalTateHeckeArithmetic

/-! DUB-17/18 -> Hecke-adjoint original Tate pairing. The finite
Hecke operator identified by the divisorial pairing is exactly the
coordinate of the existing original Tate Hecke operator. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (p : ℕ) [Fact p.Prime]

theorem originalWeilHeckeTorsion_coordinate (k : ℕ) (x : TateModule p (originalJZero N)) :
    originalWeilHeckeTorsion Qbar N ℓ (p ^ k) (originalTateTorsionCoordinate N p k x) =
      originalTateTorsionCoordinate N p k (originalTateHecke N ℓ p x) := by
  apply Subtype.ext
  rw [originalWeilHeckeTorsion_val]
  exact (originalTateHecke_apply N ℓ p x k).symm

theorem originalWeilPairing_tateHecke_coordinate (k : ℕ)
    (x y : TateModule p (originalJZero N)) :
    originalWeilPairing N Qbar (p ^ k)
      (originalTateTorsionCoordinate N p k (originalTateHecke N ℓ p x))
      (originalTateTorsionCoordinate N p k y) =
    originalWeilPairing N Qbar (p ^ k) (originalTateTorsionCoordinate N p k x)
      (originalWeilHeckeTransposeTorsion Qbar N ℓ (p ^ k) (originalTateTorsionCoordinate N p k y)) := by
  rw [← originalWeilHeckeTorsion_coordinate]
  exact originalWeilPairing_hecke_transpose Qbar N ℓ (p ^ k) _ _

end
end Dubon2026.SourceFunctionField
