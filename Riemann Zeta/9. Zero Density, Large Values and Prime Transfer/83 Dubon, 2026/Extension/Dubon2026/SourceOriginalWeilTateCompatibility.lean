import Dubon2026.SourceOriginalWeilLevelCompatibility
import Dubon2026.SourceOriginalTateGalois

/-! DUB-17/18 -> the assembled original Tate pairing. The existing
Tate-coordinate transition is exactly the proved Picard torsion lowering
map. Consequently the actual unit-valued Weil coordinates form a
compatible p-power root sequence. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

omit [NeZero N] [Fact p.Prime] in
theorem originalPicardTorsionLower_coordinate (k : ℕ) (x : TateModule p (originalJZero N)) :
    originalPicardTorsionLower N Qbar (p ^ k) p (originalTateTorsionCoordinate N p (k + 1) x) =
      originalTateTorsionCoordinate N p k x := by
  apply Subtype.ext
  change p • (x : ℕ → originalJZero N) (k + 1) = (x : ℕ → originalJZero N) k
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  exact TateModule.compat x k

theorem originalWeilPairing_tate_power_compat (k : ℕ)
    (x y : TateModule p (originalJZero N)) :
    (originalWeilPairing N Qbar (p ^ (k + 1))
      (originalTateTorsionCoordinate N p (k + 1) x)
      (originalTateTorsionCoordinate N p (k + 1) y) : Qbarˣ) ^ p =
    (originalWeilPairing N Qbar (p ^ k)
      (originalTateTorsionCoordinate N p k x) (originalTateTorsionCoordinate N p k y) : Qbarˣ) := by
  have he := originalWeilPairing_level_change N Qbar (p ^ k) p
    (originalTateTorsionCoordinate N p (k + 1) x) (originalTateTorsionCoordinate N p (k + 1) y)
  rw [originalPicardTorsionLower_coordinate, originalPicardTorsionLower_coordinate] at he
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val] using he.symm

end
end Dubon2026.SourceFunctionField
