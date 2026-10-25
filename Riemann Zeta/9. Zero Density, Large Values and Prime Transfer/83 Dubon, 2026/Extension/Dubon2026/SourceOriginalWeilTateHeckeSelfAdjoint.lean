import Dubon2026.SourceOriginalWeilTateHeckeCoordinate
import Dubon2026.SourceOriginalWeilHeckeSelfAdjoint

/-! DUB-17/18 -> determinant on the original Hecke component.
Every finite coordinate of the existing original Tate Hecke operator
is self-adjoint for the actual Weil pairing at primes away from level.
No transpose-identification or Hecke-adjointness premise remains here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]

theorem originalWeilPairing_tateHecke_self_adjoint (hℓN : ¬ ℓ ∣ N) (k : ℕ)
    (x y : TateModule p (originalJZero N)) :
    originalWeilPairing N Qbar (p ^ k)
      (originalTateTorsionCoordinate N p k (originalTateHecke N ℓ p x))
      (originalTateTorsionCoordinate N p k y) =
    originalWeilPairing N Qbar (p ^ k) (originalTateTorsionCoordinate N p k x)
      (originalTateTorsionCoordinate N p k (originalTateHecke N ℓ p y)) := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  rw [← originalWeilHeckeTorsion_coordinate, ← originalWeilHeckeTorsion_coordinate]
  exact originalWeilPairing_hecke_self_adjoint Qbar N ℓ (p ^ k) hℓN _ _

end
end Dubon2026.SourceFunctionField
