import Dubon2026.SourceOriginalTateWeilLinearity
import Dubon2026.SourceOriginalWeilTateHeckeSelfAdjoint

/-! DUB-17/18 -> determinant on the original Hecke component.
The assembled arithmetic Tate pairing is alternating at odd primes and
self-adjoint for the existing Hecke operators away from the level.
Nondegeneracy and restriction to the required component remain separate. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalTateWeilPairing_self_of_odd (hp : Odd p)
    (x : TateModule p (originalJZero N)) : originalTateWeilPairing N p x x = 0 := by
  apply Subtype.ext
  funext k
  rw [originalTateWeilPairing_coordinate, originalWeilPairing_self_of_odd N Qbar (p ^ k) hp.pow]
  rfl

theorem originalTateWeilBilinear_self_of_odd (hp : Odd p)
    (x : TateModule p (originalJZero N)) : originalTateWeilBilinear N p x x = 0 :=
  originalTateWeilPairing_self_of_odd N p hp x

theorem originalTateWeilPairing_hecke_self_adjoint (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p (originalTateHecke N ℓ p x) y =
      originalTateWeilPairing N p x (originalTateHecke N ℓ p y) := by
  apply Subtype.ext
  funext k
  rw [originalTateWeilPairing_coordinate, originalTateWeilPairing_coordinate,
    originalWeilPairing_tateHecke_self_adjoint N ℓ p hℓN k x y]

end
end Dubon2026.SourceFunctionField
