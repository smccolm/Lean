import Dubon2026.SourceOriginalWeilTateCompatibility
import Dubon2026.SourceOriginalWeilAlternation

/-! DUB-17/18 -> Frobenius determinant -> original arithmetic Tate pairing.
The value is the actual compatible sequence of divisorial Weil roots of unity.
Torsion and transition laws are proved, rather than supplied as pairing data. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

/-- The arithmetic Weil pairing on the existing original Jacobian Tate module. -/
def originalTateWeilPairing (x y : TateModule p (originalJZero N)) :
    TateModule p (Additive Qbarˣ) :=
  ⟨fun k => Additive.ofMul (originalWeilPairing N Qbar (p ^ k)
      (originalTateTorsionCoordinate N p k x) (originalTateTorsionCoordinate N p k y) : Qbarˣ),
    fun k => ⟨by
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul, zpow_natCast,
        toMul_zero]
      exact (mem_rootsOfUnity (p ^ k) _).mp (originalWeilPairing N Qbar (p ^ k)
        (originalTateTorsionCoordinate N p k x) (originalTateTorsionCoordinate N p k y)).property,
    by
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul, zpow_natCast]
      exact originalWeilPairing_tate_power_compat N p k x y⟩⟩

theorem originalTateWeilPairing_coordinate (k : ℕ) (x y : TateModule p (originalJZero N)) :
    (originalTateWeilPairing N p x y : ℕ → Additive Qbarˣ) k =
      Additive.ofMul (originalWeilPairing N Qbar (p ^ k)
        (originalTateTorsionCoordinate N p k x) (originalTateTorsionCoordinate N p k y) : Qbarˣ) := rfl

theorem originalTateWeilPairing_add_left (x x' y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p (x + x') y =
      originalTateWeilPairing N p x y + originalTateWeilPairing N p x' y := by
  apply Subtype.ext
  funext k
  simp only [TateModule.coe_add, Pi.add_apply, originalTateWeilPairing_coordinate,
    map_add, originalWeilPairing_add_left, Subgroup.coe_mul, ofMul_mul]

theorem originalTateWeilPairing_add_right (x y y' : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p x (y + y') =
      originalTateWeilPairing N p x y + originalTateWeilPairing N p x y' := by
  apply Subtype.ext
  funext k
  simp only [TateModule.coe_add, Pi.add_apply, originalTateWeilPairing_coordinate,
    map_add, originalWeilPairing_add_right, Subgroup.coe_mul, ofMul_mul]

theorem originalTateWeilPairing_zero_left (y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p 0 y = 0 := by
  apply Subtype.ext
  funext k
  simp only [TateModule.coe_zero, Pi.zero_apply, originalTateWeilPairing_coordinate,
    map_zero, originalWeilPairing_zero_left, OneMemClass.coe_one, ofMul_one]

theorem originalTateWeilPairing_zero_right (x : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p x 0 = 0 := by
  apply Subtype.ext
  funext k
  simp only [TateModule.coe_zero, Pi.zero_apply, originalTateWeilPairing_coordinate,
    map_zero, originalWeilPairing_zero_right, OneMemClass.coe_one, ofMul_one]

end
end Dubon2026.SourceFunctionField
