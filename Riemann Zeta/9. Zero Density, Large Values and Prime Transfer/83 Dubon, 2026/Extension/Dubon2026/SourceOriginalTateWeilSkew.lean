import Dubon2026.SourceOriginalTateWeilLinearity
import Dubon2026.SourceTateScalarFaithfulness

/-! DUB-17/18 -> the alternating rational pairing for the original primitive
component. Finite Weil skew symmetry and faithful Tate scalar multiplication
prove alternation at every Tate prime, including two. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalTateWeilPairing_skew (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p x y = -originalTateWeilPairing N p y x := by
  apply Subtype.ext
  funext k
  simp only [TateModule.coe_neg, Pi.neg_apply, originalTateWeilPairing_coordinate]
  rw [originalWeilPairing_symm]
  rfl

theorem originalTateWeilBilinear_self (x : TateModule p (originalJZero N)) :
    originalTateWeilBilinear N p x x = 0 := by
  apply TateModule.eq_zero_of_nonzero_scalar_smul_eq_zero p (2 : ℤ_[p]) (by norm_num)
  change (2 : ℤ_[p]) • originalTateWeilPairing N p x x = 0
  calc
    (2 : ℤ_[p]) • originalTateWeilPairing N p x x =
        ((1 : ℤ_[p]) + 1) • originalTateWeilPairing N p x x := by norm_num
    _ = originalTateWeilPairing N p x x + originalTateWeilPairing N p x x := by
      simpa only [_root_.one_smul] using
        (_root_.add_smul (1 : ℤ_[p]) 1 (originalTateWeilPairing N p x x))
    _ = 0 := add_eq_zero_iff_eq_neg.mpr (originalTateWeilPairing_skew N p x x)

end
end Dubon2026.SourceFunctionField
