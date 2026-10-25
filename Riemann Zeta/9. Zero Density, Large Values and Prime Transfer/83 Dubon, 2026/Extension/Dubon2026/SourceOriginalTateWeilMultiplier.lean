import Dubon2026.SourceOriginalTateWeilCyclotomic
import Dubon2026.SourceTateScalarFaithfulness

/-! DUB-17/18 -> determinant -> unique cyclotomic pairing multiplier.
A nonzero value of the actual pairing detects its scalar multiplier.
Producing such a value on the required Hecke component remains the explicit
nondegeneracy obligation; it is not assumed to have been discharged here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalTateWeilPairing_scalar_eq
    (x y : TateModule p (originalJZero N)) (hxy : originalTateWeilPairing N p x y ≠ 0)
    (a b : ℤ_[p]) (hab : a • originalTateWeilPairing N p x y =
      b • originalTateWeilPairing N p x y) : a = b := by
  by_contra hne
  apply hxy
  apply TateModule.eq_zero_of_nonzero_scalar_smul_eq_zero p (a - b) (sub_ne_zero.mpr hne)
  exact (_root_.sub_smul a b (originalTateWeilPairing N p x y)).trans (sub_eq_zero.mpr hab)

theorem originalTateWeilPairing_cyclotomic_multiplier_unique
    (σ : Qbar ≃ₐ[ℚ] Qbar) (x y : TateModule p (originalJZero N))
    (hxy : originalTateWeilPairing N p x y ≠ 0) (a : ℤ_[p])
    (ha : originalTateWeilPairing N p (originalTateGaloisRep N p σ x)
      (originalTateGaloisRep N p σ y) = a • originalTateWeilPairing N p x y) :
    a = (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p]) := by
  apply originalTateWeilPairing_scalar_eq N p x y hxy
  exact ha.symm.trans (originalTateWeilPairing_cyclotomic p N σ x y)

end
end Dubon2026.SourceFunctionField
