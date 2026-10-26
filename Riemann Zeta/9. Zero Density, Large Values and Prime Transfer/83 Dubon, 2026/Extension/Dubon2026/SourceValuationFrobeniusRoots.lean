import Dubon2026.SourceLocalCyclotomicAction
import Dubon2026.SourceOriginalTateInertia

/-! DUB-17/18 -> the primitive Frobenius determinant -> evaluate the
cyclotomic multiplier at the exact source valuation-subring Frobenius.
Reuse the proved local-domain root separation and the original residue
action; only the necessary valuation-ring membership bridge is added. -/
namespace Dubon2026
noncomputable section
variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem valuation_root_mem (n : ℕ) (hn : n ≠ 0) {ζ : L} (hζ : ζ ^ n = 1) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have he : (ζ⁻¹) ^ (n - 1) = ζ := by
      rw [inv_pow]
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), hζ]
    rw [← he]
    exact pow_mem h _

variable [Algebra ℚ L]

theorem valuation_frobenius_root (n q : ℕ) (hn : n ≠ 0)
    (hnr : (n : IsLocalRing.ResidueField A) ≠ 0)
    (g : A.decompositionSubgroup ℚ)
    (hg : ∀ x : IsLocalRing.ResidueField A, g • x = x ^ q)
    (ζ : L) (hζ : ζ ^ n = 1) : (g : L ≃ₐ[ℚ] L) ζ = ζ ^ q := by
  let z : A := ⟨ζ, valuation_root_mem A n hn hζ⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  have hgz : (g • z) ^ n = 1 := by rw [← smul_pow', hz, smul_one]
  have hqz : (z ^ q) ^ n = 1 := by rw [← pow_mul, mul_comm q n, pow_mul, hz, one_pow]
  have he : IsLocalRing.residue A (g • z) = IsLocalRing.residue A (z ^ q) := by
    rw [IsLocalRing.ResidueField.residue_smul, hg, map_pow]
  exact congrArg Subtype.val (sourceLocal_roots_eq_of_residue_eq hgz hqz hnr he)

end
end Dubon2026
