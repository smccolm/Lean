import Dubon2026.SourceResidueMixedPrimePowerGenerators

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> mixed prime-power tower. The proved divisor memberships
identify the actual full coefficient field with the required simple extension.
No generation assumption is supplied; only the original level being away
from the coefficient characteristic is required. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem residue_full_mixed_prime_power_step_eq_adjoin
    (K : Type*) [Field K] [IsAlgClosed K] (M p : ℕ)
    [NeZero M] [Fact p.Prime] (a : ℕ) (hpM : ¬ p ∣ M)
    (hMK : ((M * p ^ (a + 1) : ℕ) : K) ≠ 0) :
    modularFunctionFieldCoeff (M * p ^ (a + 1)) K = IntermediateField.adjoin K
      ((modularFunctionFieldCoeff (M * p ^ a) K : Set (LaurentSeries K)) ∪
        {qExpand K (p ^ (a + 1)) (jqModC K)}) := by
  apply le_antisymm
  · rw [modularFunctionFieldCoeff, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd, hdN, rfl⟩
    exact residue_mixed_prime_power_divisor_mem K M p a hpM hMK d hdN
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact coefficient_field_mono
        (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a))) hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ jqd_mem_coeff_field (M * p ^ (a + 1)) K (dvd_mul_left _ M)

end
end Dubon2026.SourceFunctionField
