import Dubon2026.SourceMixedPrimePowerGenerators

/-! DUB-17/18 -> numerical modular genus -> composite degree -> actual
prime-power tower. The mixed-divisor generation proof identifies the
original full next-level field with adjoining the next pure prime-power
series. Induction identifies every stage of the existing spread argument
with the literal original divisor field. No degree or generation
assumption is used in these field equalities.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField PrimePowerNonmembership

theorem original_full_mixed_prime_power_step_eq_adjoin
    (M p : ℕ) [NeZero M] [Fact p.Prime] (a : ℕ) (hpM : ¬ p ∣ M) :
    modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)) ∪
        {qExpand ℚ (p ^ (a + 1)) jq}) := by
  apply le_antisymm
  · rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd, hdN, rfl⟩
    exact mixed_prime_power_divisor_mem M p a hpM d hdN
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact original_full_mono_of_dvd
        (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a))) hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ jqd_mem_full (M * p ^ (a + 1)) (dvd_mul_left _ M)

theorem chainField_eq_original_mixed_prime_power
    (M p : ℕ) [NeZero M] [Fact p.Prime] (a : ℕ) (hpM : ¬ p ∣ M) :
    chainField M p a = modularFunctionFieldFull (M * p ^ a) := by
  induction a with
  | zero => rw [chainField_zero, pow_zero, mul_one]
  | succ a ih =>
    rw [chainField_succ, ih,
      qExpand_congr (pow_succ p a).symm jq,
      ← original_full_mixed_prime_power_step_eq_adjoin M p a hpM]

end
end Dubon2026.SourceFunctionField
