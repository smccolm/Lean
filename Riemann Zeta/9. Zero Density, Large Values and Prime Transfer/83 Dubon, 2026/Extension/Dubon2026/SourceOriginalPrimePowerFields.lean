import Dubon2026.SourcePrimePowerChainNonmembership
import Dubon2026.SourceOriginalDegreeBaseChange
import Dubon2026.SourceJPrimeNonmembership

/-! DUB-17/18 -> numerical modular genus -> original prime-power degree.
Identify the spread argument's stage over level one with the actual
divisor-generated prime-power field. The base case uses the already
proved nonpolynomiality and integral-root descent for the literal j series.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField PrimePowerNonmembership

theorem original_level_one_field_eq :
    modularFunctionFieldFull 1 = IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) := by
  change IntermediateField.adjoin ℚ (divisorExpansions 1) = _
  apply congrArg (IntermediateField.adjoin ℚ)
  ext x
  constructor
  · rintro ⟨d, hd, hdvd, rfl⟩
    have he : d = 1 := Nat.dvd_one.mp hdvd
    rw [qExpand_congr he jq, qExpand_one_apply]
    exact Set.mem_singleton jq
  · rintro rfl
    exact ⟨1, inferInstance, dvd_rfl, (qExpand_one_apply jq).symm⟩

theorem prime_j_not_mem_original_one (p : ℕ) [Fact p.Prime] :
    qExpand ℚ p jq ∉ modularFunctionFieldFull 1 := by
  rw [original_level_one_field_eq]
  have h := prime_j_not_mem_rational_j p ℚ
  simpa only [coeffEmb_rat_apply] using h

theorem chainField_one_eq_original_prime_power (p : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    chainField 1 p a = modularFunctionFieldFull (p ^ a) := by
  apply le_antisymm
  · rw [chainField, adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · rw [original_level_one_field_eq] at hx
      exact (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (jq_mem_full (p ^ a)))) hx
    · exact jqd_mem_full _ (pow_dvd_pow p hj)
  · rw [modularFunctionFieldFull, adjoin_le_iff]
    rintro x ⟨d, hd, hdvd, rfl⟩
    obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rw [qExpand_congr he jq]
    exact mem_chainField 1 p hj

theorem original_prime_power_next_not_mem (p : ℕ) [Fact p.Prime] (a : ℕ) :
    qExpand ℚ (p ^ (a + 2)) jq ∉ modularFunctionFieldFull (p ^ (a + 1)) := by
  rw [← chainField_one_eq_original_prime_power p (a + 1)]
  exact prime_power_next_not_mem_chain 1 p a (prime_j_not_mem_original_one p)

end
end Dubon2026.SourceFunctionField
