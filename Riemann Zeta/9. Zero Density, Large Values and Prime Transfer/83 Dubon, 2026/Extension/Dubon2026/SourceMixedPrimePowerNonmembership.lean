import Dubon2026.SourceMixedPrimePowerFields

/-! DUB-17/18 -> numerical modular genus -> composite degree -> exact
relative prime-power degrees. The original-field identification lets the
existing spread induction use the newly proved coprime-base prime
nonmembership. Thus every next pure prime-power series is outside the
actual mixed-level divisor field, under only the lower coprime base's
divisor-level induction data. The relative degree consumer follows.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimePowerNonmembership SourceLevelProjective
open scoped IntermediateField

theorem mixed_prime_power_next_not_mem_of_divisor_induction
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (hall : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
      modularFunctionFieldFull d = IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d)
    (a : ℕ) :
    qExpand ℚ (p ^ (a + 1)) jq ∉ modularFunctionFieldFull (M * p ^ a) := by
  have hbase := prime_j_not_mem_original_coprime_of_divisor_induction M p hpM hall
  cases a with
  | zero => simpa only [pow_zero, pow_one, mul_one, zero_add] using hbase
  | succ a =>
    rw [← chainField_eq_original_mixed_prime_power M p (a + 1) hpM]
    exact prime_power_next_not_mem_chain M p a hbase

end
end Dubon2026.SourceFunctionField
