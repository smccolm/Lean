import Dubon2026.SourceRationalPrimeStepDegree

/-! DUB-17/18 -> numerical modular genus -> all-level original j-map
degree. The original mixed tower has relative degree p+1 at its first
prime step and p thereafter. Actual field equalities and next-series
nonmembership supply all inputs to the existing prime relation and
cyclotomic-cycle degree proofs. Only the coprime base's lower divisor
induction data remain explicit for the final strong induction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem original_mixed_prime_power_step_relfinrank (M p : ℕ)
    [NeZero M] [hp : Fact p.Prime] (a : ℕ) (hpM : ¬ p ∣ M)
    (hall : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
      modularFunctionFieldFull d = IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d) :
    relfinrank (modularFunctionFieldFull (M * p ^ a))
      (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by
  cases a with
  | zero =>
    have he := original_full_mixed_prime_power_step_eq_adjoin M p 0 hpM
    simp only [pow_zero, zero_add, pow_one, mul_one] at he
    simp only [pow_zero, zero_add, pow_one, mul_one, ↓reduceIte]
    rw [he, relfinrank_adjoin_union_singleton]
    exact rational_prime_step_finrank_eq_of_not_mem (modularFunctionFieldFull M) (jq_mem_full M)
      p (prime_j_not_mem_original_coprime_of_divisor_induction M p hpM hall)
  | succ a =>
    rw [original_full_mixed_prime_power_step_eq_adjoin M p (a + 1) hpM,
      relfinrank_adjoin_union_singleton]
    rw [if_neg (Nat.succ_ne_zero a)]
    apply prime_power_step_finrank_eq_of_not_mem (modularFunctionFieldFull (M * p ^ (a + 1))) p a
    · exact jqd_mem_full _ ((pow_dvd_pow p (Nat.le_succ a)).trans (dvd_mul_left _ M))
    · exact jqd_mem_full _ (dvd_mul_left _ M)
    · exact mixed_prime_power_next_not_mem_of_divisor_induction M p hpM hall (a + 1)

end
end Dubon2026.SourceFunctionField
