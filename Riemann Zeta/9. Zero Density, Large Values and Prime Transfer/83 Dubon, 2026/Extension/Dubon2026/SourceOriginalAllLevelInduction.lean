import Dubon2026.SourceMixedPrimePowerDegree

/-! DUB-17/18 -> numerical modular genus -> exact original modular
coordinate degree. Strong induction proves generation and degree together.
Generation uses only proper divisor data. Prime-power factorization,
the actual mixed tower, derived nonmembership and native relative-degree
multiplication then prove degree dedekindPsi(N). No generation, degree,
conjugate identity or nonmembership hypothesis remains on this consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem original_full_generation_and_degree (N : ℕ) : ∀ [NeZero N],
    modularFunctionFieldFull N = IntermediateField.adjoin ℚ
      ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) ∧
    relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull N) = dedekindPsi N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro _
    have hgen := original_generation_of_proper_divisor_induction N
      (fun d _ hd _ => ih d hd)
    refine ⟨hgen, ?_⟩
    by_cases hN1 : N = 1
    · subst N
      rw [original_level_one_field_eq, IntermediateField.relfinrank_self, dedekindPsi_one]
    · let p := N.minFac
      have hp : p.Prime := Nat.minFac_prime hN1
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, M, hpM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) p hp.ne_one
      have hM0 : M ≠ 0 := fun he => NeZero.ne N (by rw [hN, he, mul_zero])
      haveI : NeZero M := ⟨hM0⟩
      obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := by
        cases k with
        | zero =>
          have hd : p ∣ N := Nat.minFac_dvd N
          rw [hN, pow_zero, one_mul] at hd
          exact False.elim (hpM hd)
        | succ a => exact ⟨a, rfl⟩
      have hNM : N = M * p ^ (a + 1) := hN.trans (Nat.mul_comm _ _)
      have hlowN : M * p ^ a ∣ M * p ^ (a + 1) :=
        mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ a))
      have hlowLt : M * p ^ a < N := by
        rw [hNM, pow_succ, ← Nat.mul_assoc]
        exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne _)) hp.one_lt
      have hMlt : M < N := lt_of_le_of_lt
        (Nat.le_mul_of_pos_right M (pow_pos hp.pos a)) hlowLt
      have hallM : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
          modularFunctionFieldFull d = IntermediateField.adjoin ℚ
            ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
          relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d :=
        fun d hd _ => ih d (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd) hMlt)
      have hlow := (ih (M * p ^ a) hlowLt).2
      have hj : ℚ⟮jq⟯ ≤ modularFunctionFieldFull (M * p ^ a) :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_full _))
      have htower := IntermediateField.relfinrank_mul_relfinrank hj (original_full_mono_of_dvd hlowN)
      have hstep := original_mixed_prime_power_step_relfinrank M p a hpM hallM
      rw [hNM, ← htower, hlow, hstep]
      by_cases ha : a = 0
      · simp only [ha, pow_zero, pow_one, zero_add, mul_one]
        exact (dedekindPsi_mul_prime_not_dvd hp hpM).symm
      · rw [if_neg ha, pow_succ, ← Nat.mul_assoc]
        exact (dedekindPsi_mul_prime_dvd (NeZero.ne _) hp
          ((dvd_pow_self p ha).mul_left M)).symm

end
end Dubon2026.SourceFunctionField
