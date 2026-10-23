import Dubon2026.SourceResidueMixedPrimePowerDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue j-map degree. Strong induction proves actual generation
by j and j_N and degree dedekindPsi(N) together, over an algebraically closed
coefficient field in which N is nonzero. Generation uses proper divisors;
coprime nonmembership and the reverse-expansion recurrence give the mixed
prime-power step. No generation, conjugate, degree or nonmembership input
remains on this consumer. Adapted from the proved local all-level induction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem residue_full_generation_and_degree (N : ℕ) : ∀ [NeZero N], (N : K) ≠ 0 →
    modularFunctionFieldCoeff N K = IntermediateField.adjoin K
      ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)) ∧
    relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff N K) = dedekindPsi N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro _ hNK
    have hgen := residue_generation_of_proper_divisor_induction N hNK
      (fun d hdvd hd _ => ih d hd (ne_zero_of_dvd_ne_zero hNK hdvd.natCast))
    refine ⟨hgen, ?_⟩
    by_cases hN1 : N = 1
    · subst N
      rw [coefficient_level_one_eq, IntermediateField.relfinrank_self, dedekindPsi_one]
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
      have hMN : M ∣ N := ⟨p ^ (a + 1), hNM⟩
      have hMK : (M : K) ≠ 0 := ne_zero_of_dvd_ne_zero hNK hMN.natCast
      have hpK : (p : K) ≠ 0 := ne_zero_of_dvd_ne_zero hNK (Nat.minFac_dvd N).natCast
      have hallM : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
          modularFunctionFieldCoeff d K = IntermediateField.adjoin K
            ({(jqModC K), qExpand K d (jqModC K)} : Set (LaurentSeries K)) ∧
          relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff d K) = dedekindPsi d :=
        fun d hd _ => ih d (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd) hMlt)
          (ne_zero_of_dvd_ne_zero hMK hd.natCast)
      have hlow := (ih (M * p ^ a) hlowLt
        (ne_zero_of_dvd_ne_zero hNK (show M * p ^ a ∣ N from hNM ▸ hlowN).natCast)).2
      have hj : K⟮(jqModC K)⟯ ≤ modularFunctionFieldCoeff (M * p ^ a) K :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_coeff_field _ K))
      have htower := IntermediateField.relfinrank_mul_relfinrank hj (coefficient_field_mono hlowN)
      have hstep := residue_mixed_prime_power_step_relfinrank M p a hpM hMK hpK hallM
      rw [hNM, ← htower, hlow, hstep]
      by_cases ha : a = 0
      · simp only [ha, pow_zero, pow_one, zero_add, mul_one]
        exact (dedekindPsi_mul_prime_not_dvd hp hpM).symm
      · rw [if_neg ha, pow_succ, ← Nat.mul_assoc]
        exact (dedekindPsi_mul_prime_dvd (NeZero.ne _) hp
          ((dvd_pow_self p ha).mul_left M)).symm

end
end Dubon2026.SourceFunctionField
