import Dubon2026.SourceOriginalDivisorPrimeGeneration

/-! DUB-17/18 -> numerical modular genus -> mixed prime-power degree.
Every divisor series at M*p^(a+1), with p coprime to M, belongs to the
field obtained by adjoining j_(p^(a+1)) to the original previous field.
Native coprime divisor factorization isolates its prime-power part; the
proved two-prime intersection recovers every missing mixed divisor.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_full_eq_adjoin_full_div_prime.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem mixed_prime_power_divisor_mem (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (a : ℕ) (hpM : ¬ p ∣ M) (d : ℕ) : ∀ [NeZero d], d ∣ M * p ^ (a + 1) →
    qExpand ℚ d jq ∈ IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)) ∪
        {qExpand ℚ (p ^ (a + 1)) jq}) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd0 hdN
    by_cases hbase : d ∣ M * p ^ a
    · exact IntermediateField.subset_adjoin ℚ _ (Or.inl (jqd_mem_full _ hbase))
    · have hcop : Nat.Coprime M (p ^ (a + 1)) :=
        (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpM).symm).pow_right _
      have hsplit : Nat.gcd d M * Nat.gcd d (p ^ (a + 1)) = d :=
        (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdN
      let m := Nat.gcd d M
      have hmM : m ∣ M := Nat.gcd_dvd_right d M
      have hm0 : m ≠ 0 := fun he => NeZero.ne M (Nat.eq_zero_of_zero_dvd (he ▸ hmM))
      obtain ⟨j, hj, hpj⟩ := (Nat.dvd_prime_pow hp.out).mp (Nat.gcd_dvd_right d (p ^ (a + 1)))
      have hd : d = m * p ^ j := by rw [← hsplit, hpj]
      have hja : j = a + 1 := by
        by_contra he
        exact hbase (hd ▸ mul_dvd_mul hmM (pow_dvd_pow p (by omega)))
      rw [hja] at hd
      by_cases hm1 : m = 1
      · rw [qExpand_congr (show d = p ^ (a + 1) by simpa only [hm1, one_mul] using hd) jq]
        exact IntermediateField.subset_adjoin ℚ _ (Or.inr rfl)
      · let q := m.minFac
        have hq : q.Prime := Nat.minFac_prime hm1
        haveI : Fact q.Prime := ⟨hq⟩
        have hqm : q ∣ m := Nat.minFac_dvd m
        have hpq : p ≠ q := fun he => hpM ((he ▸ hqm).trans hmM)
        have hpd : p ∣ d := hd ▸ (dvd_pow_self p (Nat.succ_ne_zero a)).mul_left m
        have hqd : q ∣ d := hd ▸ hqm.trans (dvd_mul_right m (p ^ (a + 1)))
        obtain ⟨m', hm'⟩ := hqm
        have hm'0 : m' ≠ 0 := fun he => hm0 (by rw [hm', he, mul_zero])
        have hdp : d / p = m * p ^ a := by
          rw [hd, pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
        have hdq : d / q = m' * p ^ (a + 1) := by
          calc
            d / q = (q * (m' * p ^ (a + 1))) / q := by congr 1; rw [hd, hm']; ring
            _ = m' * p ^ (a + 1) := Nat.mul_div_cancel_left _ hq.pos
        haveI : NeZero (d / p) := ⟨by rw [hdp]; exact Nat.mul_ne_zero hm0 (pow_ne_zero _ hp.out.ne_zero)⟩
        haveI : NeZero (d / q) := ⟨by rw [hdq]; exact Nat.mul_ne_zero hm'0 (pow_ne_zero _ hp.out.ne_zero)⟩
        apply original_divisor_series_mem_of_two_primes d p q hpq hpd hqd
          (IntermediateField.adjoin ℚ
            ((modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)) ∪
              {qExpand ℚ (p ^ (a + 1)) jq}))
        · exact IntermediateField.subset_adjoin ℚ _ (Or.inl (jqd_mem_full (M * p ^ a) (by
            rw [hdp]
            exact mul_dvd_mul hmM dvd_rfl)))
        · exact ih (d / q) (Nat.div_lt_self (Nat.pos_of_ne_zero hd0.out) hq.one_lt)
            ((Nat.div_dvd_of_dvd hqd).trans hdN)

end
end Dubon2026.SourceFunctionField
