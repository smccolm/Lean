import Tao2026.PowerfulExtraction
import Tao2026.IntervalMultiples

/-!
# The coefficient-product estimate in Tao's Lemma 3.2

For every integer in a very bad interval, the canonical exponent-one part is
squarefree and has only primes at most the interval length.  A fixed prime can
occur in at most `H / p + 1` interval elements.  Consequently, the product of
all canonical coefficients divides the corresponding small-prime envelope.

This is an exact arithmetic statement; logarithmic estimates for the envelope
are developed separately.
-/

namespace Tao2026

open scoped BigOperators

noncomputable def intervalCoefficientProduct (N H : ℕ) : ℕ :=
  ∏ k ∈ consecutiveInterval N H, singleExponentPart k

noncomputable def smallPrimeCoefficientEnvelope (H : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 H).filter Nat.Prime, p ^ (H / p + 1)

theorem intervalCoefficientProduct_pos (N H : ℕ) :
    0 < intervalCoefficientProduct N H := by
  rw [intervalCoefficientProduct]
  apply Finset.prod_pos
  intro k hk
  exact singleExponentPart_pos (by
    have := (Finset.mem_Ioc.mp hk).1
    omega)

theorem smallPrimeCoefficientEnvelope_pos (H : ℕ) :
    0 < smallPrimeCoefficientEnvelope H := by
  rw [smallPrimeCoefficientEnvelope]
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Finset.mem_filter.mp hp).2.pos _

private theorem factorization_intervalCoefficientProduct_le_count
    (N H p : ℕ) (hp : p.Prime) :
    (intervalCoefficientProduct N H).factorization p ≤
      (intervalMultiples N H p).card := by
  rw [intervalCoefficientProduct, Nat.factorization_prod_apply]
  · calc
      ∑ k ∈ consecutiveInterval N H, (singleExponentPart k).factorization p ≤
          ∑ k ∈ consecutiveInterval N H, if p ∣ k then 1 else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkPos : 0 < k := by
          have := (Finset.mem_Ioc.mp hk).1
          omega
        by_cases hpk : p ∣ k
        · simp only [if_pos hpk]
          exact (Nat.squarefree_iff_factorization_le_one
            (singleExponentPart_pos hkPos).ne').mp
              (squarefree_singleExponentPart hkPos) p
        · have hpCoeff : ¬p ∣ singleExponentPart k := by
            intro hpCoeff
            apply hpk
            apply dvd_trans hpCoeff
            exact ⟨powerfulCore k,
              (singleExponentPart_mul_powerfulCore hkPos.ne').symm⟩
          rw [hp.dvd_iff_one_le_factorization
            (singleExponentPart_pos hkPos).ne'] at hpCoeff
          simp only [if_neg hpk]
          omega
      _ = (intervalMultiples N H p).card := by
        simp [intervalMultiples]
  · intro k hk
    exact (singleExponentPart_pos (by
      have := (Finset.mem_Ioc.mp hk).1
      omega)).ne'

private theorem envelope_exponent_le_factorization
    {H p : ℕ} (hp : p.Prime) (hpLe : p ≤ H) :
    H / p + 1 ≤ (smallPrimeCoefficientEnvelope H).factorization p := by
  rw [smallPrimeCoefficientEnvelope, Nat.factorization_prod_apply]
  · have hpMem : p ∈ (Finset.Icc 2 H).filter Nat.Prime := by
      simp [hp, hp.two_le, hpLe]
    calc
      H / p + 1 = (p ^ (H / p + 1)).factorization p := by
        exact (Nat.factorization_pow_self hp).symm
      _ ≤ ∑ q ∈ (Finset.Icc 2 H).filter Nat.Prime,
          (q ^ (H / q + 1)).factorization p := by
        exact Finset.single_le_sum
          (s := (Finset.Icc 2 H).filter Nat.Prime)
          (f := fun q => (q ^ (H / q + 1)).factorization p)
          (fun _ _ => Nat.zero_le _) hpMem
  · intro q hq
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
    exact pow_ne_zero _ hqPrime.ne_zero

theorem intervalCoefficientProduct_dvd_smallPrimeEnvelope
    {N H : ℕ} (hveryBad : IsVeryBadInterval N H) :
    intervalCoefficientProduct N H ∣ smallPrimeCoefficientEnvelope H := by
  rw [← Nat.factorization_le_iff_dvd
    (intervalCoefficientProduct_pos N H).ne'
    (smallPrimeCoefficientEnvelope_pos H).ne']
  intro p
  by_cases hp : p.Prime
  · by_cases hpLe : p ≤ H
    · calc
        (intervalCoefficientProduct N H).factorization p ≤
            (intervalMultiples N H p).card :=
          factorization_intervalCoefficientProduct_le_count N H p hp
        _ ≤ H / p + 1 := card_intervalMultiples_le N H p hp.pos
        _ ≤ (smallPrimeCoefficientEnvelope H).factorization p :=
          envelope_exponent_le_factorization hp hpLe
    · have hzero : (intervalCoefficientProduct N H).factorization p = 0 := by
        rw [intervalCoefficientProduct, Nat.factorization_prod_apply]
        · apply Finset.sum_eq_zero
          intro k hk
          have hkPos : 0 < k := by
            have := (Finset.mem_Ioc.mp hk).1
            omega
          have hnotDvd : ¬p ∣ singleExponentPart k := by
            intro hpdvd
            exact hpLe (prime_dvd_singleExponentPart_le_length_of_veryBad
              hveryBad hk hp hpdvd)
          rw [hp.dvd_iff_one_le_factorization
            (singleExponentPart_pos hkPos).ne'] at hnotDvd
          omega
        · intro k hk
          exact (singleExponentPart_pos (by
            have := (Finset.mem_Ioc.mp hk).1
            omega)).ne'
      rw [hzero]
      exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end Tao2026
