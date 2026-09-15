import Tao2026.VeryBadIntervals

/-!
# Small lengths in Sylvester--Schur

The uniform fixed-length estimate in `VeryBadIntervals` propagates a verified
binomial-growth baseline to every later start. This file combines small
baselines with finite certificates for the first forty-eight lengths.
-/

namespace Tao2026

/-- A bounded search certificate supplies the unbounded existential statement
used by the Sylvester--Schur interface. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_range_certificate
    {N H B : ℕ}
    (hcert : ∃ p ∈ Finset.range B,
      p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨p, _hpB, hp⟩ := hcert
  exact ⟨p, hp⟩

/-- A verified binomial-growth inequality at any upper index propagates to
all later starts and supplies the required large prime in the interval. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
    {N H T : ℕ} (hH : 1 ≤ H) (hHT : H ≤ T) (hTle : T ≤ N + H)
    (hgrowth : T ^ (H + 1).primesBelow.card < T.choose H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  have hrH : (H + 1).primesBelow.card < H := by
    rw [card_primesBelow_succ_eq_primeCounting]
    exact primeCounting_lt_self hH
  have hgrowth' :
      (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H :=
    choose_growth_of_le hHT hrH hTle hgrowth
  have hsumPos : 0 < N + H := by omega
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_pow_card_lt
      (show H ≤ N + H by omega) hsumPos hgrowth'
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

/-- Sylvester--Schur holds uniformly over all starts for lengths below eleven.
Lengths one and two are already beyond their canonical threshold whenever
`N > H`. For lengths three through ten, small verified binomial-growth
baselines leave only short finite ranges, which are checked by reduction. -/
theorem sylvesterSchurBelow_eleven : SylvesterSchurBelow 11 := by
  intro N H hH hHB hHN
  interval_cases H
  · apply exists_large_prime_dvd_consecutiveProduct_of_threshold_le
    · omega
    · simp [sylvesterSchurBinomialThreshold]
      omega
  · apply exists_large_prime_dvd_consecutiveProduct_of_threshold_le
    · omega
    · simp [sylvesterSchurBinomialThreshold]
      omega
  · by_cases htail : sylvesterSchurBinomialThreshold 3 ≤ N + 3
    · exact exists_large_prime_dvd_consecutiveProduct_of_threshold_le
        (by omega) htail
    · have hNUpper : N ≤ 24 := by
        simp [sylvesterSchurBinomialThreshold] at htail
        omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · by_cases htail : sylvesterSchurBinomialThreshold 4 ≤ N + 4
    · exact exists_large_prime_dvd_consecutiveProduct_of_threshold_le
        (by omega) htail
    · have hNUpper : N ≤ 252 := by
        simp [sylvesterSchurBinomialThreshold] at htail
        omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 260) <;>
        decide
  · by_cases htail : 16 ≤ N + 5
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := 5) (T := 16) (by omega) (by omega) htail (by decide)
    · have hNUpper : N ≤ 10 := by omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · by_cases htail : 14 ≤ N + 6
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := 6) (T := 14) (by omega) (by omega) htail (by decide)
    · have hNUpper : N ≤ 7 := by omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · by_cases htail : 24 ≤ N + 7
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := 7) (T := 24) (by omega) (by omega) htail (by decide)
    · have hNUpper : N ≤ 16 := by omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · by_cases htail : 21 ≤ N + 8
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := 8) (T := 21) (by omega) (by omega) htail (by decide)
    · have hNUpper : N ≤ 12 := by omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · by_cases htail : 20 ≤ N + 9
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := 9) (T := 20) (by omega) (by omega) htail (by decide)
    · have hNUpper : N ≤ 10 := by omega
      interval_cases N <;>
        apply exists_large_prime_dvd_consecutiveProduct_of_range_certificate
          (B := 30) <;>
        decide
  · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
      (N := N) (H := 10) (T := 20) (by omega) (by omega) (by omega) (by decide)

/-- For every length from eleven through forty-eight, the upper index `3H`
already satisfies the binomial-growth inequality. -/
theorem sylvesterSchur_triple_baseline_below_fortyNine :
    ∀ H : Fin 49, 11 ≤ H.1 →
      (3 * H.1) ^ (H.1 + 1).primesBelow.card < (3 * H.1).choose H.1 := by
  decide

set_option maxHeartbeats 2000000

/-- One finite certificate covers every start below the `3H` propagation
baseline for lengths from eleven through forty-eight. -/
theorem sylvesterSchur_below_triple_certificate_below_fortyNine :
    ∀ H : Fin 49, ∀ N : Fin 97,
      11 ≤ H.1 → H.1 < N.1 → N.1 + H.1 < 3 * H.1 →
        ∃ p : Fin 145, p.1.Prime ∧ H.1 < p.1 ∧
          p.1 ∣ consecutiveProduct N.1 H.1 := by
  decide

/-- Sylvester--Schur holds uniformly over all starts for every length below
forty-nine. The range `11 ≤ H ≤ 48` uses the uniform `3H` baseline and
one finite-type certificate below it. -/
theorem sylvesterSchurBelow_fortyNine : SylvesterSchurBelow 49 := by
  intro N H hH hHB hHN
  by_cases hHSmall : H < 11
  · exact sylvesterSchurBelow_eleven hH hHSmall hHN
  · have hHEleven : 11 ≤ H := Nat.le_of_not_gt hHSmall
    let hFin : Fin 49 := ⟨H, hHB⟩
    have hbase :
        (3 * H) ^ (H + 1).primesBelow.card < (3 * H).choose H := by
      simpa [hFin] using
        sylvesterSchur_triple_baseline_below_fortyNine hFin (by
          simpa [hFin] using hHEleven)
    by_cases htail : 3 * H ≤ N + H
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := H) (T := 3 * H) hH (by omega) htail hbase
    · have hbelow : N + H < 3 * H := Nat.lt_of_not_ge htail
      have hNBound : N < 97 := by omega
      let nFin : Fin 97 := ⟨N, hNBound⟩
      obtain ⟨p, hpPrime, hHltp, hpDvd⟩ :=
        sylvesterSchur_below_triple_certificate_below_fortyNine
          hFin nFin (by simpa [hFin] using hHEleven)
          (by simpa [hFin, nFin] using hHN)
          (by simpa [hFin, nFin] using hbelow)
      exact ⟨p.1, hpPrime, hHltp, hpDvd⟩

end Tao2026
