import Tao2026.SylvesterSchurPrimeCountTailFiveHundredTwelve

/-!
# Prime-counted Sylvester--Schur tail from length 121

On the finite bridge `121 ≤ H < 512`, the central binomial baseline at `2H`
already works except at five lengths.  The two exceptional pairs are covered
by the prime-counted square-root envelope up to the fixed upper indices `281`
and `403`, where exact binomial growth begins.
-/

namespace Tao2026

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Exact central binomial-growth certificate away from the five exceptional
lengths in `121 ≤ H < 512`. -/
theorem primeCountCentral_choose_growth_bounded
    {H : ℕ} (hH : 121 ≤ H) (hHUpper : H < 512)
    (h139 : H ≠ 139) (h140 : H ≠ 140)
    (h199 : H ≠ 199) (h200 : H ≠ 200) (h201 : H ≠ 201) :
    (2 * H) ^ (H + 1).primesBelow.card < (2 * H).choose H := by
  let Hfin : Fin 512 := ⟨H, hHUpper⟩
  have hfinite : ∀ K : Fin 512, 121 ≤ K.1 →
      K.1 ≠ 139 → K.1 ≠ 140 → K.1 ≠ 199 → K.1 ≠ 200 → K.1 ≠ 201 →
      (2 * K.1) ^ (K.1 + 1).primesBelow.card < (2 * K.1).choose K.1 := by
    decide
  simpa [Hfin] using hfinite Hfin (by simpa [Hfin] using hH)
    (by simpa [Hfin] using h139) (by simpa [Hfin] using h140)
    (by simpa [Hfin] using h199) (by simpa [Hfin] using h200)
    (by simpa [Hfin] using h201)

/-- Exact binomial-growth baseline for the exceptional lengths `139,140`. -/
theorem primeCountCentral_choose_growth_281
    {H : ℕ} (hH : H = 139 ∨ H = 140) :
    281 ^ (H + 1).primesBelow.card < (281 : ℕ).choose H := by
  rcases hH with rfl | rfl <;> decide

/-- Exact square-root-envelope gap through upper index `281` for lengths
`139,140`. -/
theorem primeCountCentral_near_gap_281
    {n H : ℕ} (hH : H = 139 ∨ H = 140) (hn : n ≤ 281) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  have hsqrt : n.sqrt ≤ (281 : ℕ).sqrt := Nat.sqrt_le_sqrt hn
  have hpi : n.sqrt.primeCounting ≤ (281 : ℕ).sqrt.primeCounting :=
    Nat.monotone_primeCounting hsqrt
  calc
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) ≤
        H * (281 ^ (281 : ℕ).sqrt.primeCounting * 3 ^ (H + 1)) := by
      gcongr
      norm_num
    _ < 4 ^ H := by
      have hsqrt281 : (281 : ℕ).sqrt = 16 := by norm_num
      have hpi16 : Nat.primeCounting 16 = 6 := by decide
      rw [hsqrt281, hpi16]
      rcases hH with rfl | rfl <;> norm_num

/-- Exact binomial-growth baseline for the exceptional lengths `199,200,201`. -/
theorem primeCountCentral_choose_growth_403
    {H : ℕ} (hH : H = 199 ∨ H = 200 ∨ H = 201) :
    403 ^ (H + 1).primesBelow.card < (403 : ℕ).choose H := by
  rcases hH with rfl | rfl | rfl <;> decide

/-- Exact square-root-envelope gap through upper index `403` for lengths
`199,200,201`. -/
theorem primeCountCentral_near_gap_403
    {n H : ℕ} (hH : H = 199 ∨ H = 200 ∨ H = 201) (hn : n ≤ 403) :
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) < 4 ^ H := by
  have hsqrt : n.sqrt ≤ (403 : ℕ).sqrt := Nat.sqrt_le_sqrt hn
  have hpi : n.sqrt.primeCounting ≤ (403 : ℕ).sqrt.primeCounting :=
    Nat.monotone_primeCounting hsqrt
  calc
    H * (n ^ n.sqrt.primeCounting * 3 ^ (H + 1)) ≤
        H * (403 ^ (403 : ℕ).sqrt.primeCounting * 3 ^ (H + 1)) := by
      gcongr
      norm_num
    _ < 4 ^ H := by
      have hsqrt403 : (403 : ℕ).sqrt = 20 := by norm_num
      have hpi20 : Nat.primeCounting 20 = 8 := by decide
      rw [hsqrt403, hpi20]
      rcases hH with rfl | rfl | rfl <;> norm_num

private theorem exists_large_prime_dvd_consecutiveProduct_of_choose_growth
    {N H : ℕ} (hHN : H < N)
    (hgrowth : (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_pow_card_lt
      (by omega : H ≤ N + H) (by omega : 0 < N + H) hgrowth
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- Effective all-start tail beginning at length `121`. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_oneHundredTwentyOne
    {N H : ℕ} (hH : 121 ≤ H) (hHN : H < N) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  by_cases hOldTail : 512 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_fiveHundredTwelve
        hOldTail hHN
  have hHUpper : H < 512 := Nat.lt_of_not_ge hOldTail
  by_cases hFirst : H = 139 ∨ H = 140
  · by_cases hnear : N + H ≤ 281
    · exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN (primeCountCentral_near_gap_281 hFirst hnear)
    · apply exists_large_prime_dvd_consecutiveProduct_of_choose_growth hHN
      apply choose_growth_of_le (m := 281)
      · omega
      · rw [card_primesBelow_succ_eq_primeCounting]
        exact primeCounting_lt_self (by omega)
      · omega
      · exact primeCountCentral_choose_growth_281 hFirst
  by_cases hSecond : H = 199 ∨ H = 200 ∨ H = 201
  · by_cases hnear : N + H ≤ 403
    · exact
        exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
          (by omega) hHN (primeCountCentral_near_gap_403 hSecond hnear)
    · apply exists_large_prime_dvd_consecutiveProduct_of_choose_growth hHN
      apply choose_growth_of_le (m := 403)
      · omega
      · rw [card_primesBelow_succ_eq_primeCounting]
        exact primeCounting_lt_self (by omega)
      · omega
      · exact primeCountCentral_choose_growth_403 hSecond
  · apply exists_large_prime_dvd_consecutiveProduct_of_choose_growth hHN
    apply choose_growth_of_le (m := 2 * H)
    · omega
    · rw [card_primesBelow_succ_eq_primeCounting]
      exact primeCounting_lt_self (by omega)
    · omega
    · apply primeCountCentral_choose_growth_bounded hH hHUpper
      all_goals omega

/-- The length residual after the `H ≥ 121` tail. -/
def SylvesterSchurPrimeCountOneHundredTwentyOneResidualRectangle : Prop :=
  ∀ {N H : ℕ}, 101 ≤ H → H < 121 → H < N →
    N + 1 < sylvesterSchurPrimeCountFactorialThreshold H →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- Discharging the `101 ≤ H < 121` rectangle proves unrestricted
Sylvester--Schur. -/
theorem sylvesterSchurConclusion_of_primeCountOneHundredTwentyOneResidualRectangle
    (hrect : SylvesterSchurPrimeCountOneHundredTwentyOneResidualRectangle) :
    SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmallLength : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmallLength hHN
  by_cases htail : 121 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_oneHundredTwentyOne
        htail hHN
  by_cases hsmallStart :
      N + 1 < sylvesterSchurPrimeCountFactorialThreshold H
  · exact hrect (by omega) (by omega) hHN hsmallStart
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCountFactorialThreshold_le
        hH hHN (Nat.le_of_not_gt hsmallStart)

end Tao2026
