import Tao2026.SylvesterSchurPrimeCountTailOneHundredTwentyOne

/-!
# Unrestricted Sylvester--Schur

The final twenty lengths use one common binomial-growth baseline at upper
index `243`.  Below that baseline only a bounded set of starts remains, and a
single kernel certificate supplies the required large prime divisor.
-/

namespace Tao2026

set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

/-- The upper index `243` satisfies the binomial-growth inequality for every
remaining length `101 ≤ H < 121`. -/
theorem sylvesterSchur_baseline_oneHundredOne_to_oneHundredTwenty :
    ∀ H : Fin 121, 101 ≤ H.1 →
      243 ^ (H.1 + 1).primesBelow.card < (243 : ℕ).choose H.1 := by
  decide

/-- One finite certificate handles every start below upper index `243` for
the final twenty lengths. -/
theorem sylvesterSchur_below_243_certificate_oneHundredOne_to_oneHundredTwenty :
    ∀ H : Fin 121, ∀ N : Fin 143,
      101 ≤ H.1 → H.1 < N.1 → N.1 + H.1 < 243 →
        ∃ p : Fin 243, p.1.Prime ∧ H.1 < p.1 ∧
          p.1 ∣ consecutiveProduct N.1 H.1 := by
  decide

/-- The unrestricted Sylvester--Schur theorem: every product of `H`
consecutive integers beginning after `H` has a prime divisor larger than
`H`. -/
theorem sylvesterSchur : SylvesterSchurConclusion := by
  intro N H hH hHN
  by_cases hsmall : H < 101
  · exact sylvesterSchurBelow_oneHundredOne hH hsmall hHN
  by_cases htail : 121 ≤ H
  · exact
      exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail_oneHundredTwentyOne
        htail hHN
  have hHUpper : H < 121 := Nat.lt_of_not_ge htail
  let hFin : Fin 121 := ⟨H, hHUpper⟩
  have hbase : 243 ^ (H + 1).primesBelow.card < (243 : ℕ).choose H := by
    simpa [hFin] using
      sylvesterSchur_baseline_oneHundredOne_to_oneHundredTwenty hFin (by
        simpa [hFin] using (show 101 ≤ H by omega))
  by_cases hfar : 243 ≤ N + H
  · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
      (N := N) (H := H) (T := 243) hH (by omega) hfar hbase
  · have hbelow : N + H < 243 := Nat.lt_of_not_ge hfar
    have hNBound : N < 143 := by omega
    let nFin : Fin 143 := ⟨N, hNBound⟩
    obtain ⟨p, hpPrime, hHltp, hpDvd⟩ :=
      sylvesterSchur_below_243_certificate_oneHundredOne_to_oneHundredTwenty
        hFin nFin (by simpa [hFin] using (show 101 ≤ H by omega))
        (by simpa [hFin, nFin] using hHN)
        (by simpa [hFin, nFin] using hbelow)
    exact ⟨p.1, hpPrime, hHltp, hpDvd⟩

end Tao2026
