import Tao2026.SylvesterSchurFactorialThreshold

/-!
# Sylvester--Schur through length one hundred

The `3H` binomial-growth baseline used below length forty-nine continues to
hold through length one hundred.  A single bounded certificate handles the
starts below that propagation baseline.  Together they prove the unrestricted
large-prime conclusion for every positive length `H < 101`.
-/

namespace Tao2026

set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

/-- For lengths `49` through `100`, the upper index `3H` satisfies the
binomial-growth inequality. -/
theorem sylvesterSchur_triple_baseline_fortyNine_to_oneHundred :
    ∀ H : Fin 101, 49 ≤ H.1 →
      (3 * H.1) ^ (H.1 + 1).primesBelow.card < (3 * H.1).choose H.1 := by
  decide

/-- One finite certificate handles every start below the `3H` propagation
baseline for lengths `49` through `100`. -/
theorem sylvesterSchur_below_triple_certificate_fortyNine_to_oneHundred :
    ∀ H : Fin 101, ∀ N : Fin 201,
      49 ≤ H.1 → H.1 < N.1 → N.1 + H.1 < 3 * H.1 →
        ∃ p : Fin 301, p.1.Prime ∧ H.1 < p.1 ∧
          p.1 ∣ consecutiveProduct N.1 H.1 := by
  decide

/-- Sylvester--Schur holds uniformly over every start for all positive lengths
at most one hundred. -/
theorem sylvesterSchurBelow_oneHundredOne : SylvesterSchurBelow 101 := by
  intro N H hH hHB hHN
  by_cases hHSmall : H < 49
  · exact sylvesterSchurBelow_fortyNine hH hHSmall hHN
  · have hHFortyNine : 49 ≤ H := Nat.le_of_not_gt hHSmall
    let hFin : Fin 101 := ⟨H, hHB⟩
    have hbase :
        (3 * H) ^ (H + 1).primesBelow.card < (3 * H).choose H := by
      simpa [hFin] using
        sylvesterSchur_triple_baseline_fortyNine_to_oneHundred hFin (by
          simpa [hFin] using hHFortyNine)
    by_cases htail : 3 * H ≤ N + H
    · exact exists_large_prime_dvd_consecutiveProduct_of_base_choose_growth
        (N := N) (H := H) (T := 3 * H) hH (by omega) htail hbase
    · have hbelow : N + H < 3 * H := Nat.lt_of_not_ge htail
      have hNBound : N < 201 := by omega
      let nFin : Fin 201 := ⟨N, hNBound⟩
      obtain ⟨p, hpPrime, hHltp, hpDvd⟩ :=
        sylvesterSchur_below_triple_certificate_fortyNine_to_oneHundred
          hFin nFin (by simpa [hFin] using hHFortyNine)
          (by simpa [hFin, nFin] using hHN)
          (by simpa [hFin, nFin] using hbelow)
      exact ⟨p.1, hpPrime, hHltp, hpDvd⟩

end Tao2026
