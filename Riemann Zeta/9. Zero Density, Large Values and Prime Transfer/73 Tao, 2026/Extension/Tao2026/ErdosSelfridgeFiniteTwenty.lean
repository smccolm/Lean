import Tao2026.ErdosSelfridgePrimeUnion
import Mathlib.Data.Nat.GCD.BigOperators

namespace Tao2026

theorem not_dvd_powerFreePart_two_of_not_dvd
    {m p : ℕ} (hm : m ≠ 0) (hpm : ¬ p ∣ m) :
    ¬ p ∣ powerFreePart 2 m := by
  intro hpa
  apply hpm
  rw [← powerFreePart_mul_powerRootPart_pow (l := 2) (n := m) hm]
  exact dvd_mul_of_dvd_left hpa _

theorem powerFreePart_two_dvd_six_of_failure_of_avoids_primeSet
    {N H m : ℕ} (P : Finset ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hproduct : erdosSelfridgePrimeProduct H = (∏ p ∈ P, p) * 6)
    (hm : m ∈ consecutiveInterval N H)
    (havoid : ∀ p ∈ P, ¬ p ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∣ 6 := by
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  rw [hproduct] at hdvd
  have hm0 : m ≠ 0 := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hcop : (powerFreePart 2 m).Coprime (∏ p ∈ P, p) :=
    Nat.coprime_prod_right_iff.mpr fun p hp =>
      ((hPprime p hp).coprime_iff_not_dvd.mpr
        (not_dvd_powerFreePart_two_of_not_dvd hm0 (havoid p hp))).symm
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_primeSet_count
    (hSS : SylvesterSchurConclusion) {N H : ℕ} (hH : 3 ≤ H) (hHN : H < N)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime)
    (hproduct : erdosSelfridgePrimeProduct H = (∏ p ∈ P, p) * 6)
    (hcount : 5 ≤ ((consecutiveInterval N H).filter
      (fun m => ∀ p ∈ P, ¬ p ∣ m)).card) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  let G := (consecutiveInterval N H).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)
  let A := G.image (powerFreePart 2)
  let D := (Finset.Icc 1 6).filter (fun a => a ∣ 6)
  have hinj : Set.InjOn (powerFreePart 2) G :=
    (powerFreePart_two_injOn_consecutiveInterval_of_failure
      hSS hH hHN hfail).mono (Finset.filter_subset _ _)
  have hAcard : A.card = G.card := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
  have hsubset : A ⊆ D := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hmData := Finset.mem_filter.mp hm
    have hdvd6 := powerFreePart_two_dvd_six_of_failure_of_avoids_primeSet
      P hPprime hproduct hmData.1 hmData.2 hfail
    change powerFreePart 2 m ∈
      (Finset.Icc 1 6).filter (fun a => a ∣ 6)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
      Nat.le_of_dvd (by norm_num) hdvd6⟩, hdvd6⟩
  have hDcard : D.card = 4 := by decide
  have hle := Finset.card_le_card hsubset
  change 5 ≤ G.card at hcount
  omega

theorem
    not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_eighteen_le_of_le_nineteen
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 18 ≤ H) (hHupper : H ≤ 19) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  apply not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_primeSet_count
    hSS (by omega) hHN erdosSelfridgeExcludedPrimesThroughSeventeen
  · intro p hp
    simp only [erdosSelfridgeExcludedPrimesThroughSeventeen,
      Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · interval_cases H <;> decide
  · exact
      five_le_card_consecutiveInterval_eighteen_to_nineteen_avoiding_large_primes
        hHlower hHupper

theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_twenty
    (hSS : SylvesterSchurConclusion) {N : ℕ} (hN : 20 < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N 20 2 := by
  apply not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_primeSet_count
    hSS (by norm_num) hN erdosSelfridgeExcludedPrimesThroughNineteen
  · intro p hp
    simp only [erdosSelfridgeExcludedPrimesThroughNineteen,
      Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · decide
  · exact five_le_card_consecutiveInterval_twenty_avoiding_large_primes N

theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_twenty
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 20) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hH17 : H ≤ 17
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seventeen
      hSS hHlower hH17 hHN
  by_cases hH19 : H ≤ 19
  · exact
      not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_eighteen_le_of_le_nineteen
        hSS (by omega) hH19 hHN
  have hH20 : H = 20 := by omega
  subst H
  exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_twenty hSS hHN

end Tao2026
