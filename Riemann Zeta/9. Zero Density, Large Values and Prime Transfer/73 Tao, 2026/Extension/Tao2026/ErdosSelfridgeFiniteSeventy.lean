import Tao2026.ErdosSelfridgeFiniteTwenty

namespace Tao2026

theorem le_card_filter_avoiding_primeSet
    {N H K : ℕ} (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (hsum : (∑ p ∈ P, (H / p + if p ∣ H then 0 else 1)) + K ≤ H) :
    K ≤ ((consecutiveInterval N H).filter
      (fun m => ∀ p ∈ P, ¬ p ∣ m)).card := by
  let S := consecutiveInterval N H
  let B := intervalPrimeMultiplesUnion N H P
  have hBsub : B ⊆ S := by
    intro m hm
    change m ∈ intervalPrimeMultiplesUnion N H P at hm
    rw [intervalPrimeMultiplesUnion, Finset.mem_biUnion] at hm
    obtain ⟨p, hp, hpm⟩ := hm
    exact (Finset.mem_filter.mp hpm).1
  have hBcard := card_intervalPrimeMultiplesUnion_le N H P hP
  change B.card ≤ _ at hBcard
  have hdiff : (S \ B).card = S.card - (B ∩ S).card := Finset.card_sdiff
  rw [Finset.inter_eq_left.mpr hBsub] at hdiff
  have hScard : S.card = H := by simp [S, consecutiveInterval]
  have hcard : K ≤ (S \ B).card := by omega
  have heq : S \ B = S.filter (fun m => ∀ p ∈ P, ¬ p ∣ m) := by
    ext m
    simp only [S, B, Finset.mem_sdiff, Finset.mem_filter,
      intervalPrimeMultiplesUnion, Finset.mem_biUnion, intervalMultiples]
    constructor
    · rintro ⟨hmS, hm⟩
      exact ⟨hmS, fun p hp hpm => hm ⟨p, hp, hmS, hpm⟩⟩
    · rintro ⟨hmS, hm⟩
      exact ⟨hmS, fun ⟨p, hp, _hmS, hpm⟩ => hm p hp hpm⟩
  rwa [heq] at hcard

def erdosSelfridgeExcludedPrimesFromSeven (H : ℕ) : Finset ℕ :=
  (Nat.primesBelow H).filter (fun p => 7 ≤ p)

theorem nine_le_card_consecutiveInterval_twenty_one_to_seventy_avoiding_large_primes
    {N H : ℕ} (hHlower : 21 ≤ H) (hHupper : H ≤ 70) :
    9 ≤ ((consecutiveInterval N H).filter
      (fun m => ∀ p ∈ erdosSelfridgeExcludedPrimesFromSeven H,
        ¬ p ∣ m)).card := by
  apply le_card_filter_avoiding_primeSet
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    exact (Nat.prime_of_mem_primesBelow hp').pos
  · interval_cases H <;> decide

theorem powerFreePart_two_dvd_base_of_failure_of_avoids_primeSet
    {N H m B : ℕ} (P : Finset ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hproduct : erdosSelfridgePrimeProduct H = (∏ p ∈ P, p) * B)
    (hm : m ∈ consecutiveInterval N H)
    (havoid : ∀ p ∈ P, ¬ p ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∣ B := by
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

theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_primeSet_base_count
    (hSS : SylvesterSchurConclusion) {N H B K : ℕ}
    (hH : 3 ≤ H) (hHN : H < N) (P : Finset ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hproduct : erdosSelfridgePrimeProduct H = (∏ p ∈ P, p) * B)
    (hBpos : 0 < B)
    (hcount : K ≤ ((consecutiveInterval N H).filter
      (fun m => ∀ p ∈ P, ¬ p ∣ m)).card)
    (hcandidates : ((Finset.Icc 1 B).filter (fun a => a ∣ B)).card < K) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  let G := (consecutiveInterval N H).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)
  let A := G.image (powerFreePart 2)
  let D := (Finset.Icc 1 B).filter (fun a => a ∣ B)
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
    have hdvdB := powerFreePart_two_dvd_base_of_failure_of_avoids_primeSet
      P hPprime hproduct hmData.1 hmData.2 hfail
    change powerFreePart 2 m ∈ (Finset.Icc 1 B).filter (fun a => a ∣ B)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
      Nat.le_of_dvd hBpos hdvdB⟩, hdvdB⟩
  have hle := Finset.card_le_card hsubset
  change K ≤ G.card at hcount
  change D.card < K at hcandidates
  omega

theorem
    not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_twenty_one_le_of_le_seventy
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 21 ≤ H) (hHupper : H ≤ 70) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  apply not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_primeSet_base_count
    hSS (by omega) hHN (B := 30) (K := 9)
    (erdosSelfridgeExcludedPrimesFromSeven H)
  · intro p hp
    exact Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  · interval_cases H <;> decide
  · norm_num
  · exact
      nine_le_card_consecutiveInterval_twenty_one_to_seventy_avoiding_large_primes
        hHlower hHupper
  · decide

theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seventy
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 70) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hH20 : H ≤ 20
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_twenty
      hSS hHlower hH20 hHN
  · exact
      not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_twenty_one_le_of_le_seventy
        hSS (by omega) hHupper hHN

end Tao2026
