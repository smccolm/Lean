import Tao2026.ErdosSelfridgeFinite
import Tao2026.IntervalMultiples

namespace Tao2026

/-- Four individual multiple-count bounds give a lower bound for the terms
avoiding all four primes. -/
theorem five_le_card_consecutiveInterval_filter_not_five_seven_eleven_thirteen
    {N H c5 c7 c11 c13 : ℕ}
    (h5 : (intervalMultiples N H 5).card ≤ c5)
    (h7 : (intervalMultiples N H 7).card ≤ c7)
    (h11 : (intervalMultiples N H 11).card ≤ c11)
    (h13 : (intervalMultiples N H 13).card ≤ c13)
    (hsum : c5 + c7 + c11 + c13 + 5 ≤ H) :
    5 ≤ ((consecutiveInterval N H).filter
      (fun m => ¬ 5 ∣ m ∧ ¬ 7 ∣ m ∧ ¬ 11 ∣ m ∧ ¬ 13 ∣ m)).card := by
  let S := consecutiveInterval N H
  let B5 := intervalMultiples N H 5
  let B7 := intervalMultiples N H 7
  let B11 := intervalMultiples N H 11
  let B13 := intervalMultiples N H 13
  let B := (((B5 ∪ B7) ∪ B11) ∪ B13)
  have hBad : S.filter
      (fun m => 5 ∣ m ∨ 7 ∣ m ∨ 11 ∣ m ∨ 13 ∣ m) = B := by
    ext m
    simp only [S, B, B5, B7, B11, B13, intervalMultiples,
      Finset.mem_filter, Finset.mem_union]
    tauto
  have hB5B7 := Finset.card_union_le B5 B7
  have hB11 := Finset.card_union_le (B5 ∪ B7) B11
  have hB13 := Finset.card_union_le ((B5 ∪ B7) ∪ B11) B13
  have hBcard : B.card ≤ c5 + c7 + c11 + c13 := by
    dsimp only [B, B5, B7, B11, B13] at hB13 ⊢
    dsimp only [B5, B7] at hB5B7
    dsimp only [B5, B7, B11] at hB11
    omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (fun m => 5 ∣ m ∨ 7 ∣ m ∨ 11 ∣ m ∨ 13 ∣ m)
  have hScard : S.card = H := by simp [S, consecutiveInterval]
  rw [hBad] at hpartition
  have hgood : 5 ≤ (S.filter
      (fun m => ¬ (5 ∣ m ∨ 7 ∣ m ∨ 11 ∣ m ∨ 13 ∣ m))).card := by
    omega
  simpa only [not_or] using hgood

theorem five_le_card_consecutiveInterval_fourteen_to_seventeen_avoiding_large_primes
    {N H : ℕ} (hHlower : 14 ≤ H) (hHupper : H ≤ 17) :
    5 ≤ ((consecutiveInterval N H).filter
      (fun m => ¬ 5 ∣ m ∧ ¬ 7 ∣ m ∧ ¬ 11 ∣ m ∧ ¬ 13 ∣ m)).card := by
  interval_cases H
  · apply
      five_le_card_consecutiveInterval_filter_not_five_seven_eleven_thirteen
        (c5 := 3) (c7 := 2) (c11 := 2) (c13 := 2)
    · simpa using card_intervalMultiples_le N 14 5 (by norm_num)
    · simpa [intervalMultiples, consecutiveInterval] using
        (card_filter_dvd_Ioc_add_of_dvd N 14 7 (by norm_num)).le
    · simpa using card_intervalMultiples_le N 14 11 (by norm_num)
    · simpa using card_intervalMultiples_le N 14 13 (by norm_num)
    · norm_num
  · apply
      five_le_card_consecutiveInterval_filter_not_five_seven_eleven_thirteen
        (c5 := 3) (c7 := 3) (c11 := 2) (c13 := 2)
    · simpa [intervalMultiples, consecutiveInterval] using
        (card_filter_dvd_Ioc_add_of_dvd N 15 5 (by norm_num)).le
    · simpa using card_intervalMultiples_le N 15 7 (by norm_num)
    · simpa using card_intervalMultiples_le N 15 11 (by norm_num)
    · simpa using card_intervalMultiples_le N 15 13 (by norm_num)
    · norm_num
  · apply
      five_le_card_consecutiveInterval_filter_not_five_seven_eleven_thirteen
        (c5 := 4) (c7 := 3) (c11 := 2) (c13 := 2)
    · simpa using card_intervalMultiples_le N 16 5 (by norm_num)
    · simpa using card_intervalMultiples_le N 16 7 (by norm_num)
    · simpa using card_intervalMultiples_le N 16 11 (by norm_num)
    · simpa using card_intervalMultiples_le N 16 13 (by norm_num)
    · norm_num
  · apply
      five_le_card_consecutiveInterval_filter_not_five_seven_eleven_thirteen
        (c5 := 4) (c7 := 3) (c11 := 2) (c13 := 2)
    · simpa using card_intervalMultiples_le N 17 5 (by norm_num)
    · simpa using card_intervalMultiples_le N 17 7 (by norm_num)
    · simpa using card_intervalMultiples_le N 17 11 (by norm_num)
    · simpa using card_intervalMultiples_le N 17 13 (by norm_num)
    · norm_num

/-- Candidate coefficients after removing the primes from five through
thirteen. -/
def erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen
    (H : ℕ) : Finset ℕ :=
  (erdosSelfridgeSquareCoefficientCandidates H).filter
    (fun a => ¬ 5 ∣ a ∧ ¬ 7 ∣ a ∧ ¬ 11 ∣ a ∧ ¬ 13 ∣ a)

theorem powerFreePart_two_mem_candidatesWithoutFiveThroughThirteen_of_failure
    {N H m : ℕ} (hHlower : 14 ≤ H) (hHupper : H ≤ 17)
    (hm : m ∈ consecutiveInterval N H)
    (h5m : ¬ 5 ∣ m) (h7m : ¬ 7 ∣ m) (h11m : ¬ 11 ∣ m)
    (h13m : ¬ 13 ∣ m)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    powerFreePart 2 m ∈
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen H := by
  rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen,
    Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
    Finset.mem_filter, Finset.mem_Icc]
  have hdvd :=
    powerFreePart_two_dvd_erdosSelfridgePrimeProduct_of_failure hm hfail
  have hprod : erdosSelfridgePrimeProduct H = 30030 := by
    interval_cases H <;> decide
  rw [hprod] at hdvd
  have hdecomp := powerFreePart_mul_powerRootPart_pow (l := 2)
    (n := m) (by
      have := (Finset.mem_Ioc.mp hm).1
      omega)
  have hnotFive : ¬ 5 ∣ powerFreePart 2 m := by
    intro ha
    apply h5m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left ha _
  have hnotSeven : ¬ 7 ∣ powerFreePart 2 m := by
    intro ha
    apply h7m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left ha _
  have hnotEleven : ¬ 11 ∣ powerFreePart 2 m := by
    intro ha
    apply h11m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left ha _
  have hnotThirteen : ¬ 13 ∣ powerFreePart 2 m := by
    intro ha
    apply h13m
    rw [← hdecomp]
    exact dvd_mul_of_dvd_left ha _
  simp only [hprod]
  exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (powerFreePart_ne_zero _ _),
    Nat.le_of_dvd (by norm_num) hdvd⟩, hdvd⟩,
    hnotFive, hnotSeven, hnotEleven, hnotThirteen⟩

/-- Section 3.2 for the uniform lengths fourteen through seventeen. -/
theorem
    not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_fourteen_le_of_le_seventeen
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 14 ≤ H) (hHupper : H ≤ 17) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  let G := (consecutiveInterval N H).filter
    (fun m => ¬ 5 ∣ m ∧ ¬ 7 ∣ m ∧ ¬ 11 ∣ m ∧ ¬ 13 ∣ m)
  let A := G.image (powerFreePart 2)
  have hGcard : 5 ≤ G.card :=
    five_le_card_consecutiveInterval_fourteen_to_seventeen_avoiding_large_primes
      hHlower hHupper
  have hinj : Set.InjOn (powerFreePart 2) G :=
    (powerFreePart_two_injOn_consecutiveInterval_of_failure
      hSS (by omega) hHN hfail).mono (Finset.filter_subset _ _)
  have hcard : A.card = G.card := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj]
  have hsubset : A ⊆
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen H := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hmData := Finset.mem_filter.mp hm
    exact
      powerFreePart_two_mem_candidatesWithoutFiveThroughThirteen_of_failure
        hHlower hHupper hmData.1 hmData.2.1 hmData.2.2.1 hmData.2.2.2.1
        hmData.2.2.2.2 hfail
  let D := (Finset.Icc 1 6).filter (fun a => a ∣ 6)
  have hcandidates :
      erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen H ⊆
        D := by
    intro a ha
    rw [erdosSelfridgeSquareCoefficientCandidatesWithoutFiveThroughThirteen,
      Finset.mem_filter, erdosSelfridgeSquareCoefficientCandidates,
      Finset.mem_filter, Finset.mem_Icc] at ha
    have hprod : erdosSelfridgePrimeProduct H = 30030 := by
      interval_cases H <;> decide
    rw [hprod] at ha
    have h5c : a.Coprime 5 :=
      ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr ha.2.1).symm
    have h7c : a.Coprime 7 :=
      ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr ha.2.2.1).symm
    have h11c : a.Coprime 11 :=
      ((show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr
        ha.2.2.2.1).symm
    have h13c : a.Coprime 13 :=
      ((show Nat.Prime 13 by norm_num).coprime_iff_not_dvd.mpr
        ha.2.2.2.2).symm
    have hc : a.Coprime (5 * 7 * 11 * 13) :=
      ((h5c.mul_right h7c).mul_right h11c).mul_right h13c
    have hadvd : a ∣ (5 * 7 * 11 * 13) * 6 := by
      norm_num
      exact ha.1.2
    have hadvd6 : a ∣ 6 := hc.dvd_of_dvd_mul_left hadvd
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ha.1.1.1, Nat.le_of_dvd (by norm_num) hadvd6⟩, hadvd6⟩
  have hDcard : D.card = 4 := by decide
  have hle := Finset.card_le_card (hsubset.trans hcandidates)
  omega

/-- Combined finite Section 3.2 endpoint through length seventeen. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seventeen
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 3 ≤ H) (hHupper : H ≤ 17) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hH13 : H ≤ 13
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_thirteen
      hSS hHlower hH13 hHN
  · exact
      not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_fourteen_le_of_le_seventeen
        hSS (by omega) hHupper hHN

end Tao2026
