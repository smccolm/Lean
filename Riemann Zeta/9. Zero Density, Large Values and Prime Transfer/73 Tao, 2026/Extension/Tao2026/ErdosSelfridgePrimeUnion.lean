import Tao2026.ErdosSelfridgeFiniteCounts

namespace Tao2026

/-- The number of multiples of `p` in an interval of length `H` is at most
the ceiling of `H/p`, written without integer ceiling notation. -/
theorem card_intervalMultiples_le_div_add_indicator
    (N H p : ℕ) (hp : 0 < p) :
    (intervalMultiples N H p).card ≤
      H / p + if p ∣ H then 0 else 1 := by
  by_cases hd : p ∣ H
  · have hexact := card_filter_dvd_Ioc_add_of_dvd N H p hd
    simpa [intervalMultiples, consecutiveInterval, hd] using hexact.le
  · simpa [hd] using card_intervalMultiples_le N H p hp

/-- The positions divisible by at least one prime in `P`. -/
def intervalPrimeMultiplesUnion (N H : ℕ) (P : Finset ℕ) : Finset ℕ :=
  P.biUnion (fun p => intervalMultiples N H p)

theorem card_intervalPrimeMultiplesUnion_le
    (N H : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    (intervalPrimeMultiplesUnion N H P).card ≤
      ∑ p ∈ P, (H / p + if p ∣ H then 0 else 1) := by
  rw [intervalPrimeMultiplesUnion]
  refine Finset.card_biUnion_le.trans ?_
  exact Finset.sum_le_sum fun p hp =>
    card_intervalMultiples_le_div_add_indicator N H p (hP p hp)

/-- If the total ceiling bound for the excluded primes leaves five positions,
then at least five interval elements avoid all those primes. -/
theorem five_le_card_filter_avoiding_primeSet
    {N H : ℕ} (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (hsum : (∑ p ∈ P, (H / p + if p ∣ H then 0 else 1)) + 5 ≤ H) :
    5 ≤ ((consecutiveInterval N H).filter
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
  have hdiff : (S \ B).card = S.card - (B ∩ S).card :=
    Finset.card_sdiff
  rw [Finset.inter_eq_left.mpr hBsub] at hdiff
  have hScard : S.card = H := by simp [S, consecutiveInterval]
  have hcard : 5 ≤ (S \ B).card := by omega
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

/-- The coefficient primes above three that can occur below lengths eighteen
and nineteen. -/
def erdosSelfridgeExcludedPrimesThroughSeventeen : Finset ℕ :=
  {5, 7, 11, 13, 17}

/-- The sharp union count leaves five usable terms at lengths eighteen and
nineteen. -/
theorem five_le_card_consecutiveInterval_eighteen_to_nineteen_avoiding_large_primes
    {N H : ℕ} (hHlower : 18 ≤ H) (hHupper : H ≤ 19) :
    5 ≤ ((consecutiveInterval N H).filter
      (fun m => ∀ p ∈ erdosSelfridgeExcludedPrimesThroughSeventeen,
        ¬ p ∣ m)).card := by
  apply five_le_card_filter_avoiding_primeSet
  · intro p hp
    simp only [erdosSelfridgeExcludedPrimesThroughSeventeen,
      Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  · interval_cases H <;> decide

/-- The coefficient primes above three that can occur below length twenty. -/
def erdosSelfridgeExcludedPrimesThroughNineteen : Finset ℕ :=
  {5, 7, 11, 13, 17, 19}

/-- The sharp union count also leaves five usable terms at length twenty. -/
theorem five_le_card_consecutiveInterval_twenty_avoiding_large_primes
    (N : ℕ) :
    5 ≤ ((consecutiveInterval N 20).filter
      (fun m => ∀ p ∈ erdosSelfridgeExcludedPrimesThroughNineteen,
        ¬ p ∣ m)).card := by
  apply five_le_card_filter_avoiding_primeSet
  · intro p hp
    simp only [erdosSelfridgeExcludedPrimesThroughNineteen,
      Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  · decide

end Tao2026
