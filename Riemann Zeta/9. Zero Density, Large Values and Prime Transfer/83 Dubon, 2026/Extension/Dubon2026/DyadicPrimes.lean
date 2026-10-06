import Dubon2026.IsolatedPrimeSupport
import Mathlib.NumberTheory.PrimeCounting

/-! # The literal isolated-prime block (N/2,N] and its exact cardinality -/

namespace Dubon2026

open Filter Set

noncomputable section

/-- All primes in the source's open/closed dyadic interval. -/
def dyadicPrimes (N : ℕ) : Finset ℕ := (Finset.Ioc (N / 2) N).filter Nat.Prime

theorem mem_dyadicPrimes {N p : ℕ} : p ∈ dyadicPrimes N ↔
    Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ioc]
  have hiff : N / 2 < p ↔ (N : ℝ) / 2 < p := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ)), div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    norm_cast
  tauto

theorem isolatedPrimeBlocks_dyadicPrimes : IsolatedPrimeBlocks dyadicPrimes :=
  fun _ _ hp => mem_dyadicPrimes.mp hp

theorem dyadicPrimes_eq_sdiff (N : ℕ) :
    dyadicPrimes N = Nat.primesLE N \ Nat.primesLE (N / 2) := by
  ext p
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨⟨hu, hp⟩, fun h => (not_le_of_gt hl) h.1⟩
  · rintro ⟨⟨hu, hp⟩, hn⟩
    exact ⟨⟨by by_contra h; exact hn ⟨by omega, hp⟩, hu⟩, hp⟩

theorem card_dyadicPrimes (N : ℕ) :
    (dyadicPrimes N).card = Nat.primeCounting N - Nat.primeCounting (N / 2) := by
  rw [dyadicPrimes_eq_sdiff, Finset.card_sdiff_of_subset]
  · rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.div_le_self N 2),
      (Nat.mem_primesLE.mp hp).2⟩

end

end Dubon2026
