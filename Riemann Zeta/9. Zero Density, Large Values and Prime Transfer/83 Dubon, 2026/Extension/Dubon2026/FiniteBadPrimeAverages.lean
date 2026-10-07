import Dubon2026.BadPrimeDensity

/-! # Exact finite bad-prime errors in genuine prime averages -/

namespace Dubon2026

open Filter Set
open scoped Topology

noncomputable section

/-- Once the cutoff exceeds the level, the discrepancy of two good-prime-equal sequences is a fixed finite sum. -/
theorem prime_sum_difference_of_good_eq {u v : ℕ → ℝ} {Q : ℕ} (hQ : 0 < Q)
    (huv : ∀ p, Nat.Prime p → ¬p ∣ Q → u p = v p) {N : ℕ} (hN : Q ≤ N) :
    (∑ p ∈ Nat.primesLE N, u p) - (∑ p ∈ Nat.primesLE N, v p) =
      ∑ p ∈ Nat.primesLE Q, (u p - v p) := by
  classical
  rw [← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨hpQ, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpQ.trans hN, hp⟩
  · intro p hpN hpQ
    have hp := (Nat.mem_primesLE.mp hpN).2
    have hn : ¬p ∣ Q := fun hd => hpQ (Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hQ hd, hp⟩)
    exact sub_eq_zero.mpr (huv p hp hn)

/-- Finitely many bad-prime discrepancies vanish in the literal prime-count normalized average. -/
theorem tendsto_prime_average_difference_of_good_eq {u v : ℕ → ℝ} {Q : ℕ} (hQ : 0 < Q)
    (huv : ∀ p, Nat.Prime p → ¬p ∣ Q → u p = v p) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N -
      (∑ p ∈ Nat.primesLE N, v p) / Nat.primeCounting N) atTop (𝓝 0) := by
  have hh := (tendsto_const_div_atTop_nhds_zero_nat
    (∑ p ∈ Nat.primesLE Q, (u p - v p))).comp Nat.tendsto_primeCounting
  apply hh.congr'
  filter_upwards [eventually_ge_atTop Q] with N hN
  rw [← sub_div, prime_sum_difference_of_good_eq hQ huv hN]
  rfl

/-- A uniform bound away from the level gives a genuine common bound including every bad prime. -/
theorem exists_prime_value_bound_of_good_bound {x : ℕ → ℝ} {Q : ℕ} (hQ : 0 < Q)
    (hx : ∀ p, Nat.Prime p → ¬p ∣ Q → |x p| ≤ 2) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ p, Nat.Prime p → |x p| ≤ C := by
  classical
  let C : ℝ := (∑ p ∈ Nat.primesLE Q, |x p|) + 2
  have hs : 0 ≤ ∑ p ∈ Nat.primesLE Q, |x p| := Finset.sum_nonneg (fun p _ => abs_nonneg (x p))
  refine ⟨C, by dsimp [C]; linarith, fun p hp => ?_⟩
  by_cases hd : p ∣ Q
  · have hm : p ∈ Nat.primesLE Q := Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hQ hd, hp⟩
    have he := Finset.single_le_sum (fun q (_ : q ∈ Nat.primesLE Q) => abs_nonneg (x q)) hm
    dsimp only [C]
    linarith
  · exact (hx p hp hd).trans (by dsimp [C]; linarith)

end
end Dubon2026
