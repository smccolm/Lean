import Dubon2026.IsolatedPrimeMonomials

/-! # Exact removal and linear reconstruction of the isolated prime coordinates -/

namespace Dubon2026

noncomputable section

/-- Set the selected complex coordinates to zero, keeping every other coordinate. -/
def erasePrimeCoordinates {N : ℕ} (S : Finset (PrimeCoordinate N))
    (z : PrimeCoordinate N → ℂ) : PrimeCoordinate N → ℂ :=
  fun p => if p ∈ S then 0 else z p

theorem isolatedBohr_decomposition (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (S : Finset (PrimeCoordinate N)) (hS : ∀ p ∈ S, N < 2 * p.val)
    (z : PrimeCoordinate N → ℂ) :
    bohrLift a N σ z = bohrLift a N σ (erasePrimeCoordinates S z) +
      ∑ p ∈ S, a p.val * (p.val : ℂ) ^ (-(σ : ℂ)) * z p := by
  classical
  let Q : Finset ℕ := S.image Subtype.val
  have hQN : Q ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpp := mem_primesUpTo.mp p.property
    exact Finset.mem_Icc.mpr ⟨hpp.1.one_lt.le, hpp.2⟩
  have hQ : ∀ p ∈ Q, N < 2 * p := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hS p hp
  have hrest {n : ℕ} (hn : n ≤ N) (hnQ : n ∉ Q) :
      bohrMonomial N n z = bohrMonomial N n (erasePrimeCoordinates S z) := by
    apply bohrMonomial_eq_of_agree_off_isolated hn Q hQ hnQ
    intro p hp
    unfold erasePrimeCoordinates
    rw [if_neg (fun h => hp (Finset.mem_image.mpr ⟨p, h, rfl⟩))]
  have hsum : (∑ n ∈ Q, (a n * (n : ℂ) ^ (-(σ : ℂ)) * bohrMonomial N n z -
      a n * (n : ℂ) ^ (-(σ : ℂ)) * bohrMonomial N n (erasePrimeCoordinates S z))) =
      ∑ n ∈ Finset.Icc 1 N, (a n * (n : ℂ) ^ (-(σ : ℂ)) * bohrMonomial N n z -
        a n * (n : ℂ) ^ (-(σ : ℂ)) * bohrMonomial N n (erasePrimeCoordinates S z)) := by
    apply Finset.sum_subset hQN
    intro n hn hnQ
    rw [hrest (Finset.mem_Icc.mp hn).2 hnQ, sub_self]
  apply sub_eq_iff_eq_add'.mp
  rw [bohrLift, bohrLift, ← Finset.sum_sub_distrib, ← hsum]
  rw [show Q = S.image Subtype.val from rfl, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [bohrMonomial_prime, bohrMonomial_prime]
    simp [erasePrimeCoordinates, hp]
  · intro p _ q _ hpq
    exact Subtype.ext hpq

end

end Dubon2026
