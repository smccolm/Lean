import Dubon2026.TorusPolynomial

/-! # Isolated primes occur only as linear terms in the actual finite Bohr polynomial -/

namespace Dubon2026

noncomputable section

theorem isolated_divisor_eq {n N p : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (hpN : N < 2 * p) (hpn : p ∣ n) : n = p := by
  obtain ⟨k, hk⟩ := hpn
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, mul_zero] at hk
    omega
  have hklt : k < 2 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left p hk2
    nlinarith
  have hk1 : k = 1 := by omega
  simpa [hk1] using hk

theorem isolated_factorization_eq_zero {n N p : ℕ} (hnN : n ≤ N)
    (hpN : N < 2 * p) (hne : n ≠ p) : n.factorization p = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  apply Nat.factorization_eq_zero_of_not_dvd
  exact fun hd => hne (isolated_divisor_eq (by omega) hnN hpN hd)

theorem bohrMonomial_prime (N : ℕ) (p : PrimeCoordinate N) (z : PrimeCoordinate N → ℂ) :
    bohrMonomial N p.val z = z p := by
  classical
  have hp := (mem_primesUpTo.mp p.property).1
  unfold bohrMonomial
  rw [hp.factorization]
  calc
    (∏ q : PrimeCoordinate N, z q ^ (Finsupp.single p.val 1) q.val) =
        z p ^ (Finsupp.single p.val 1) p.val := by
      apply Finset.prod_eq_single p
      · intro q _ hqp
        have hv : p.val ≠ q.val := fun h => hqp (Subtype.ext h.symm)
        rw [Finsupp.single_eq_of_ne' hv, pow_zero]
      · simp
    _ = z p := by simp

theorem bohrMonomial_eq_of_agree_off_isolated {N n : ℕ} (hnN : n ≤ N)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, N < 2 * p) (hnQ : n ∉ Q)
    (z w : PrimeCoordinate N → ℂ) (hzw : ∀ p : PrimeCoordinate N, p.val ∉ Q → z p = w p) :
    bohrMonomial N n z = bohrMonomial N n w := by
  classical
  unfold bohrMonomial
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p.val ∈ Q
  · rw [isolated_factorization_eq_zero hnN (hQ p.val hp) (fun h => hnQ (h.symm ▸ hp))]
    simp
  · rw [hzw p hp]

end

end Dubon2026
