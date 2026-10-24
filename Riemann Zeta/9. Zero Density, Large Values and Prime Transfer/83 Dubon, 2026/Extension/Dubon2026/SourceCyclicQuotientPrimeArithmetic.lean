import Dubon2026.SourceEllipticCanonicalCyclicStep

/-! Arithmetic for the actual successive cyclic quotient construction.
An order invertible in the original field gives an invertible least prime
factor and smaller invertible quotient order. These discharge the recursive
prime-step hypotheses on the DUB-17/18 all-level inertia-census chain. -/

namespace Dubon2026.SourceEllipticCyclicCount
variable {F : Type*} [Field F]

/-- A divisor of an order nonzero in the original field is nonzero there. -/
theorem cast_ne_zero_of_dvd_order {a N : ℕ} (ha : a ∣ N) (hN : (N : F) ≠ 0) :
    (a : F) ≠ 0 := by
  obtain ⟨b, rfl⟩ := ha
  intro hz
  apply hN
  rw [Nat.cast_mul, hz, zero_mul]

/-- The least-prime step strictly decreases the positive order and preserves invertibility. -/
theorem cyclicQuotient_prime_arithmetic (N : ℕ) (hN : (N : F) ≠ 0) (hN1 : N ≠ 1) :
    N.minFac.Prime ∧ N / N.minFac ≠ 0 ∧ N / N.minFac < N ∧
      (N.minFac : F) ≠ 0 ∧ ((N / N.minFac : ℕ) : F) ≠ 0 := by
  have hN0 : N ≠ 0 := by intro he; apply hN; rw [he, Nat.cast_zero]
  have hp := Nat.minFac_prime hN1
  have he : N.minFac * (N / N.minFac) = N := Nat.mul_div_cancel' (Nat.minFac_dvd N)
  have hm : N / N.minFac ≠ 0 := by intro hz; rw [hz, mul_zero] at he; exact hN0 he.symm
  exact ⟨hp, hm, Nat.div_lt_self (Nat.pos_of_ne_zero hN0) hp.one_lt,
    cast_ne_zero_of_dvd_order (Nat.minFac_dvd N) hN,
    cast_ne_zero_of_dvd_order ⟨N.minFac, by rw [Nat.mul_comm, he]⟩ hN⟩

end Dubon2026.SourceEllipticCyclicCount
