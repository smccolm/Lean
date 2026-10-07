import Dubon2026.PrimitiveEulerFactors

/-! # All-prime Euler product of the actual normalized primitive cusp form -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The ramified prime-power normalization preserves the actual one-root coefficient law. -/
theorem primitiveCuspForm_normalized_bad_prime_power {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q) (r : ℕ) :
    normalizedCuspCoefficients f.toCuspForm (p ^ r) =
      normalizedCuspCoefficients f.toCuspForm p ^ r := by
  simp only [normalizedCuspCoefficients, shiftedCoefficients,
    primitiveCuspForm_bad_prime_power f hp hpQ, nat_power_cpow_real, mul_pow]

/-- The actual ramified local summands are powers of the genuine normalized prime summand. -/
theorem primitiveLocalTerm_bad {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q) (s : ℂ) (r : ℕ) :
    primitiveLocalTerm f p s r =
      (normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s)) ^ r := by
  rw [primitiveLocalTerm, primitiveCuspForm_normalized_bad_prime_power f hp hpQ, mul_pow]

/-- Actual global convergence and the ramified Hecke relation give the exact linear Euler factor. -/
theorem primitive_bad_euler_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveLocalTerm f p s r) =
      (1 - normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s))⁻¹ := by
  have he := tsum_second_order_eq_euler_inverse (b := 0)
    (summable_primitiveLocalTerm f hk hp hs)
    (by rw [primitiveLocalTerm_bad f hp hpQ, pow_zero])
    (by rw [primitiveLocalTerm_bad f hp hpQ, pow_one])
    (by intro r; simp only [primitiveLocalTerm_bad f hp hpQ, zero_mul, sub_zero];
        exact pow_succ' _ (r + 1))
  simpa only [add_zero] using he

/-- The actual degree-one or degree-two local Euler polynomial, according to ramification. -/
def primitiveEulerDenominator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) (s : ℂ) : ℂ :=
  1 - normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s) +
    if p ∣ Q then 0 else ((p : ℂ) ^ (-s)) ^ 2

/-- Every local series equals its correct Euler factor, including all primes dividing the level. -/
theorem primitive_euler_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveLocalTerm f p s r) = (primitiveEulerDenominator f p s)⁻¹ := by
  by_cases hpQ : p ∣ Q
  · simpa only [primitiveEulerDenominator, if_pos hpQ, add_zero] using
      primitive_bad_euler_series f hk hp hpQ hs
  · simpa only [primitiveEulerDenominator, if_neg hpQ] using
      primitive_good_euler_series f hk hp hpQ hs

/-- No actual local Euler denominator vanishes in the absolutely convergent half-plane. -/
theorem primitiveEulerDenominator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : 1 < s.re) : primitiveEulerDenominator f p s ≠ 0 := by
  by_cases hpQ : p ∣ Q
  · have he := second_order_euler_denominator_ne_zero (b := 0)
      (summable_primitiveLocalTerm f hk hp hs)
      (by rw [primitiveLocalTerm_bad f hp hpQ, pow_zero])
      (by rw [primitiveLocalTerm_bad f hp hpQ, pow_one])
      (by intro r; simp only [primitiveLocalTerm_bad f hp hpQ, zero_mul, sub_zero];
          exact pow_succ' _ (r + 1))
    simpa only [primitiveEulerDenominator, if_pos hpQ] using he
  · simpa only [primitiveEulerDenominator, if_neg hpQ] using
      second_order_euler_denominator_ne_zero (summable_primitiveLocalTerm f hk hp hs)
      (by simp only [primitiveLocalTerm, pow_zero, mul_one,
        normalizedCuspCoefficients_one f.toCuspForm f.normalized])
      (by simp only [primitiveLocalTerm, pow_one])
      (primitiveLocalTerm_good_recurrence f hp hpQ s)

/-- The true normalized cusp L-series is the all-prime product of its actual rational Euler factors. -/
theorem primitive_cusp_lseries_rational_euler_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (primitiveEulerDenominator f p s)⁻¹)
      (LSeries (normalizedCuspCoefficients f.toCuspForm) s) := by
  have he := primitive_cusp_lseries_euler_hasProd f hk hs
  have hf : (fun p : Nat.Primes => ∑' r : ℕ,
      normalizedCuspCoefficients f.toCuspForm ((p : ℕ) ^ r) *
        (((p : ℕ) ^ r : ℕ) : ℂ) ^ (-s)) =
      (fun p : Nat.Primes => (primitiveEulerDenominator f p s)⁻¹) := by
    funext p
    simp_rw [← primitiveLocalTerm_eq_dirichlet]
    exact primitive_euler_series f hk p.property hs
  rwa [hf] at he

end
end Dubon2026
