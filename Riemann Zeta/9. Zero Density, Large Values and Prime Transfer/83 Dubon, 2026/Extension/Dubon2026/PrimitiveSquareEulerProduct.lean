import Dubon2026.PrimitiveSquareEulerFactors

/-! # The genuine all-prime Rankin square Euler product -/

namespace Dubon2026

noncomputable section

/-- The actual primitive normalized coefficient squares supply the genuine convergent all-prime Euler product. -/
theorem primitive_square_lseries_euler_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' r : ℕ, primitiveSquareLocalTerm f p s r)
      (cuspRankinSeries f.toCuspForm s) := by
  have h1 : ((‖normalizedCuspCoefficients f.toCuspForm 1‖ ^ 2 : ℝ) : ℂ) * (1 : ℂ) ^ (-s) = 1 := by
    rw [normalizedCuspCoefficients_one f.toCuspForm f.normalized]
    simp
  have hm : ∀ m n : ℕ, m.Coprime n →
      ((‖normalizedCuspCoefficients f.toCuspForm (m * n)‖ ^ 2 : ℝ) : ℂ) *
        ((m * n : ℕ) : ℂ) ^ (-s) =
      (((‖normalizedCuspCoefficients f.toCuspForm m‖ ^ 2 : ℝ) : ℂ) * (m : ℂ) ^ (-s)) *
      (((‖normalizedCuspCoefficients f.toCuspForm n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
    intro m n hmn
    rw [primitiveCuspForm_normalized_mul f m n hmn, norm_mul, mul_pow, Complex.ofReal_mul,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have h0 : ((‖normalizedCuspCoefficients f.toCuspForm 0‖ ^ 2 : ℝ) : ℂ) * (0 : ℂ) ^ (-s) = 0 := by
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  have he := EulerProduct.eulerProduct_hasProd
    (f := fun n => ((‖normalizedCuspCoefficients f.toCuspForm n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s))
    (by simpa only [Nat.cast_one] using h1) (fun {m n} h => hm m n h)
    (summable_normalized_cusp_square_dirichlet f.toCuspForm hk hs).norm
    (by simpa only [Nat.cast_zero] using h0)
  simpa only [← primitiveSquareLocalTerm_eq_dirichlet, ← cuspRankinSeries_eq_tsum] using he

/-- The actual ramified local square terms have their precise geometric form. -/
theorem primitiveSquareLocalTerm_bad {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q) (s : ℂ) (r : ℕ) :
    primitiveSquareLocalTerm f p s r =
      (((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (p : ℂ) ^ (-s)) ^ r := by
  rw [primitiveSquareLocalTerm, primitiveCuspForm_normalized_bad_prime_power f hp hpQ, norm_pow]
  rw [← pow_mul, Nat.mul_comm r 2, pow_mul, Complex.ofReal_pow, mul_pow]

/-- The genuine ramified Rankin local factor is the inverse of its actual linear square-coefficient denominator. -/
theorem primitive_bad_square_euler_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveSquareLocalTerm f p s r) =
      (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
  have he := tsum_second_order_eq_euler_inverse (b := 0)
    (summable_primitiveSquareLocalTerm f hk hp hs)
    (by rw [primitiveSquareLocalTerm_bad f hp hpQ, pow_zero])
    (by rw [primitiveSquareLocalTerm_bad f hp hpQ, pow_one])
    (by intro r; simp only [primitiveSquareLocalTerm_bad f hp hpQ, zero_mul, sub_zero];
        exact pow_succ' _ (r + 1))
  simpa only [add_zero] using he

/-- Actual convergence forces each genuine ramified square denominator to be nonzero on Re(s)>1. -/
theorem primitive_bad_square_denominator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (p : ℂ) ^ (-s) ≠ 0 := by
  have he := second_order_euler_denominator_ne_zero (b := 0)
    (summable_primitiveSquareLocalTerm f hk hp hs)
    (by rw [primitiveSquareLocalTerm_bad f hp hpQ, pow_zero])
    (by rw [primitiveSquareLocalTerm_bad f hp hpQ, pow_one])
    (by intro r; simp only [primitiveSquareLocalTerm_bad f hp hpQ, zero_mul, sub_zero];
        exact pow_succ' _ (r + 1))
  simpa only [add_zero] using he

end
end Dubon2026
