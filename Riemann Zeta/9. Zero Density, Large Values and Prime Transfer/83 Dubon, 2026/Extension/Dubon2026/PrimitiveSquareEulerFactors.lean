import Dubon2026.ThirdOrderRecurrenceSeries
import Dubon2026.PrimitiveFirstSymmetricL

/-! # Genuine Rankin square-coefficient Euler factors and the symmetric-square polynomial -/

namespace Dubon2026

noncomputable section

/-- The squared norm of a real-valued complex coefficient is its literal complex square. -/
theorem complex_norm_sq_eq_sq_of_im_zero {z : ℂ} (hz : z.im = 0) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z ^ 2 := by
  rw [Complex.sq_norm]
  apply Complex.ext <;> simp [Complex.normSq_apply, pow_two, hz]

/-- The degree-two actual spectral Euler polynomial has precisely the cubic recurrence denominator. -/
theorem symmetricEulerPolynomial_two_eval {α β : ℂ} (hp : α * β = 1) (z : ℂ) :
    (symmetricEulerPolynomial α β 2).eval z =
      1 - ((α + β) ^ 2 - 1) * z + ((α + β) ^ 2 - 1) * z ^ 2 - z ^ 3 := by
  have hs : α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 := by linear_combination -2 * hp
  have hc : α ^ 2 * β ^ 2 = 1 := by
    calc
      _ = (α * β) ^ 2 := by ring
      _ = _ := by rw [hp, one_pow]
  have he : (1 - α ^ 2 * z) * (1 - β ^ 2 * z) =
      1 - ((α + β) ^ 2 - 2) * z + z ^ 2 := by
    linear_combination -z * hs + z ^ 2 * hc
  have hd : (symmetricEulerPolynomial α β 2).eval z =
      (1 - β ^ 2 * z) * (1 - α * β * z) * (1 - α ^ 2 * z) := by
    norm_num [symmetricEulerPolynomial_eval, Finset.prod_range_succ]
  rw [hd, hp]
  calc
    _ = (1 - z) * ((1 - α ^ 2 * z) * (1 - β ^ 2 * z)) := by ring
    _ = _ := by rw [he]; ring

/-- The genuine normalized square coefficient at a prime power with its original local Dirichlet coordinate. -/
def primitiveSquareLocalTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  ((‖normalizedCuspCoefficients f.toCuspForm (p ^ r)‖ ^ 2 : ℝ) : ℂ) * ((p : ℂ) ^ (-s)) ^ r

/-- These local square terms are exactly the actual Rankin series summands at prime powers. -/
theorem primitiveSquareLocalTerm_eq_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) (s : ℂ) (r : ℕ) :
    primitiveSquareLocalTerm f p s r =
      ((‖normalizedCuspCoefficients f.toCuspForm (p ^ r)‖ ^ 2 : ℝ) : ℂ) *
        ((p ^ r : ℕ) : ℂ) ^ (-s) := by
  unfold primitiveSquareLocalTerm
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- The proved actual Rankin series convergence supplies every genuine prime-square local series. -/
theorem summable_primitiveSquareLocalTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : 1 < s.re) : Summable (primitiveSquareLocalTerm f p s) := by
  have he := (summable_normalized_cusp_square_dirichlet f.toCuspForm hk hs).comp_injective
    (Nat.pow_right_injective hp.one_lt)
  exact he.congr (fun r => (primitiveSquareLocalTerm_eq_dirichlet f p s r).symm)

/-- At good primes the actual square coefficient equals the square of the genuine real normalized coefficient. -/
theorem primitiveSquareLocalTerm_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (s : ℂ) (r : ℕ) :
    primitiveSquareLocalTerm f p s r =
      normalizedCuspCoefficients f.toCuspForm (p ^ r) ^ 2 * ((p : ℂ) ^ (-s)) ^ r := by
  rw [primitiveSquareLocalTerm, complex_norm_sq_eq_sq_of_im_zero
    (primitiveCuspForm_normalizedCoefficient_im f _ ((hp.coprime_iff_not_dvd.mpr hpQ).pow_left r))]

/-- The genuine Rankin square local series has numerator 1+p^(-s) and exactly the actual symmetric-square spectral denominator. -/
theorem primitive_good_square_euler_identity {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (primitiveSymmetricEulerPolynomial f p 2).eval ((p : ℂ) ^ (-s)) *
      (∑' r : ℕ, primitiveSquareLocalTerm f p s r) = 1 + (p : ℂ) ^ (-s) := by
  have hsum : Summable (fun r : ℕ => normalizedCuspCoefficients f.toCuspForm (p ^ r) ^ 2 *
      ((p : ℂ) ^ (-s)) ^ r) :=
    (summable_primitiveSquareLocalTerm f hk hp hs).congr
      (primitiveSquareLocalTerm_good f hp hpQ s)
  have he := tsum_square_recurrence_euler
    (by simp only [pow_zero, normalizedCuspCoefficients_one f.toCuspForm f.normalized])
    (by simp only [pow_one]) (primitiveCuspForm_normalized_primePower_recurrence f hp hpQ) hsum
  rw [primitiveSymmetricEulerPolynomial,
    symmetricEulerPolynomial_two_eval (primitiveSatake_trace_det f p).2,
    (primitiveSatake_trace_det f p).1]
  simpa only [primitiveSquareLocalTerm_good f hp hpQ] using he

end
end Dubon2026
