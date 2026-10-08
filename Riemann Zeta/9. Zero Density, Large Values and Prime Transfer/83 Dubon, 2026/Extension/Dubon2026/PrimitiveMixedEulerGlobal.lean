import Dubon2026.PrimitiveMixedEulerLocal

/-! # The mixed norm inequality for the original global first and Rankin functions -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual Rankin local Euler factor has norm at least one on the real convergence ray. -/
theorem primitive_rankin_real_euler_norm_ge_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) {σ : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ‖ := by
  have hh := primitive_rankin_local_three_four_one f hk p hσ 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hh
  have hp : 1 ≤ ‖primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ‖ ^ 8 := by
    convert hh using 1
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    ring
  by_contra h
  have hl := pow_lt_one₀ (norm_nonneg (primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ))
    (lt_of_not_ge h) (show 8 ≠ 0 by omega)
  exact (not_lt_of_ge hp) hl

/-- The literal principal prime factor, including omission of exactly the primes dividing its modulus. -/
def principalPrimeEulerFactor (Q : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if (p : ℕ) ∣ Q then 1 else (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹

/-- The actual mixed norm inequality includes every good and ramified prime with its genuine factor. -/
theorem primitive_mixed_local_all_primes {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 ≤ ‖primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ *
      principalPrimeEulerFactor Q p σ ^ 2 *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p ((σ : ℂ) + Complex.I * y) ^ 4 *
          principalPrimeEulerFactor Q p ((σ : ℂ) + 2 * Complex.I * y) ^ 2‖ := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [principalPrimeEulerFactor, if_pos hpQ,
      primitiveSymmetricSpectralEulerFactor_bad f 1 p hpQ, one_pow, mul_one]
    exact primitive_rankin_real_euler_norm_ge_one f hk p hσ
  · simp only [principalPrimeEulerFactor, if_neg hpQ]
    exact primitive_good_mixed_euler_inequality f hk p hpQ hσ y

/-- The original Rankin convolution, actual principal L-function and true entire first symmetric continuation satisfy the mixed global inequality. -/
theorem primitive_mixed_global_inequality {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖rankinConvolutionGlobalContinuation f.toCuspForm (1 + x) *
      DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
        primitiveFirstContinuation f (1 + x + Complex.I * y) ^ 4 *
          DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2‖ := by
  have h0 : 1 < (1 + (x : ℂ)).re := by simp; exact hx
  have h1 : 1 < (1 + (x : ℂ) + Complex.I * y).re := by simpa using h0
  have h2 : 1 < (1 + (x : ℂ) + 2 * Complex.I * y).re := by simpa using h0
  rw [primitiveFirstContinuation_eq_symmetric f (by omega) h1]
  have hR := primitive_rankin_spectral_hasProd f (by omega) h0
  have hA := principal_incomplete_euler_hasProd Q h0
  have hU := primitive_first_symmetric_hasProd f (by omega) h1
  have hB := principal_incomplete_euler_hasProd Q h2
  change Tendsto _ atTop _ at hR hA hU hB
  have hlim := ((hR.mul (hA.pow 2)).mul (hU.pow 4)).mul (hB.pow 2)
  apply ge_of_tendsto hlim.norm
  apply Filter.Eventually.of_forall
  intro t
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, norm_prod]
  apply Finset.one_le_prod
  intro p _
  simpa only [principalPrimeEulerFactor, Complex.ofReal_add, Complex.ofReal_one,
    primitive_first_symmetric_local_factor] using
    primitive_mixed_local_all_primes f hk p (by linarith : 1 < 1 + x) y

end
end Dubon2026
