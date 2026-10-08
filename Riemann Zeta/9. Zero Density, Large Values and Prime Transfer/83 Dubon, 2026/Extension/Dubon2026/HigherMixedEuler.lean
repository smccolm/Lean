import Dubon2026.FiniteTensorEulerInequality
import Dubon2026.HigherAugmentedEuler

/-! # Mixed norm inequalities for every actual higher symmetric Euler function -/

namespace Dubon2026

noncomputable section
open Filter
open scoped Topology

/-- The true even symmetric tensor factors and original symmetric factor satisfy the mixed
Euler inequality at every prime, with exactly the ramified factors omitted. -/
theorem primitive_higher_mixed_local {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) (p : Nat.Primes) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 ≤ ‖(∏ t ∈ Finset.range (r + 1),
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p σ) *
      principalPrimeEulerFactor Q p σ ^ 2 *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p ((σ : ℂ) + Complex.I * y) ^ 4 *
          principalPrimeEulerFactor Q p ((σ : ℂ) + 2 * Complex.I * y) ^ 2‖ := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp [principalPrimeEulerFactor, hpQ, primitiveSymmetricSpectralEulerFactor_bad f _ p hpQ]
  · let a : ℝ := ((p : ℕ) : ℝ) ^ (-σ)
    have ha : (a : ℂ) = (((p : ℕ) : ℂ) ^ (-(σ : ℂ))) := by
      dsimp only [a]
      rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
      simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
    have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith)
    have hh := finiteTensorEuler_mixed_rankin (primitiveSymmetricSpectralRoots f r p)
      (a := a) (by dsimp [a]; positivity) ha1
      (norm_primitiveSymmetricSpectralRoots_le f hbound r p)
      (primitiveSymmetricSpectral_power_trace_real f r p) (norm_prime_cpow_imaginary p y)
    have he : (∏ i : Fin (r + 1) × Fin (r + 1),
        (1 - (primitiveSymmetricSpectralRoots f r p i.1 * primitiveSymmetricSpectralRoots f r p i.2) * (a : ℂ)))⁻¹ =
        ∏ t ∈ Finset.range (r + 1), primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p σ := by
      rw [ha, ← Finset.prod_inv_distrib]
      exact primitiveHigherTensor_euler_factor f r p σ
    rw [he] at hh
    simpa only [principalPrimeEulerFactor, if_neg hpQ, primeSpectralEulerFactor,
      ← ha, prime_cpow_vertical_split p σ y, prime_cpow_vertical_twice p σ y] using hh

/-- The exact prime-product limits give the actual global higher mixed Euler norm inequality. -/
theorem primitive_higher_mixed_global {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖(∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) (1 + x)) *
      DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
        primitiveSymmetricLFunction f r (1 + x + Complex.I * y) ^ 4 *
          DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2‖ := by
  have h0 : 1 < (1 + (x : ℂ)).re := by simp; exact hx
  have h1 : 1 < (1 + (x : ℂ) + Complex.I * y).re := by simpa using h0
  have h2 : 1 < (1 + (x : ℂ) + 2 * Complex.I * y).re := by simpa using h0
  have hR : HasProd (fun p : Nat.Primes => ∏ t ∈ Finset.range (r + 1),
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p (1 + x))
      (∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) (1 + x)) := by
    apply hasProd_prod
    intro t _
    exact spectralGlobalLSeries_hasProd (norm_primitiveSymmetricSpectralRoots_le f hbound (2 * t)) h0
  have hA := principal_incomplete_euler_hasProd Q h0
  have hU : HasProd (fun p : Nat.Primes =>
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p (1 + x + Complex.I * y))
      (primitiveSymmetricLFunction f r (1 + x + Complex.I * y)) :=
    spectralGlobalLSeries_hasProd (norm_primitiveSymmetricSpectralRoots_le f hbound r) h1
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
  simpa only [principalPrimeEulerFactor, Complex.ofReal_add, Complex.ofReal_one] using
    primitive_higher_mixed_local f hbound r p (by linarith : 1 < 1 + x) y

end
end Dubon2026
