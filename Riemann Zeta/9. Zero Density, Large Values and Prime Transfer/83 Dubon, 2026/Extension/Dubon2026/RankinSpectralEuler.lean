import Dubon2026.RankinSpectralTraces
import Dubon2026.EulerBoundaryNonvanishing

/-! # The actual Rankin convolution as a genuine spectral Euler product -/

namespace Dubon2026

noncomputable section

/-- The true good-prime Rankin tensor factor is exactly the symmetric-square factor times the principal factor. -/
theorem primitiveRankinSpectralEulerFactor_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q) (s : ℂ) :
    primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s =
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s *
        (1 - (((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  have he : primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 2) p s =
      ((1 - primitiveSatakeMinus f p ^ 2 * (((p : ℕ) : ℂ) ^ (-s))) *
        (1 - (((p : ℕ) : ℂ) ^ (-s))) *
          (1 - primitiveSatakePlus f p ^ 2 * (((p : ℕ) : ℂ) ^ (-s))))⁻¹ := by
    unfold primeSpectralEulerFactor
    rw [Fin.prod_univ_three]
    norm_num [primitiveSymmetricSpectralRoots, hpQ, (primitiveSatake_trace_det f p).2]
  rw [he, primeSpectralEulerFactor, primitiveRankinSpectralRoots, if_neg hpQ,
    Fin.prod_univ_four]
  change ((1 - primitiveSatakePlus f p ^ 2 * (((p : ℕ) : ℂ) ^ (-s))) *
      (1 - 1 * (((p : ℕ) : ℂ) ^ (-s))) * (1 - 1 * (((p : ℕ) : ℂ) ^ (-s))) *
        (1 - primitiveSatakeMinus f p ^ 2 * (((p : ℕ) : ℂ) ^ (-s))))⁻¹ = _
  simp only [one_mul, ← mul_inv]
  congr 1
  ring

/-- The true ramified Rankin tensor factor retains exactly the actual square-coefficient linear denominator. -/
theorem primitiveRankinSpectralEulerFactor_bad {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : (p : ℕ) ∣ Q) (s : ℂ) :
    primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s =
      (1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  simp [primeSpectralEulerFactor, primitiveRankinSpectralRoots, hpQ, Fin.prod_univ_four]

/-- The genuine spectral local product agrees exactly with the original Rankin square factor times its principal factor at 2s. -/
theorem primitiveRankinSpectralEulerFactor_eq_square {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s =
      (∑' r : ℕ, primitiveSquareLocalTerm f p s r) *
        (if (p : ℕ) ∣ Q then 1 else (1 - (((p : ℕ) : ℂ) ^ (-(2 * s))))⁻¹) := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rw [primitiveRankinSpectralEulerFactor_bad f p hpQ,
      primitive_bad_square_euler_series f hk p.property hpQ hs, if_pos hpQ, mul_one]
  · rw [primitiveRankinSpectralEulerFactor_good f p hpQ, if_neg hpQ]
    exact primitive_second_rankin_local_identity f hk p hpQ hs

/-- The original globally continued Rankin convolution is the actual product of its genuine tensor roots on Re(s)>1. -/
theorem primitive_rankin_spectral_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s)
      (rankinConvolutionGlobalContinuation f.toCuspForm s) := by
  have hs2 : 1 < (2 * s).re := by norm_num [Complex.mul_re]; linarith
  have hh := (primitive_square_lseries_euler_hasProd f hk hs).mul
    (principal_incomplete_euler_hasProd Q hs2)
  rw [rankinConvolutionGlobalContinuation_eq_series f.toCuspForm hk hs,
    rankinConvolution_LSeries f.toCuspForm hk hs, mul_comm]
  convert hh using 1
  funext p
  exact primitiveRankinSpectralEulerFactor_eq_square f hk p hs

end
end Dubon2026
