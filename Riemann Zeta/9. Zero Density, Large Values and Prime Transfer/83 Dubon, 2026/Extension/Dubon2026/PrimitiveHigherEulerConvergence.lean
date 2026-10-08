import Dubon2026.SpectralEulerShift
import Dubon2026.PrimitiveAugmentedTensor

/-! # Genuine far-half-plane convergence of every actual symmetric Euler power -/

namespace Dubon2026

noncomputable section

/-- All actual symmetric-power roots satisfy a proved polynomial prime bound, without Deligne. -/
theorem primitiveSymmetricSpectralRoots_norm_le_prime_pow {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) (p : Nat.Primes) (i : Fin (r + 1)) :
    ‖primitiveSymmetricSpectralRoots f r p i‖ ≤ ((p : ℕ) : ℝ) ^ r := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos hpQ, norm_zero]
    positivity
  · have ha : ‖primitiveSatakePlus f p‖ ≤ ((p : ℕ) : ℝ) := by
      simpa [primitiveAugmentedRoots, hpQ] using primitiveAugmentedRoots_norm_le_prime f hk p (1 : Fin 3)
    have hb : ‖primitiveSatakeMinus f p‖ ≤ ((p : ℕ) : ℝ) := by
      simpa [primitiveAugmentedRoots, hpQ] using primitiveAugmentedRoots_norm_le_prime f hk p (2 : Fin 3)
    rw [primitiveSymmetricSpectralRoots, if_neg hpQ, norm_mul, norm_pow, norm_pow]
    calc
      _ ≤ ((p : ℕ) : ℝ) ^ (i : ℕ) * ((p : ℕ) : ℝ) ^ (r - (i : ℕ)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
          (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (by omega : (i : ℕ) ≤ r)]

/-- Every original symmetric Euler product genuinely converges in a proved far half-plane. -/
theorem primitive_higher_symmetric_hasProd_far {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ} (hs : (r : ℝ) + 1 < s.re) :
    HasProd (fun p : Nat.Primes => primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p s)
      (primitiveSymmetricLFunction f r s) := by
  apply spectralGlobalLSeries_hasProd_of_prime_bound (A := (r : ℝ)) _ hs
  intro p i
  simpa only [Real.rpow_natCast] using primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i

/-- The actual higher symmetric Euler function cannot vanish in its proved far convergence half-plane. -/
theorem primitive_higher_symmetric_ne_zero_far {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ} (hs : (r : ℝ) + 1 < s.re) :
    primitiveSymmetricLFunction f r s ≠ 0 := by
  apply spectralGlobalLSeries_ne_zero_of_prime_bound (A := (r : ℝ)) _ hs
  intro p i
  simpa only [Real.rpow_natCast] using primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i

/-- Every actual symmetric Euler power is holomorphic on its proved far half-plane. -/
theorem primitive_higher_symmetric_differentiableOn_far {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) :
    DifferentiableOn ℂ (primitiveSymmetricLFunction f r) {s : ℂ | (r : ℝ) + 1 < s.re} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply spectralGlobalLSeries_differentiableAt_of_prime_bound (A := (r : ℝ)) _ hs
  intro p i
  simpa only [Real.rpow_natCast] using primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i

end
end Dubon2026
