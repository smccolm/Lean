import Dubon2026.PrimitiveAugmentedCoefficients
import Dubon2026.PrimitiveMixedEulerGlobal

/-! # Exact local and global Euler identities for the genuine augmented Rankin coefficients -/

namespace Dubon2026

noncomputable section

/-- Exact factorization of the nine augmented tensor Euler denominators. -/
theorem augmented_tensor_euler_factor {α β : ℂ} (hp : α * β = 1) (z : ℂ) :
    (∏ i : Fin 3 × Fin 3, (1 - (![1, α, β] i.1 * ![1, α, β] i.2) * z)⁻¹) =
      (1 - z)⁻¹ * ((1 - α ^ 2 * z) * (1 - z) * (1 - z) * (1 - β ^ 2 * z))⁻¹ *
        (((1 - α * z) * (1 - β * z))⁻¹) ^ 2 := by
  have hp' : β * α = 1 := by rw [mul_comm, hp]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_three]
  change ((1 - (1 * 1 : ℂ) * z)⁻¹ * (1 - (1 * α) * z)⁻¹ * (1 - (1 * β) * z)⁻¹) *
      ((1 - (α * 1) * z)⁻¹ * (1 - (α * α) * z)⁻¹ * (1 - (α * β) * z)⁻¹) *
      ((1 - (β * 1) * z)⁻¹ * (1 - (β * α) * z)⁻¹ * (1 - (β * β) * z)⁻¹) = _
  simp only [one_mul, mul_one, hp, hp', ← pow_two, inv_pow, ← mul_inv]
  congr 1
  ring

/-- The genuine augmented local Euler product equals the actual principal, Rankin and
first symmetric factors, with precisely the finite ramified removal. -/
theorem primitiveAugmentedTensor_euler_factor {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (∏ i : Fin 3 × Fin 3, (1 - primitiveAugmentedTensorRoots f p i * (((p : ℕ) : ℂ) ^ (-s)))⁻¹) =
      principalPrimeEulerFactor Q p s *
        primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s *
        (if (p : ℕ) ∣ Q then
          1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) else 1) *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p s ^ 2 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rw [principalPrimeEulerFactor, if_pos hpQ,
      primitiveRankinSpectralEulerFactor_bad f p hpQ,
      primitiveSymmetricSpectralEulerFactor_bad f 1 p hpQ, if_pos hpQ,
      one_mul, inv_mul_cancel₀ (primitive_bad_square_denominator_ne_zero f hk p.property hpQ hs)]
    simp [primitiveAugmentedTensorRoots, primitiveAugmentedRoots, hpQ]
  · have he := augmented_tensor_euler_factor (primitiveSatake_trace_det f p).2
      (((p : ℕ) : ℂ) ^ (-s))
    have hfirst : primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p s =
        ((1 - primitiveSatakePlus f p * (((p : ℕ) : ℂ) ^ (-s))) *
          (1 - primitiveSatakeMinus f p * (((p : ℕ) : ℂ) ^ (-s))))⁻¹ := by
      simp [primeSpectralEulerFactor, primitiveSymmetricSpectralRoots, hpQ, Fin.prod_univ_two, mul_comm]
    rw [hfirst, principalPrimeEulerFactor, if_neg hpQ, if_neg hpQ, mul_one,
      primeSpectralEulerFactor, primitiveRankinSpectralRoots, if_neg hpQ, Fin.prod_univ_four]
    simpa [primitiveAugmentedTensorRoots, primitiveAugmentedRoots, hpQ] using he

/-- The actual augmented tensor coordinates are strictly inside the geometric convergence disk on Re(s)>2. -/
theorem norm_primitiveAugmentedTensor_coordinate_lt_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 3 × Fin 3)
    {s : ℂ} (hs : 2 < s.re) :
    ‖primitiveAugmentedTensorRoots f p i * (((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (primitiveAugmentedTensor_norm_le_prime_sq f hk p i) (by positivity)
    _ = ((p : ℕ) : ℝ) ^ (2 - s.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
      congr 1
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)

/-- The true augmented local coefficient series evaluates to its exact principal/Rankin/first-power Euler factor. -/
theorem primitiveAugmentedLocalCoeff_tsum {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) {s : ℂ} (hs : 2 < s.re) :
    (∑' r : ℕ, primitiveAugmentedLocalCoeff f p r * ((((p : ℕ) : ℂ) ^ (-s)) ^ r)) =
      principalPrimeEulerFactor Q p s *
        primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p s *
        (if (p : ℕ) ∣ Q then
          1 - ((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) else 1) *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p s ^ 2 := by
  have he := (spectralFormalEuler_evaluation Finset.univ (primitiveAugmentedTensorRoots f p)
    (((p : ℕ) : ℂ) ^ (-s)) (fun i _ => norm_primitiveAugmentedTensor_coordinate_lt_one f hk p i hs)).2.tsum_eq
  exact he.trans (primitiveAugmentedTensor_euler_factor f (by omega) p (by linarith))

/-- The literal nonnegative coefficient L-series is exactly the genuine mixed Euler product. -/
theorem primitiveAugmentedCoefficient_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 7 < s.re) :
    LSeries (primitiveAugmentedCoefficient f) s =
      DirichletCharacter.LFunctionTrivChar Q s * rankinConvolutionGlobalContinuation f.toCuspForm s *
        primitiveRankinBadCorrection f s * primitiveSymmetricLFunction f 1 s ^ 2 := by
  have hs1 : 1 < s.re := by linarith
  have hh := (((principal_incomplete_euler_hasProd Q hs1).mul
    (primitive_rankin_spectral_hasProd f (by omega) hs1)).mul
    (primitive_rankin_bad_correction_hasProd f s)).mul
    ((primitive_first_symmetric_hasProd f (by omega) hs1).pow 2)
  apply (primitiveAugmentedCoefficient_hasProd f hk hs).unique
  convert hh using 1
  funext p
  rw [primitiveAugmentedLocalCoeff_tsum f hk p (by linarith),
    primitive_first_symmetric_local_factor, principalPrimeEulerFactor]

end
end Dubon2026
