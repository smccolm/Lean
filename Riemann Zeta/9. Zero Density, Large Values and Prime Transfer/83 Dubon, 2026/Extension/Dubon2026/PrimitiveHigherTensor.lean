import Dubon2026.SatakeTensorDecomposition
import Dubon2026.PrimitiveHigherEulerConvergence
import Dubon2026.SpectralDirichletCoefficients

/-! # Actual tensor squares of all symmetric Hecke systems -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- The literal roots of the tensor square of the r-th symmetric Hecke system. -/
def primitiveHigherTensorRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes)
    (i : Fin (r + 1) × Fin (r + 1)) : ℂ :=
  primitiveSymmetricSpectralRoots f r p i.1 * primitiveSymmetricSpectralRoots f r p i.2

/-- Every power trace of the actual symmetric Hecke system is real. -/
theorem primitiveSymmetricSpectral_power_trace_real {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (m : ℕ) :
    (∑ i : Fin (r + 1), primitiveSymmetricSpectralRoots f r p i ^ m).im = 0 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · cases m <;> simp [primitiveSymmetricSpectralRoots, hpQ]
  · simp only [primitiveSymmetricSpectralRoots, if_neg hpQ]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) ^ m),
      satakeSymmetricTrace_power_sum]
    have hp : primitiveSatakePlus f p ^ m * primitiveSatakeMinus f p ^ m = 1 := by
      rw [← mul_pow, (primitiveSatake_trace_det f p).2, one_pow]
    apply satakeSymmetricTrace_im_zero hp
    apply satake_power_sum_im_zero (primitiveSatake_trace_det f p).2
    rw [(primitiveSatake_trace_det f p).1]
    exact primitiveCuspForm_normalizedCoefficient_im f p (p.property.coprime_iff_not_dvd.mpr hpQ)

/-- The actual tensor power trace is precisely the square of the actual symmetric power trace. -/
theorem primitiveHigherTensor_trace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (m : ℕ) :
    (∑ i : Fin (r + 1) × Fin (r + 1), primitiveHigherTensorRoots f r p i ^ m) =
      (∑ i : Fin (r + 1), primitiveSymmetricSpectralRoots f r p i ^ m) ^ 2 := by
  simp only [primitiveHigherTensorRoots, Fintype.sum_prod_type, mul_pow,
    ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- All actual higher tensor power traces are nonnegative real without any local purity premise. -/
theorem primitiveHigherTensor_trace_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (m : ℕ) :
    0 ≤ ∑ i : Fin (r + 1) × Fin (r + 1), primitiveHigherTensorRoots f r p i ^ m := by
  rw [primitiveHigherTensor_trace, Complex.sq_nonneg_iff]
  exact primitiveSymmetricSpectral_power_trace_real f r p m

/-- The proved coarse prime bound for each genuine higher tensor root. -/
theorem primitiveHigherTensor_norm_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) (p : Nat.Primes)
    (i : Fin (r + 1) × Fin (r + 1)) :
    ‖primitiveHigherTensorRoots f r p i‖ ≤ ((p : ℕ) : ℝ) ^ (2 * r) := by
  rw [primitiveHigherTensorRoots, norm_mul, two_mul, pow_add]
  exact mul_le_mul (primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i.1)
    (primitiveSymmetricSpectralRoots_norm_le_prime_pow f hk r p i.2) (norm_nonneg _) (by positivity)

/-- The genuine global higher tensor coefficients use their literal formal Euler factors. -/
def primitiveHigherTensorCoefficient {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) : ℕ → ℂ :=
  spectralDirichletCoefficient (primitiveHigherTensorRoots f r)

/-- All true global higher tensor coefficients are nonnegative real. -/
theorem primitiveHigherTensorCoefficient_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (n : ℕ) : 0 ≤ primitiveHigherTensorCoefficient f r n :=
  spectralDirichletCoefficient_nonneg _ (fun p m _ => primitiveHigherTensor_trace_nonneg f r p m) n

/-- A concrete finite abscissa for every actual higher tensor Dirichlet series. -/
theorem primitiveHigherTensorCoefficient_abscissa_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) :
    LSeries.abscissaOfAbsConv (primitiveHigherTensorCoefficient f r) ≤
      ((2 * r + (r + 1) ^ 2 + 1 : ℕ) : ℝ) + 1 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, ← pow_two] using
    spectralDirichletCoefficient_abscissa_le _ (2 * r) (primitiveHigherTensor_norm_le f hk r)

/-- Exact Clebsch–Gordan factorization of the actual tensor Euler factor at every prime,
including the omitted ramified factors and repeated good roots. -/
theorem primitiveHigherTensor_euler_factor {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (s : ℂ) :
    (∏ i : Fin (r + 1) × Fin (r + 1),
      (1 - primitiveHigherTensorRoots f r p i * (((p : ℕ) : ℂ) ^ (-s)))⁻¹) =
    ∏ t ∈ Finset.range (r + 1), primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p s := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp [primitiveHigherTensorRoots, primitiveSymmetricSpectralRoots, hpQ,
      primitiveSymmetricSpectralEulerFactor_bad f _ p hpQ]
  · simp only [primitiveHigherTensorRoots, primitiveSymmetricSpectralRoots, if_neg hpQ,
      Fintype.prod_prod_type, primeSpectralEulerFactor, Finset.prod_inv_distrib]
    congr 1
    have hfin (n : ℕ) (u : ℕ → ℂ) : (∏ i : Fin n, u i) = ∏ i ∈ Finset.range n, u i :=
      Fin.prod_univ_eq_prod_range u n
    rw [hfin (r + 1) (fun i => ∏ j : Fin (r + 1),
      (1 - (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) *
        (primitiveSatakePlus f p ^ (j : ℕ) * primitiveSatakeMinus f p ^ (r - (j : ℕ))) *
        (((p : ℕ) : ℂ) ^ (-s))))]
    have hinner (i : ℕ) :
        (∏ j : Fin (r + 1), (1 -
          (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) *
          (primitiveSatakePlus f p ^ (j : ℕ) * primitiveSatakeMinus f p ^ (r - (j : ℕ))) *
          (((p : ℕ) : ℂ) ^ (-s)))) =
        ∏ j ∈ Finset.range (r + 1), (1 -
          (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) *
          (primitiveSatakePlus f p ^ j * primitiveSatakeMinus f p ^ (r - j)) *
          (((p : ℕ) : ℂ) ^ (-s))) :=
      hfin (r + 1) (fun j => 1 -
        (primitiveSatakePlus f p ^ i * primitiveSatakeMinus f p ^ (r - i)) *
        (primitiveSatakePlus f p ^ j * primitiveSatakeMinus f p ^ (r - j)) *
        (((p : ℕ) : ℂ) ^ (-s)))
    have heven (t : ℕ) :
        (∏ i : Fin (2 * t + 1), (1 - primitiveSatakePlus f p ^ (i : ℕ) *
          primitiveSatakeMinus f p ^ (2 * t - (i : ℕ)) * (((p : ℕ) : ℂ) ^ (-s)))) =
        ∏ i ∈ Finset.range (2 * t + 1), (1 - primitiveSatakePlus f p ^ i *
          primitiveSatakeMinus f p ^ (2 * t - i) * (((p : ℕ) : ℂ) ^ (-s))) :=
      hfin (2 * t + 1) (fun i => 1 - primitiveSatakePlus f p ^ i *
        primitiveSatakeMinus f p ^ (2 * t - i) * (((p : ℕ) : ℂ) ^ (-s)))
    simp_rw [hinner, heven]
    exact satake_tensor_product_decomposition (primitiveSatake_trace_det f p).2
      (fun w => 1 - w * (((p : ℕ) : ℂ) ^ (-s))) r

end
end Dubon2026
