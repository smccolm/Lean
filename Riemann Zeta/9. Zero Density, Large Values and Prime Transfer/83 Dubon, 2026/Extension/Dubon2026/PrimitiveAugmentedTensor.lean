import Dubon2026.PrimitiveMixedEulerLocal
import Dubon2026.SpectralFormalEvaluation

/-! # Genuine tensor roots of the unramified augmented Hecke system -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- The roots of the actual unramified augmentation `1 ⊕ f`, with omitted ramified factors. -/
def primitiveAugmentedRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) : Fin 3 → ℂ :=
  if (p : ℕ) ∣ Q then 0 else ![1, primitiveSatakePlus f p, primitiveSatakeMinus f p]

/-- The actual nine tensor roots of `(1 ⊕ f) ⊗ (1 ⊕ f)`, with ramified factors omitted. -/
def primitiveAugmentedTensorRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (i : Fin 3 × Fin 3) : ℂ :=
  primitiveAugmentedRoots f p i.1 * primitiveAugmentedRoots f p i.2

/-- A genuine tensor power trace is the square of the genuine augmented power trace. -/
theorem primitiveAugmentedTensor_trace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) :
    ∑ i : Fin 3 × Fin 3, primitiveAugmentedTensorRoots f p i ^ r =
      (∑ i : Fin 3, primitiveAugmentedRoots f p i ^ r) ^ 2 := by
  simp only [primitiveAugmentedTensorRoots, Fintype.sum_prod_type, mul_pow,
    ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- All positive-order actual augmented tensor power traces are real and nonnegative,
without assuming Deligne. -/
theorem primitiveAugmentedTensor_trace_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) (hr : 0 < r) :
    0 ≤ ∑ i : Fin 3 × Fin 3, primitiveAugmentedTensorRoots f p i ^ r := by
  rw [primitiveAugmentedTensor_trace, Complex.sq_nonneg_iff]
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp [primitiveAugmentedRoots, hpQ, ne_of_gt hr]
  · have hreal : (primitiveSatakePlus f p + primitiveSatakeMinus f p).im = 0 := by
      rw [(primitiveSatake_trace_det f p).1]
      exact primitiveCuspForm_normalizedCoefficient_im f p (p.property.coprime_iff_not_dvd.mpr hpQ)
    have hh := satake_power_sum_im_zero (primitiveSatake_trace_det f p).2 hreal r
    simpa [primitiveAugmentedRoots, hpQ, Fin.sum_univ_three, add_assoc] using hh

/-- A coarse prime bound for every actual augmented root follows from the proved Rankin remainder. -/
theorem primitiveAugmentedRoots_norm_le_prime {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 3) :
    ‖primitiveAugmentedRoots f p i‖ ≤ (p : ℕ) := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp [primitiveAugmentedRoots, hpQ]
  · have hp1 : 1 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.one_le
    have hA : ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) ≤ (p : ℕ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (3 / 5 : ℝ) ≤ 1)
    obtain ⟨ha, hb⟩ := primitiveSatake_norm_sq_le_three_fifths f hk p.property hpQ
    have ha' : ‖primitiveSatakePlus f p‖ ≤ ((p : ℕ) : ℝ) := by
      nlinarith [sq_nonneg (‖primitiveSatakePlus f p‖ - 1)]
    have hb' : ‖primitiveSatakeMinus f p‖ ≤ ((p : ℕ) : ℝ) := by
      nlinarith [sq_nonneg (‖primitiveSatakeMinus f p‖ - 1)]
    rw [primitiveAugmentedRoots, if_neg hpQ]
    fin_cases i
    · simpa using hp1
    · exact ha'
    · exact hb'

/-- Every genuine augmented tensor root has the elementary bound p². -/
theorem primitiveAugmentedTensor_norm_le_prime_sq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 3 × Fin 3) :
    ‖primitiveAugmentedTensorRoots f p i‖ ≤ ((p : ℕ) : ℝ) ^ 2 := by
  rw [primitiveAugmentedTensorRoots, norm_mul, pow_two]
  exact mul_le_mul (primitiveAugmentedRoots_norm_le_prime f hk p i.1)
    (primitiveAugmentedRoots_norm_le_prime f hk p i.2) (norm_nonneg _) (Nat.cast_nonneg _)

/-- The literal local Euler coefficients of the genuine augmented tensor system. -/
def primitiveAugmentedLocalCoeff {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) : ℂ :=
  PowerSeries.coeff r (spectralFormalEuler Finset.univ (primitiveAugmentedTensorRoots f p))

/-- The genuine local constant coefficient is one. -/
theorem primitiveAugmentedLocalCoeff_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) : primitiveAugmentedLocalCoeff f p 0 = 1 :=
  coeff_zero_spectralFormalEuler _ _

/-- Every actual augmented tensor Euler coefficient is nonnegative real. -/
theorem primitiveAugmentedLocalCoeff_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) : 0 ≤ primitiveAugmentedLocalCoeff f p r :=
  spectralFormalEuler_coeff_nonneg _ _ (primitiveAugmentedTensor_trace_nonneg f p) r

end
end Dubon2026
