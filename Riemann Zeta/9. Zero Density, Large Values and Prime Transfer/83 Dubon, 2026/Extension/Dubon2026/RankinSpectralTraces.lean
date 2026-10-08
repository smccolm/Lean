import Dubon2026.RankinSatakeBounds
import Dubon2026.PrimitiveSecondValueOne

/-! # Nonnegative power traces of the genuine Rankin local roots -/

namespace Dubon2026

noncomputable section

/-- The powers of two determinant-one roots satisfy the true second-order Newton recurrence. -/
theorem satake_power_sum_recurrence {α β : ℂ} (hp : α * β = 1) (r : ℕ) :
    α ^ (r + 2) + β ^ (r + 2) =
      (α + β) * (α ^ (r + 1) + β ^ (r + 1)) - (α ^ r + β ^ r) := by
  calc
    _ = (α + β) * (α ^ (r + 1) + β ^ (r + 1)) - α * β * (α ^ r + β ^ r) := by
      simp only [pow_add, pow_one, pow_two]
      ring
    _ = _ := by rw [hp, one_mul]

/-- Real determinant-one trace makes every genuine root power sum real, without unit-modulus assumptions. -/
theorem satake_power_sum_im_zero {α β : ℂ} (hp : α * β = 1)
    (hr : (α + β).im = 0) (r : ℕ) : (α ^ r + β ^ r).im = 0 := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simpa only [pow_one] using hr
  | more r ih0 ih1 =>
    rw [satake_power_sum_recurrence hp, Complex.sub_im, Complex.mul_im, hr, ih0, ih1]
    ring

/-- The four true Rankin tensor roots at a good prime, and the actual linear square root at a ramified prime. -/
def primitiveRankinSpectralRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) : Fin 4 → ℂ :=
  if (p : ℕ) ∣ Q then ![((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ), 0, 0, 0]
  else ![primitiveSatakePlus f p ^ 2, 1, 1, primitiveSatakeMinus f p ^ 2]

/-- At a good prime the actual Rankin power trace is exactly the square of the real Hecke root power sum. -/
theorem primitiveRankinSpectral_trace_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q) (r : ℕ) :
    ∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r =
      (primitiveSatakePlus f p ^ r + primitiveSatakeMinus f p ^ r) ^ 2 := by
  have hp : primitiveSatakePlus f p ^ r * primitiveSatakeMinus f p ^ r = 1 := by
    rw [← mul_pow, (primitiveSatake_trace_det f p).2, one_pow]
  simp only [primitiveRankinSpectralRoots, if_neg hpQ, Fin.sum_univ_four]
  change (primitiveSatakePlus f p ^ 2) ^ r + (1 : ℂ) ^ r + (1 : ℂ) ^ r +
    (primitiveSatakeMinus f p ^ 2) ^ r = _
  simp only [one_pow]
  have he (z : ℂ) : (z ^ 2) ^ r = (z ^ r) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 r]
  rw [he, he]
  linear_combination -2 * hp

/-- Every power trace of the actual Rankin local roots is real and nonnegative. -/
theorem primitiveRankinSpectral_trace_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (r : ℕ) :
    (∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r).im = 0 ∧
      0 ≤ (∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r).re := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rcases r with _ | r
    · simp
    · simp [primitiveRankinSpectralRoots, hpQ, Fin.sum_univ_four, ← Complex.ofReal_pow]
  · rw [primitiveRankinSpectral_trace_good f p hpQ]
    have hreal : (primitiveSatakePlus f p + primitiveSatakeMinus f p).im = 0 := by
      rw [(primitiveSatake_trace_det f p).1]
      exact primitiveCuspForm_normalizedCoefficient_im f p (p.property.coprime_iff_not_dvd.mpr hpQ)
    have hr := satake_power_sum_im_zero (primitiveSatake_trace_det f p).2 hreal r
    constructor
    · simp [pow_two, Complex.mul_im, hr]
    · simp only [pow_two, Complex.mul_re, hr, zero_mul, sub_zero]
      exact mul_self_nonneg _

/-- Every actual Rankin local root has norm at most p^(3/5), by the proved coefficient remainder at both good and bad primes. -/
theorem primitiveRankinSpectral_norm_le_three_fifths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 4) :
    ‖primitiveRankinSpectralRoots f p i‖ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · rw [primitiveRankinSpectralRoots, if_pos hpQ]
    fin_cases i
    · change ‖((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact primitive_bad_coefficient_norm_sq_le_three_fifths f hk p.property hpQ
    all_goals change ‖(0 : ℂ)‖ ≤ _; rw [norm_zero]; positivity
  · obtain ⟨ha, hb⟩ := primitiveSatake_norm_sq_le_three_fifths f hk p.property hpQ
    rw [primitiveRankinSpectralRoots, if_neg hpQ]
    fin_cases i
    · change ‖primitiveSatakePlus f p ^ 2‖ ≤ _
      rwa [norm_pow]
    · change ‖(1 : ℂ)‖ ≤ _
      rw [norm_one]
      exact Real.one_le_rpow (by exact_mod_cast p.property.one_lt.le) (by norm_num)
    · change ‖(1 : ℂ)‖ ≤ _
      rw [norm_one]
      exact Real.one_le_rpow (by exact_mod_cast p.property.one_lt.le) (by norm_num)
    · change ‖primitiveSatakeMinus f p ^ 2‖ ≤ _
      rwa [norm_pow]

end
end Dubon2026
