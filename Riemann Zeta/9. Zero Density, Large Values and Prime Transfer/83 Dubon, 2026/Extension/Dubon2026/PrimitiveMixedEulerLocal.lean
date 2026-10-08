import Dubon2026.MixedSpectralEulerInequality
import Dubon2026.PrimitiveFirstContinuation
import Dubon2026.RankinEulerPositivity

/-! # The mixed Euler inequality for the actual first and Rankin roots -/

namespace Dubon2026

noncomputable section

/-- Both actual first-order roots obey the coarse three-fifths norm bound implied by their stronger square bound. -/
theorem primitive_first_spectral_norm_le_three_fifths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 2) :
    ‖primitiveSymmetricSpectralRoots f 1 p i‖ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
  have hA : 1 ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast p.property.one_lt.le) (by norm_num)
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos hpQ, norm_zero]
    positivity
  · obtain ⟨ha, hb⟩ := primitiveSatake_norm_sq_le_three_fifths f hk p.property hpQ
    have ha' : ‖primitiveSatakePlus f p‖ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
      nlinarith [sq_nonneg (‖primitiveSatakePlus f p‖ - 1)]
    have hb' : ‖primitiveSatakeMinus f p‖ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
      nlinarith [sq_nonneg (‖primitiveSatakeMinus f p‖ - 1)]
    fin_cases i
    · simpa [primitiveSymmetricSpectralRoots, hpQ] using hb'
    · simpa [primitiveSymmetricSpectralRoots, hpQ] using ha'

/-- Every actual first symmetric Euler coordinate is strictly inside the unit disk on Re(s)>3/5. -/
theorem norm_primitive_first_coordinate_lt_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 2)
    {s : ℂ} (hs : 3 / 5 < s.re) :
    ‖primitiveSymmetricSpectralRoots f 1 p i * (((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ (3 / 5 : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (primitive_first_spectral_norm_le_three_fifths f hk p i)
        (Real.rpow_nonneg hp0.le _)
    _ = ((p : ℕ) : ℝ) ^ (3 / 5 - s.re) := by rw [← Real.rpow_add hp0, sub_eq_add_neg]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)

/-- The doubled vertical prime coordinate uses precisely the square of the original unit phase. -/
theorem prime_cpow_vertical_twice (p : Nat.Primes) (σ y : ℝ) :
    (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * Complex.I * y))) =
      ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-(Complex.I * y))) ^ 2 := by
  have he := prime_cpow_vertical_split p σ (2 * y)
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at he
  rw [show Complex.I * (2 * (y : ℂ)) = 2 * Complex.I * y by ring] at he
  rw [he]
  congr 1
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

/-- At every genuine good prime, the original Rankin factor, two principal factors and first symmetric factors satisfy the exact mixed norm inequality. -/
theorem primitive_good_mixed_euler_inequality {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    1 ≤ ‖primeSpectralEulerFactor (primitiveRankinSpectralRoots f) p σ *
      ((1 - (((p : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹) ^ 2 *
        primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f 1) p ((σ : ℂ) + Complex.I * y) ^ 4 *
          ((1 - (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * Complex.I * y))))⁻¹) ^ 2‖ := by
  let a : ℝ := ((p : ℕ) : ℝ) ^ (-σ)
  have ha : (a : ℂ) = (((p : ℕ) : ℂ) ^ (-(σ : ℂ))) := by
    dsimp only [a]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.property.one_lt) (by linarith)
  have hreal : ∀ r : ℕ, (∑ i : Fin 2, primitiveSymmetricSpectralRoots f 1 p i ^ r).im = 0 := by
    intro r
    rw [primitive_first_spectral_power_trace_good f p hpQ]
    apply satake_power_sum_im_zero (primitiveSatake_trace_det f p).2
    rw [(primitiveSatake_trace_det f p).1]
    exact primitiveCuspForm_normalizedCoefficient_im f p (p.property.coprime_iff_not_dvd.mpr hpQ)
  have htrace : ∀ r : ℕ, ∑ i : Fin 4, primitiveRankinSpectralRoots f p i ^ r =
      (∑ i : Fin 2, primitiveSymmetricSpectralRoots f 1 p i ^ r) ^ 2 := by
    intro r
    rw [primitiveRankinSpectral_trace_good f p hpQ, primitive_first_spectral_power_trace_good f p hpQ]
  have hs' : 3 / 5 < (σ : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hU : ∀ i : Fin 2, ‖primitiveSymmetricSpectralRoots f 1 p i * (a : ℂ)‖ < 1 := by
    intro i
    rw [ha]
    exact norm_primitive_first_coordinate_lt_one f hk p i hs'
  have hV : ∀ i : Fin 4, ‖primitiveRankinSpectralRoots f p i * (a : ℂ)‖ < 1 := by
    intro i
    rw [ha]
    exact norm_primitiveRankinSpectral_coordinate_lt_one f hk p i hs'
  have hh := finiteSpectralEuler_mixed_rankin (primitiveSymmetricSpectralRoots f 1 p)
    (primitiveRankinSpectralRoots f p) (a := a) (by dsimp [a]; positivity) ha1
    hU hV hreal htrace (norm_prime_cpow_imaginary p y)
  simpa only [primeSpectralEulerFactor, ← ha, prime_cpow_vertical_split p σ y,
    prime_cpow_vertical_twice p σ y] using hh

end
end Dubon2026
