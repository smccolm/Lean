import Dubon2026.MixedSpectralPositivity

/-! # The mixed first-power and Rankin logarithmic inequality -/

namespace Dubon2026

noncomputable section

/-- A true tensor-square power trace gives the mixed Rankin logarithmic inequality, including the two principal factors. -/
theorem finiteSpectralLog_mixed_rankin {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hu : ∀ i, ‖u i * (a : ℂ)‖ < 1) (hv : ∀ i, ‖v i * (a : ℂ)‖ < 1)
    (hreal : ∀ r : ℕ, (∑ i : Fin d, u i ^ r).im = 0)
    (htrace : ∀ r : ℕ, ∑ i : Fin e, v i ^ r = (∑ i : Fin d, u i ^ r) ^ 2)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (finiteSpectralLog v a).re + 2 * (finiteSpectralLog (fun _ : Fin 1 => 1) a).re +
      4 * (finiteSpectralLog u ((a : ℂ) * z)).re +
        2 * (finiteSpectralLog (fun _ : Fin 1 => 1) ((a : ℂ) * z ^ 2)).re := by
  have hvr : ∀ r : ℕ, (∑ i : Fin e, v i ^ r).im = 0 := by
    intro r
    rw [htrace, pow_two, Complex.mul_im, hreal]
    ring
  have hvc : ∀ r : ℕ, (∑ i : Fin e, v i ^ r).re = (∑ i : Fin d, u i ^ r).re ^ 2 := by
    intro r
    rw [htrace, pow_two, Complex.mul_re, hreal]
    ring
  have hunit : ∀ _i : Fin 1, ‖(1 : ℂ) * a‖ < 1 := by
    intro i
    simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0] using ha1
  have hone : ∀ r : ℕ, (∑ _i : Fin 1, (1 : ℂ) ^ r).im = 0 := by intro r; simp
  have hR := finiteSpectralLog_rotated_hasSum v hv hvr (z := 1) (norm_one (α := ℂ))
  have hA := finiteSpectralLog_rotated_hasSum (fun _ : Fin 1 => 1) hunit hone
    (z := 1) (norm_one (α := ℂ))
  have hU := finiteSpectralLog_rotated_hasSum u hu hreal hz
  have hB := finiteSpectralLog_rotated_hasSum (fun _ : Fin 1 => 1) hunit hone
    (z := z ^ 2) (by rw [norm_pow, hz, one_pow])
  simp only [mul_one, one_pow] at hR hA
  have ht := (((Complex.hasSum_re hR).add ((Complex.hasSum_re hA).mul_left 2)).add
    ((Complex.hasSum_re hU).mul_left 4)).add ((Complex.hasSum_re hB).mul_left 2)
  rw [← ht.tsum_eq]
  apply tsum_nonneg
  intro r
  have hc : 0 ≤ a ^ r / (r : ℝ) := div_nonneg (pow_nonneg ha0 _) (Nat.cast_nonneg _)
  have hh := real_weighted_mixed_rankin hc (∑ i : Fin d, u i ^ r).re
    (z := z ^ r) (by rw [norm_pow, hz, one_pow])
  have hp : (z ^ 2) ^ r = (z ^ r) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 r]
  simp only [Complex.ofReal_re, hvc, one_pow, Fin.sum_univ_one, Complex.one_re, one_mul, hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh ⊢
  convert hh using 1
  ring

end
end Dubon2026
