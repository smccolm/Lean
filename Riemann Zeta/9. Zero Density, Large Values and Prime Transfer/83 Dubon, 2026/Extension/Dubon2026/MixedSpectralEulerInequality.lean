import Dubon2026.MixedSpectralLogInequality

/-! # The exact mixed Rankin Euler-factor inequality -/

namespace Dubon2026

noncomputable section

/-- Strict spectral-coordinate bounds give nonzero denominators after every unit rotation. -/
theorem finiteSpectral_denominator_ne_zero {d : ℕ} (w : Fin d → ℂ) {a : ℝ}
    (hw : ∀ i, ‖w i * (a : ℂ)‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) (i : Fin d) :
    1 - w i * ((a : ℂ) * z) ≠ 0 := by
  intro he
  have hn : ‖w i * ((a : ℂ) * z)‖ < 1 := by rw [norm_spectral_unit_rotation hz]; exact hw i
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact lt_irrefl _ hn

/-- The true tensor-square power traces give the mixed Rankin norm inequality for the literal reciprocal Euler products. -/
theorem finiteSpectralEuler_mixed_rankin {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hu : ∀ i, ‖u i * (a : ℂ)‖ < 1) (hv : ∀ i, ‖v i * (a : ℂ)‖ < 1)
    (hreal : ∀ r : ℕ, (∑ i : Fin d, u i ^ r).im = 0)
    (htrace : ∀ r : ℕ, ∑ i : Fin e, v i ^ r = (∑ i : Fin d, u i ^ r) ^ 2)
    {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(∏ i : Fin e, (1 - v i * (a : ℂ)))⁻¹ * ((1 - (a : ℂ))⁻¹) ^ 2 *
      ((∏ i : Fin d, (1 - u i * ((a : ℂ) * z)))⁻¹) ^ 4 *
        ((1 - (a : ℂ) * z ^ 2)⁻¹) ^ 2‖ := by
  have hunit : ∀ _i : Fin 1, ‖(1 : ℂ) * a‖ < 1 := by
    intro i
    simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0] using ha1
  have hvn : ∀ i : Fin e, 1 - v i * (a : ℂ) ≠ 0 := by
    simpa only [mul_one] using finiteSpectral_denominator_ne_zero v hv (norm_one (α := ℂ))
  have hp0 : Complex.exp (finiteSpectralLog (fun _ : Fin 1 => 1) a) = (1 - (a : ℂ))⁻¹ := by
    have hn : ∀ i : Fin 1, 1 - (1 : ℂ) * (a : ℂ) ≠ 0 := by
      simpa only [mul_one] using finiteSpectral_denominator_ne_zero (fun _ : Fin 1 => 1) hunit (norm_one (α := ℂ))
    simpa only [Fin.prod_univ_one, one_mul] using exp_finiteSpectralLog (fun _ : Fin 1 => 1) hn
  have hp2 : Complex.exp (finiteSpectralLog (fun _ : Fin 1 => 1) ((a : ℂ) * z ^ 2)) =
      (1 - (a : ℂ) * z ^ 2)⁻¹ := by
    simpa only [Fin.prod_univ_one, one_mul] using
      exp_finiteSpectralLog (fun _ : Fin 1 => 1)
        (finiteSpectral_denominator_ne_zero (fun _ : Fin 1 => 1) hunit (by rw [norm_pow, hz, one_pow]))
  rw [← exp_finiteSpectralLog v hvn, ← hp0,
    ← exp_finiteSpectralLog u (finiteSpectral_denominator_ne_zero u hu hz), ← hp2]
  simp only [← Complex.exp_nat_mul, Nat.cast_ofNat, ← Complex.exp_add, Complex.norm_exp,
    Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Real.one_le_exp_iff]
  exact finiteSpectralLog_mixed_rankin u v ha0 ha1 hu hv hreal htrace hz

end
end Dubon2026
