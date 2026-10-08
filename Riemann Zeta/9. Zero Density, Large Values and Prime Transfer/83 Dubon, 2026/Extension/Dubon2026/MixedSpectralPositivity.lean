import Dubon2026.FiniteSpectralPositivity

/-! # Mixed Rankin and first-power Euler positivity -/

namespace Dubon2026

noncomputable section

/-- The actual finite spectral logarithm on a rotated ray has its genuine real power traces as coefficients. -/
theorem finiteSpectralLog_rotated_hasSum {d : ℕ} (w : Fin d → ℂ) {a : ℝ}
    (hw : ∀ i, ‖w i * (a : ℂ)‖ < 1)
    (hreal : ∀ r : ℕ, (∑ i : Fin d, w i ^ r).im = 0)
    {z : ℂ} (hz : ‖z‖ = 1) :
    HasSum (fun r : ℕ => (((∑ i : Fin d, w i ^ r).re * a ^ r / r : ℝ) : ℂ) * z ^ r)
      (finiteSpectralLog w ((a : ℂ) * z)) := by
  have hh := finiteSpectralLog_hasSum w (fun i => by
    rw [norm_spectral_unit_rotation hz]
    exact hw i)
  convert hh using 1
  funext r
  have hr : (∑ i : Fin d, w i ^ r) = ((∑ i : Fin d, w i ^ r).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hreal r)
  rw [hr, mul_pow]
  simp only [Complex.ofReal_re]
  push_cast
  ring

/-- The mixed Rankin trigonometric polynomial is the nonnegative square c*(t+2*cos(theta))^2. -/
theorem real_weighted_mixed_rankin {c : ℝ} (hc : 0 ≤ c) (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ c * t ^ 2 + 2 * c + 4 * (((c * t : ℝ) : ℂ) * z).re +
      2 * ((c : ℂ) * z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      _ = ‖z‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by rw [hz, one_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, pow_two]
  nlinarith [mul_nonneg hc (sq_nonneg (t + 2 * z.re))]

end
end Dubon2026
