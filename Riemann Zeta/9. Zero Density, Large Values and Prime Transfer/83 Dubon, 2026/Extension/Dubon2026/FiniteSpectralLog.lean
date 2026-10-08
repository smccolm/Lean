import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Actual finite spectral logarithms and the three-four-one positivity argument -/

namespace Dubon2026

noncomputable section

/-- The genuine sum of logarithms of finitely many linear Euler denominators. -/
def finiteSpectralLog {d : ℕ} (w : Fin d → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin d, -Complex.log (1 - w i * z)

/-- The true logarithmic power series has the exact spectral power traces as coefficients. -/
theorem finiteSpectralLog_hasSum {d : ℕ} (w : Fin d → ℂ) {z : ℂ}
    (hw : ∀ i, ‖w i * z‖ < 1) :
    HasSum (fun r : ℕ => (∑ i : Fin d, w i ^ r) * z ^ r / (r : ℂ))
      (finiteSpectralLog w z) := by
  have hh := hasSum_sum (s := Finset.univ)
    (fun i _ => Complex.hasSum_taylorSeries_neg_log (hw i))
  simpa only [finiteSpectralLog, mul_pow, Finset.sum_div, Finset.sum_mul] using hh

/-- Exponentiating the actual finite logarithm gives exactly the reciprocal Euler denominator. -/
theorem exp_finiteSpectralLog {d : ℕ} (w : Fin d → ℂ) {z : ℂ}
    (hw : ∀ i, 1 - w i * z ≠ 0) :
    Complex.exp (finiteSpectralLog w z) = (∏ i : Fin d, (1 - w i * z))⁻¹ := by
  rw [finiteSpectralLog, Complex.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.exp_neg, Complex.exp_log (hw i)]

/-- The exact three-four-one trigonometric polynomial is nonnegative for every unit complex number and every nonnegative real weight. -/
theorem real_weighted_three_four_one {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * c + 4 * ((c : ℂ) * z).re + ((c : ℂ) * z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      _ = ‖z‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by rw [hz, one_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    pow_two]
  nlinarith [mul_nonneg hc (sq_nonneg (z.re + 1))]

end
end Dubon2026
