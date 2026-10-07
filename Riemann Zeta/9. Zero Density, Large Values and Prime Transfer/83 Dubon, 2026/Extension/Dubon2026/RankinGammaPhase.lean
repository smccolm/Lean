import Dubon2026.GammaPhaseCurvature

/-! # The genuine two-Gamma Rankin phase on the central line -/

namespace Dubon2026

open Complex

noncomputable section

/-- The actual reflected quotient of the two Gamma factors in the Rankin completion. -/
def rankinGammaPhase (k : ℤ) (t : ℝ) : ℂ :=
  gammaVerticalPhase (1 / 2) t * gammaVerticalPhase ((k : ℝ) - 1 / 2) t

/-- The real logarithmic frequency of the actual two-Gamma quotient. -/
def rankinGammaFrequency (k : ℤ) (t : ℝ) : ℝ :=
  gammaVerticalFrequency (1 / 2) t + gammaVerticalFrequency ((k : ℝ) - 1 / 2) t

/-- Positive integral weight places both actual Gamma arguments in the right half-plane. -/
theorem rankinGamma_shift_pos {k : ℤ} (hk : 0 < k) : 0 < (k : ℝ) - 1 / 2 := by
  have hh : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  linarith

/-- The phase is exactly the literal reflected two-Gamma quotient, with the source's weight shift. -/
theorem rankinGammaPhase_eq (k : ℤ) (t : ℝ) :
    rankinGammaPhase k t =
      Gamma ((1 / 2 : ℂ) - (t : ℂ) * I) * Gamma (((k : ℝ) - 1 / 2 : ℝ) - (t : ℂ) * I) /
        (Gamma ((1 / 2 : ℂ) + (t : ℂ) * I) * Gamma (((k : ℝ) - 1 / 2 : ℝ) + (t : ℂ) * I)) := by
  simp only [rankinGammaPhase, gammaVerticalPhase, gammaVerticalPoint, ofReal_neg,
    neg_mul, ← sub_eq_add_neg, ofReal_div, ofReal_one, ofReal_ofNat, mul_div_mul_comm]

/-- The true Rankin Gamma phase has unit modulus. -/
theorem norm_rankinGammaPhase {k : ℤ} (hk : 0 < k) (t : ℝ) : ‖rankinGammaPhase k t‖ = 1 := by
  rw [rankinGammaPhase, norm_mul, norm_gammaVerticalPhase (by norm_num),
    norm_gammaVerticalPhase (rankinGamma_shift_pos hk), mul_one]

/-- The exact derivative of the genuine two-Gamma phase. -/
theorem hasDerivAt_rankinGammaPhase {k : ℤ} (hk : 0 < k) (t : ℝ) :
    HasDerivAt (rankinGammaPhase k) (I * (rankinGammaFrequency k t : ℂ) * rankinGammaPhase k t) t := by
  have hh := (hasDerivAt_gammaVerticalPhase (by norm_num : (0 : ℝ) < 1 / 2) t).mul
    (hasDerivAt_gammaVerticalPhase (rankinGamma_shift_pos hk) t)
  convert hh using 1
  simp only [rankinGammaPhase, rankinGammaFrequency, ofReal_add]
  ring

/-- The two actual logarithmic derivatives yield the exact derivative of the Rankin frequency. -/
theorem hasDerivAt_rankinGammaFrequency {k : ℤ} (hk : 0 < k) (t : ℝ) :
    HasDerivAt (rankinGammaFrequency k)
      (deriv (gammaVerticalFrequency (1 / 2)) t + deriv (gammaVerticalFrequency ((k : ℝ) - 1 / 2)) t) t :=
  (hasDerivAt_gammaVerticalFrequency (by norm_num : (0 : ℝ) < 1 / 2) t).differentiableAt.hasDerivAt.add
    (hasDerivAt_gammaVerticalFrequency (rankinGamma_shift_pos hk) t).differentiableAt.hasDerivAt

/-- The actual two-Gamma frequency has leading term −4 log |t|, with an explicit inverse-height error. -/
theorem abs_rankinGammaFrequency_add_log_le {k : ℤ} (hk : 0 < k) {t : ℝ} (ht : 1 ≤ |t|) :
    |rankinGammaFrequency k t + 4 * Real.log (|t|)| ≤ (16 + 2 * (k : ℝ)) / |t| := by
  have h1 := abs_gammaVerticalFrequency_add_log_le (by norm_num : (0 : ℝ) < 1 / 2) ht
  have h2 := abs_gammaVerticalFrequency_add_log_le (rankinGamma_shift_pos hk) ht
  calc
    _ = |(gammaVerticalFrequency (1 / 2) t + 2 * Real.log (|t|)) +
        (gammaVerticalFrequency ((k : ℝ) - 1 / 2) t + 2 * Real.log (|t|))| := by
      congr 1
      unfold rankinGammaFrequency
      ring
    _ ≤ |gammaVerticalFrequency (1 / 2) t + 2 * Real.log (|t|)| +
        |gammaVerticalFrequency ((k : ℝ) - 1 / 2) t + 2 * Real.log (|t|)| := abs_add_le _ _
    _ ≤ 2 * (4 + 1 / 2) / |t| + 2 * (4 + ((k : ℝ) - 1 / 2)) / |t| := add_le_add h1 h2
    _ = _ := by ring

/-- The genuine Rankin frequency has strictly negative reciprocal curvature at explicit large heights. -/
theorem rankinGammaFrequency_deriv_bounds {k : ℤ} (hk : 0 < k) {t : ℝ}
    (ht : 128 ≤ t) (hkt : (k : ℝ) - 1 / 2 ≤ t) :
    -8 / t ≤ deriv (rankinGammaFrequency k) t ∧ deriv (rankinGammaFrequency k) t ≤ -1 / t := by
  rw [(hasDerivAt_rankinGammaFrequency hk t).deriv]
  have h1 := gammaVerticalFrequency_deriv_bounds (by norm_num : (0 : ℝ) < 1 / 2) ht (by linarith)
  have h2 := gammaVerticalFrequency_deriv_bounds (rankinGamma_shift_pos hk) ht hkt
  have he1 : -8 / t = 2 * (-4 / t) := by ring
  have he2 : -1 / t = 2 * (-1 / (2 * t)) := by ring
  rw [he1, he2]
  constructor <;> linarith

end
end Dubon2026
