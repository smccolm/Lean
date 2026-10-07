import Dubon2026.GammaHorizontalLogNorm
import Dubon2026.GammaHorizontalDigamma

/-! # Sharp power and derivative bounds for the actual reflected Gamma-ratio amplitude -/

namespace Dubon2026

open Complex

noncomputable section

/-- Conjugation identifies the actual reflected amplitude with the same-height Gamma norm ratio. -/
theorem norm_reflectedGammaRatio_eq (a b t : ℝ) :
    ‖reflectedGammaRatio a b t‖ = ‖Gamma (gammaVerticalPoint a t)‖ / ‖Gamma (gammaVerticalPoint b t)‖ := by
  rw [reflectedGammaRatio, gammaVerticalPoint_neg, Gamma_conj, norm_div, norm_conj]

/-- The logarithm of the actual nonzero Gamma-ratio amplitude is the true horizontal log-modulus difference. -/
theorem log_norm_reflectedGammaRatio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Real.log ‖reflectedGammaRatio a b t‖ = gammaHorizontalLogNorm t a - gammaHorizontalLogNorm t b := by
  rw [norm_reflectedGammaRatio_eq, Real.log_div]
  · rfl
  · exact norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (by simpa only [gammaVerticalPoint_re] using ha))
  · exact norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (by simpa only [gammaVerticalPoint_re] using hb))

/-- The actual reflected Gamma-ratio amplitude has its sharp horizontal power, with an explicit fixed-shift constant. -/
theorem norm_reflectedGammaRatio_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 ≤ t) :
    ‖reflectedGammaRatio a b t‖ ≤ Real.exp ((4 + max a b) * |a - b|) * t ^ (a - b) := by
  have ht0 : 0 < t := by linarith
  have hD : 0 ≤ 4 + max a b := by linarith [le_max_left a b]
  have hh := (abs_le.mp (abs_gammaHorizontalLogNorm_sub_le ha hb ht)).2
  have hsmall : ((4 + max a b) / t) * |a - b| ≤ (4 + max a b) * |a - b| :=
    mul_le_mul_of_nonneg_right (div_le_self hD ht) (abs_nonneg _)
  have hlog : Real.log ‖reflectedGammaRatio a b t‖ ≤
      (a - b) * Real.log t + (4 + max a b) * |a - b| := by
    rw [log_norm_reflectedGammaRatio ha hb]
    linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (norm_pos_iff.mpr (reflectedGammaRatio_ne_zero ha hb t)), Real.exp_add] at he
  convert he using 1
  rw [Real.rpow_def_of_pos ht0, mul_comm (Real.log t) (a - b)]
  ring

/-- The genuine amplitude derivative is bounded by its true amplitude times an explicit inverse-height factor. -/
theorem abs_deriv_norm_reflectedGammaRatio_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 ≤ t) :
    |deriv (fun u => ‖reflectedGammaRatio a b u‖) t| ≤
      (33 * |a - b| / t) * ‖reflectedGammaRatio a b t‖ := by
  rw [(hasDerivAt_norm_reflectedGammaRatio ha hb t).deriv, abs_mul,
    abs_of_nonneg (norm_nonneg _)]
  have hh := (Complex.abs_im_le_norm
    (digamma (gammaVerticalPoint b t) - digamma (gammaVerticalPoint a t))).trans
    (norm_digamma_horizontal_sub_le hb ha ht)
  have hbnd : |(digamma (gammaVerticalPoint b t)).im - (digamma (gammaVerticalPoint a t)).im| ≤
      33 * |a - b| / t := by
    calc
      _ ≤ (33 / t) * |b - a| := hh
      _ = _ := by rw [abs_sub_comm]; ring
  exact mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)

end
end Dubon2026
