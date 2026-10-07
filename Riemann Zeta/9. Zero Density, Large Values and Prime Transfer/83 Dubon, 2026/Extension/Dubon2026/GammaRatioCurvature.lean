import Dubon2026.GammaRatioPhase

/-! # Explicit frequency and curvature of the normalized unequal-shift Gamma ratio -/

namespace Dubon2026

noncomputable section

/-- The genuine ratio frequency is differentiable with its actual pair of digamma derivatives. -/
theorem hasDerivAt_gammaRatioFrequency {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    HasDerivAt (gammaRatioFrequency a b)
      ((deriv (gammaVerticalFrequency a) t + deriv (gammaVerticalFrequency b) t) / 2) t :=
  ((hasDerivAt_gammaVerticalFrequency ha t).differentiableAt.hasDerivAt.add
    (hasDerivAt_gammaVerticalFrequency hb t).differentiableAt.hasDerivAt).div_const 2

/-- The actual unequal-shift ratio frequency has the same exact leading logarithmic term. -/
theorem abs_gammaRatioFrequency_add_log_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 1 ≤ |t|) :
    |gammaRatioFrequency a b t + 2 * Real.log (|t|)| ≤ (8 + a + b) / |t| := by
  have h1 := abs_gammaVerticalFrequency_add_log_le ha ht
  have h2 := abs_gammaVerticalFrequency_add_log_le hb ht
  have he : gammaRatioFrequency a b t + 2 * Real.log |t| =
      ((gammaVerticalFrequency a t + 2 * Real.log |t|) +
        (gammaVerticalFrequency b t + 2 * Real.log |t|)) / 2 := by
    unfold gammaRatioFrequency
    ring
  rw [he, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (|gammaVerticalFrequency a t + 2 * Real.log (|t|)| +
          |gammaVerticalFrequency b t + 2 * Real.log (|t|)|) / 2 := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (2 * (4 + a) / |t| + 2 * (4 + b) / |t|) / 2 := by gcongr
    _ = _ := by ring

/-- The actual ratio frequency has strictly negative reciprocal curvature at explicit large heights. -/
theorem gammaRatioFrequency_deriv_bounds {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 128 ≤ t) (hat : a ≤ t) (hbt : b ≤ t) :
    -4 / t ≤ deriv (gammaRatioFrequency a b) t ∧
      deriv (gammaRatioFrequency a b) t ≤ -1 / (2 * t) := by
  rw [(hasDerivAt_gammaRatioFrequency ha hb t).deriv]
  have h1 := gammaVerticalFrequency_deriv_bounds ha ht hat
  have h2 := gammaVerticalFrequency_deriv_bounds hb ht hbt
  constructor <;> linarith

end
end Dubon2026
