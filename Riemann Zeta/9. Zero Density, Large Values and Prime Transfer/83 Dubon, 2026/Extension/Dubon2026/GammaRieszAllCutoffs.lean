import Dubon2026.GammaRieszPartialBounds
import Dubon2026.GammaRieszContourShift

/-! # Uniform sharp Gamma kernel bounds at every finite cutoff -/

namespace Dubon2026

open Complex Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- Every nonnegative finite positive-half cutoff obeys one sharp bound uniform in both cutoff and Mellin argument. -/
theorem norm_gammaRiesz_all_positive_cutoffs_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) (hu : 0 ≤ u) :
    ‖∫ t in 0..u, gammaRieszIntegrand k r x t‖ ≤
      (gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) * x ^ gammaRieszLine r := by
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  have hC := gammaRieszConstant_pos k r
  have hxpow := Real.rpow_pos_of_pos hx (gammaRieszLine r)
  by_cases hsmall : u ≤ gammaRieszBaseHeight k
  · apply (norm_gammaRiesz_compact_partial_le hk hr0 hr2 hx hu hsmall).trans
    nlinarith
  have hH : gammaRieszBaseHeight k ≤ u := le_of_not_ge hsmall
  by_cases hlow : u ≤ gammaRieszWindowHeight k x
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 (gammaRieszBaseHeight k)) (hc.intervalIntegrable (gammaRieszBaseHeight k) u)]
    apply (norm_add_le _ _).trans
    have h1 := norm_gammaRieszIntegrand_compact_integral_le hx k r
    have h2 := norm_gammaRiesz_low_partial_le hk hr0 hr2 hx hH hlow
    nlinarith
  have hS : gammaRieszWindowHeight k x ≤ u := le_of_not_ge hlow
  by_cases hwin : u ≤ 4 * gammaRieszWindowHeight k x
  · have he : (∫ t in 0..u, gammaRieszIntegrand k r x t) =
        (∫ t in 0..gammaRieszBaseHeight k, gammaRieszIntegrand k r x t) +
        (∫ t in gammaRieszBaseHeight k..gammaRieszWindowHeight k x, gammaRieszIntegrand k r x t) +
        (∫ t in gammaRieszWindowHeight k x..u, gammaRieszIntegrand k r x t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 (gammaRieszBaseHeight k))
        (hc.intervalIntegrable (gammaRieszBaseHeight k) (gammaRieszWindowHeight k x)),
        intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 (gammaRieszWindowHeight k x)) (hc.intervalIntegrable (gammaRieszWindowHeight k x) u)]
    rw [he]
    apply norm_add₃_le.trans
    have h1 := norm_gammaRieszIntegrand_compact_integral_le hx k r
    have h2 := norm_gammaRiesz_low_integral_le hk hr0 hr2 hx
    have h3 := norm_gammaRiesz_window_partial_le hk hr0 hr2 hx hS hwin
    nlinarith
  · exact norm_gammaRiesz_cutoff_integral_le hk hr0 hr2 hx (le_of_not_ge hwin)

/-- The literal normalized symmetric finite Gamma contour has a sharp bound independent of its height. -/
theorem norm_gammaRiesz_all_vertical_cutoffs_le {k r x T : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) (hT : 0 ≤ T) :
    ‖gammaRieszVerticalCutoff k r x (gammaRieszLine r) T‖ ≤
      ((gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) / Real.pi) * x ^ gammaRieszLine r := by
  have hh := norm_gammaRiesz_all_positive_cutoffs_le hk hr0 hr2 hx hT
  change ‖(1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, gammaRieszIntegrand k r x t‖ ≤ _
  rw [gammaRiesz_symmetric_integral_eq hk hr0 hr2 hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖∫ t in 0..T, gammaRieszIntegrand k r x t‖ +
        ‖conj (∫ t in 0..T, gammaRieszIntegrand k r x t)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (2 * ((gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) * x ^ gammaRieszLine r)) := by
      rw [norm_conj]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

end
end Dubon2026
