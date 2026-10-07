import Dubon2026.GammaRieszKernel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # An explicit stationary window for the actual Riesz Gamma integral -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A fixed height dominating all shift and frequency-error bounds. -/
def gammaRieszBaseHeight (k : ℝ) : ℝ := max 128 (21 + 2 * k)

/-- The lower edge of an actual stationary window, cut off at the fixed admissible height. -/
def gammaRieszWindowHeight (k x : ℝ) : ℝ :=
  max (gammaRieszBaseHeight k) (Real.exp ((Real.log x - 2) / 4))

/-- The fixed admissible height is positive and dominates both required thresholds. -/
theorem gammaRieszBaseHeight_properties (k : ℝ) :
    128 ≤ gammaRieszBaseHeight k ∧ 21 + 2 * k ≤ gammaRieszBaseHeight k :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- The actual window starts at or beyond the fixed admissible height. -/
theorem gammaRieszWindowHeight_ge (k x : ℝ) :
    gammaRieszBaseHeight k ≤ gammaRieszWindowHeight k x := le_max_left _ _

/-- A nonempty low-frequency interval ends at the exact positive logarithmic threshold. -/
theorem gammaRieszWindowHeight_log {k x : ℝ}
    (hne : gammaRieszBaseHeight k ≠ gammaRieszWindowHeight k x) :
    Real.log x - 4 * Real.log (gammaRieszWindowHeight k x) = 2 := by
  have he : gammaRieszWindowHeight k x = Real.exp ((Real.log x - 2) / 4) := by
    unfold gammaRieszWindowHeight at *
    exact max_eq_right (le_of_not_ge (fun h => hne (max_eq_left h).symm))
  rw [he, Real.log_exp]
  ring

/-- Twice doubling the window start passes the actual negative-frequency tail threshold. -/
theorem gammaRieszTailHeight_le_four_window (k x : ℝ) :
    gammaRieszTailHeight k x ≤ 4 * gammaRieszWindowHeight k x := by
  have hS := gammaRieszWindowHeight_ge k x
  have hH := gammaRieszBaseHeight_properties k
  have hS0 : 0 ≤ gammaRieszWindowHeight k x := by linarith [hH.1]
  have he : Real.exp ((Real.log x + 2) / 4) = Real.exp ((Real.log x - 2) / 4) * Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp ((Real.log x + 2) / 4) ≤ 4 * gammaRieszWindowHeight k x := by
    rw [he]
    calc
      _ ≤ gammaRieszWindowHeight k x * Real.exp 1 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos 1).le
      _ ≤ gammaRieszWindowHeight k x * 4 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.exp_one_lt_three]) hS0
      _ = _ := by ring
  unfold gammaRieszTailHeight
  exact max_le (by linarith [hH.1]) (max_le (by linarith [hH.2]) hexp)

/-- A positive upper-endpoint logarithmic threshold gives a genuine bound over the whole lower interval. -/
theorem norm_gammaRieszIntegrand_lower_interval_le {k r x T u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : 128 ≤ T) (hkT : 21 + 2 * k ≤ T) (hu : T ≤ u)
    (hwindow : 2 ≤ Real.log x - 4 * Real.log u) :
    ‖∫ t in T..u, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r / Real.sqrt T := by
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_shifts_pos hk hr0 hr2
  obtain ⟨haT, hbT, hcT, hdT, herror⟩ := gammaRiesz_shifts_le hk hr0 hr2 hkT
  have hfreq : 1 ≤ doubleGammaFrequency (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
      (k - gammaRieszLine r) (gammaRieszLine r + k - 1) (Real.log x) u := by
    have hh := (abs_le.mp (abs_doubleGammaFrequency_sub_log_le ha hb hc hd
      (by linarith : 1 ≤ u) (Real.log x))).1
    have hdiv := (div_le_one (by linarith : 0 < u)).mpr (herror.trans hu)
    linarith
  have hh := norm_doubleGamma_product_interval_le_of_separation ha hb hc hd (gammaRiesz_power k r)
    hT haT hbT hcT hdT hu (Real.log x) (Or.inr hfreq)
  rw [intervalIntegral.integral_congr (fun t _ => gammaRieszIntegrand_eq hx k r t),
    intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le (gammaRieszLine r)) using 1
  unfold gammaRieszConstant
  ring

end
end Dubon2026
