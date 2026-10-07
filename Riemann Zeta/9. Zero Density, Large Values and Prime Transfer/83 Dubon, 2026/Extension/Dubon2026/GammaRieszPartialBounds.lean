import Dubon2026.GammaRieszBounds

/-! # Sharp bounds for every partial interval in the genuine Gamma stationary decomposition -/

namespace Dubon2026

open Complex Set MeasureTheory Filter

noncomputable section

/-- Every truncated part of the fixed compact interval has the same genuine amplitude majorant. -/
theorem norm_gammaRiesz_compact_partial_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hu0 : 0 ≤ u) (hu : u ≤ gammaRieszBaseHeight k) :
    ‖∫ t in 0..u, gammaRieszIntegrand k r x t‖ ≤
      gammaRieszCompactMass k r * x ^ gammaRieszLine r := by
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  calc
    _ ≤ ∫ t in 0..u, ‖gammaRieszIntegrand k r x t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hu0
    _ ≤ ∫ t in 0..gammaRieszBaseHeight k, ‖gammaRieszIntegrand k r x t‖ :=
      intervalIntegral.integral_mono_interval le_rfl hu0 hu
        (Eventually.of_forall (fun _ => norm_nonneg _)) (hc.norm.intervalIntegrable _ _)
    _ = _ := by
      rw [intervalIntegral.integral_congr (fun t _ => norm_gammaRieszIntegrand_eq hx k r t),
        intervalIntegral.integral_const_mul]
      exact mul_comm _ _

/-- Every genuine partial lower interval satisfies the same nonstationary bound. -/
theorem norm_gammaRiesz_low_partial_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hu0 : gammaRieszBaseHeight k ≤ u) (hu : u ≤ gammaRieszWindowHeight k x) :
    ‖∫ t in gammaRieszBaseHeight k..u, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  have hC := gammaRieszConstant_pos k r
  by_cases he : gammaRieszBaseHeight k = gammaRieszWindowHeight k x
  · have huu : u = gammaRieszBaseHeight k := le_antisymm (hu.trans he.ge) hu0
    rw [huu, intervalIntegral.integral_same, norm_zero]
    positivity
  have huPos : 0 < u := by linarith [(gammaRieszBaseHeight_properties k).1]
  have hlog := Real.log_le_log huPos hu
  have hwindow := gammaRieszWindowHeight_log he
  have hh := norm_gammaRieszIntegrand_lower_interval_le hk hr0 hr2 hx
    (gammaRieszBaseHeight_properties k).1 (gammaRieszBaseHeight_properties k).2 hu0 (by linarith)
  exact hh.trans (div_le_self (by positivity)
    (by simpa using Real.sqrt_le_sqrt (show 1 ≤ gammaRieszBaseHeight k by
      linarith [(gammaRieszBaseHeight_properties k).1])))

/-- At most two true dyadic blocks bound every partial stationary window, with no cutoff-dependent constant. -/
theorem norm_gammaRiesz_window_partial_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hu0 : gammaRieszWindowHeight k x ≤ u) (hu : u ≤ 4 * gammaRieszWindowHeight k x) :
    ‖∫ t in gammaRieszWindowHeight k x..u, gammaRieszIntegrand k r x t‖ ≤
      16 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  have hC := gammaRieszConstant_pos k r
  let S := gammaRieszWindowHeight k x
  have h128 : 128 ≤ S := (gammaRieszBaseHeight_properties k).1.trans (gammaRieszWindowHeight_ge k x)
  have hkS : 21 + 2 * k ≤ S := (gammaRieszBaseHeight_properties k).2.trans (gammaRieszWindowHeight_ge k x)
  by_cases hsmall : u ≤ 2 * S
  · have hh := norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx h128 hkS le_rfl hu0 hsmall
    apply hh.trans
    have hp : 0 ≤ gammaRieszConstant k r * x ^ gammaRieszLine r := by positivity
    nlinarith
  · have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
    have h1 := norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx h128 hkS
      (le_refl S) (show S ≤ 2 * S by linarith) (le_refl (2 * S))
    have h2 := norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx
      (show 128 ≤ 2 * S by linarith) (show 21 + 2 * k ≤ 2 * S by linarith)
      (le_refl (2 * S)) (le_of_not_ge hsmall) (show u ≤ 2 * (2 * S) by dsimp [S] at *; linarith)
    change ‖∫ t in S..u, gammaRieszIntegrand k r x t‖ ≤ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable S (2 * S))
      (hc.intervalIntegrable (2 * S) u)]
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end
end Dubon2026
