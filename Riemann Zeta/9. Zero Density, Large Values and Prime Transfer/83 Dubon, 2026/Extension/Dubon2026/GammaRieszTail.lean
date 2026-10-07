import Dubon2026.GammaRieszDyadic
import Dubon2026.GammaNonstationaryTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Genuine upper-tail estimates and conditional convergence of the Riesz Gamma integral -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- An explicit height beyond the stationary region of the actual Riesz Gamma integrand. -/
def gammaRieszTailHeight (k x : ℝ) : ℝ :=
  max 128 (max (21 + 2 * k) (Real.exp ((Real.log x + 2) / 4)))

/-- Every height beyond this threshold dominates the fixed shifts and lies past the stationary window. -/
theorem gammaRieszTailHeight_properties {k x T : ℝ} (hT : gammaRieszTailHeight k x ≤ T) :
    128 ≤ T ∧ 21 + 2 * k ≤ T ∧ Real.log x - 4 * Real.log T ≤ -2 := by
  have h1 : 128 ≤ T := (le_max_left _ _).trans hT
  have h2 : 21 + 2 * k ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have h3 : Real.exp ((Real.log x + 2) / 4) ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hlog := Real.log_le_log (Real.exp_pos ((Real.log x + 2) / 4)) h3
  rw [Real.log_exp] at hlog
  exact ⟨h1, h2, by linarith⟩

/-- The whole finite upper tail of the literal Riesz Gamma integrand has inverse-square-root decay. -/
theorem norm_gammaRieszIntegrand_tail_le {k r x T u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : gammaRieszTailHeight k x ≤ T) (hu : T ≤ u) :
    ‖∫ t in T..u, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r / Real.sqrt T := by
  obtain ⟨h128, hkT, hwindow⟩ := gammaRieszTailHeight_properties hT
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_shifts_pos hk hr0 hr2
  obtain ⟨haT, hbT, hcT, hdT, herror⟩ := gammaRiesz_shifts_le hk hr0 hr2 hkT
  have hfreq : doubleGammaFrequency (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
      (k - gammaRieszLine r) (gammaRieszLine r + k - 1) (Real.log x) T ≤ -1 := by
    have hh := (abs_le.mp (abs_doubleGammaFrequency_sub_log_le ha hb hc hd
      (by linarith : 1 ≤ T) (Real.log x))).2
    have hdiv := (div_le_one (by linarith : 0 < T)).mpr herror
    linarith
  have hh := norm_doubleGamma_product_interval_le_of_separation ha hb hc hd (gammaRiesz_power k r)
    h128 haT hbT hcT hdT hu (Real.log x) (Or.inl hfreq)
  rw [intervalIntegral.integral_congr (fun t _ => gammaRieszIntegrand_eq hx k r t),
    intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le (gammaRieszLine r)) using 1
  unfold gammaRieszConstant
  ring

/-- The actual positive-half Riesz Gamma integral converges as a limit of ordinary finite integrals. -/
theorem exists_tendsto_gammaRieszIntegral {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    ∃ L : ℂ, Tendsto (fun u : ℝ => ∫ t in 0..u, gammaRieszIntegrand k r x t) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  have hzero : Tendsto (fun T : ℝ =>
      (4 * gammaRieszConstant k r * x ^ gammaRieszLine r) * T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (4 * gammaRieszConstant k r * x ^ gammaRieszLine r)
  obtain ⟨N, hsmall, hN⟩ := ((hzero.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop (gammaRieszTailHeight k x))).exists
  refine ⟨N, fun u hu => ?_⟩
  rw [dist_eq_norm, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 N) (hc.intervalIntegrable N u), add_sub_cancel_left]
  have hb := norm_gammaRieszIntegrand_tail_le hk hr0 hr2 hx hN hu
  have hN0 : 0 < N := by linarith [(gammaRieszTailHeight_properties hN).1]
  rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at hsmall
  exact hb.trans_lt hsmall

end
end Dubon2026
