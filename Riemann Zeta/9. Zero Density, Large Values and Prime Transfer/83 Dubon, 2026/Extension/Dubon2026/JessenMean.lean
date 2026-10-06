import Dubon2026.VerticalLogTail

/-! # The actual symmetric vertical logarithmic mean equals the Haar potential -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem haarLogPotential_le_truncated {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) (σ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    haarLogPotential a N σ ≤
      ∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N := by
  apply integral_mono_ae (integrable_bohrOnTorus_log a N σ)
    (((truncatedLogNorm ε hε).comp (bohrOnTorus a N σ)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  filter_upwards [bohrOnTorus_ne_zero_ae hN ha σ] with z hz
  exact Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)

theorem eventually_verticalLogMean_ge_haar_sub {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, haarLogPotential a N σ - δ ≤ verticalLogMean a N σ T := by
  obtain ⟨K, η, C, _, hη, _, hb⟩ := exists_uniform_vertical_logTruncationError_bound hN ha σ
  have hdecay : Tendsto (fun R : ℝ => 2 * (K : ℝ) * C * Real.exp (-R)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * (K : ℝ) * C)
  obtain ⟨R, hR, herr⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((tendsto_order.mp hdecay).2 (δ / 2) (half_pos hδ))).exists
  let ε := η * Real.exp (-(K : ℝ) * R)
  have hε : 0 < ε := mul_pos hη (Real.exp_pos _)
  have hh := haarLogPotential_le_truncated hN ha σ hε
  have ht := (tendsto_order.mp (tendsto_truncated_vertical_log a N σ hε)).1
    (haarLogPotential a N σ - δ / 2) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht] with T hT hmean
  have herror := hb R hR T hT
  have hdiff : (2 * T)⁻¹ * (∫ t in -T..T,
      logTruncationError ε (dirichletSum a N ((σ : ℂ) + Complex.I * t))) =
      (2 * T)⁻¹ * (∫ t in -T..T,
        Real.log (max ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖ ε)) -
          verticalLogMean a N σ T := by
    simp only [logTruncationError]
    have hi : IntervalIntegrable (fun t : ℝ =>
        Real.log (max ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖ ε)) volume (-T) T :=
      (((truncatedLogNorm ε hε).continuous.comp
        (continuous_vertical_dirichletSum a N σ)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub hi (intervalIntegrable_vertical_log a N σ (-T) T)]
    unfold verticalLogMean
    ring
  change (2 * T)⁻¹ * (∫ t in -T..T,
    logTruncationError ε (dirichletSum a N ((σ : ℂ) + Complex.I * t))) ≤ _ at herror
  rw [hdiff] at herror
  linarith

theorem tendsto_verticalLogMean_haar {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    Tendsto (verticalLogMean a N σ) atTop (𝓝 (haarLogPotential a N σ)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hd : 0 < (haarLogPotential a N σ - b) / 2 := half_pos (sub_pos.mpr hb)
    filter_upwards [eventually_verticalLogMean_ge_haar_sub hN ha σ hd] with T hT
    linarith
  · intro b hb
    have hd : 0 < (b - haarLogPotential a N σ) / 2 := half_pos (sub_pos.mpr hb)
    filter_upwards [eventually_verticalLogMean_le_haar_add hN ha σ hd] with T hT
    linarith

/-- Jessen's potential constructed as the limit of the actual symmetric vertical logarithmic mean. -/
def jessenFunction (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  limUnder atTop (verticalLogMean a N σ)

theorem jessenFunction_eq_haar {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    jessenFunction a N σ = haarLogPotential a N σ :=
  (tendsto_verticalLogMean_haar hN ha σ).limUnder_eq

theorem tendsto_verticalLogMean_jessen {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    Tendsto (verticalLogMean a N σ) atTop (𝓝 (jessenFunction a N σ)) := by
  rw [jessenFunction_eq_haar hN ha]
  exact tendsto_verticalLogMean_haar hN ha σ

theorem jessenFunction_bounds {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (σ : ℝ) :
    0 ≤ jessenFunction a N σ ∧ jessenFunction a N σ ≤ Real.log (coefficientEnergy a N σ) / 2 := by
  rw [jessenFunction_eq_haar hN (ha.trans_ne one_ne_zero)]
  exact haarLogPotential_bounds hN ha σ

end

end Dubon2026
