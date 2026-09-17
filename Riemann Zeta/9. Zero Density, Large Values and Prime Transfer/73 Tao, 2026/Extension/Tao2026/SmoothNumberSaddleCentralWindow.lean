import Tao2026.SmoothNumberSaddleFrequency
import Tao2026.SmoothNumberSaddleRegimes

/-!
# The finite central frequency window

This module packages the source-scale hypothesis for the normalized smooth
saddle characteristic function as an explicit symmetric interval.  The
radius is positive at every nondegenerate finite saddle, and throughout that
interval the characteristic function has the universal Gaussian envelope
proved in `SmoothNumberSaddleFrequency`.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- The largest symmetric normalized-frequency interval supplied directly by
the uniform prime-local contraction criterion. -/
noncomputable def smoothSaddleCentralRadius (X y : ℕ) : ℝ :=
  Real.pi / 2 *
      (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) *
    smoothSaddleStandardDeviation X y / Real.log (y : ℝ)

/-- The finite central radius is strictly positive whenever the saddle is
nondegenerate. -/
theorem smoothSaddleCentralRadius_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleCentralRadius X y := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hcontraction :
      0 < 1 - (2 : ℝ) ^ (-smoothSaddlePoint X y) := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      one_lt_two (neg_neg_of_pos hsigma))
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleCentralRadius
  positivity

/-- The defining radius exactly saturates the source-scale frequency bound.
-/
theorem smoothSaddleCentralRadius_mul_log_div_sd
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCentralRadius X y * Real.log (y : ℝ) /
        smoothSaddleStandardDeviation X y =
      Real.pi / 2 *
        (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) := by
  have hsd := (smoothSaddleStandardDeviation_pos hX hy).ne'
  have hlog : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).ne'
  unfold smoothSaddleCentralRadius
  field_simp [hsd, hlog]

/-- Membership in the explicit symmetric interval implies the source-scale
condition used by the prime-local Gaussian estimate. -/
theorem smoothSaddleFrequencyRange_of_abs_le_centralRadius
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {t : ℝ}
    (ht : |t| ≤ smoothSaddleCentralRadius X y) :
    |t| * Real.log (y : ℝ) / smoothSaddleStandardDeviation X y ≤
      Real.pi / 2 *
        (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) := by
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  calc
    |t| * Real.log (y : ℝ) / smoothSaddleStandardDeviation X y ≤
        smoothSaddleCentralRadius X y * Real.log (y : ℝ) /
          smoothSaddleStandardDeviation X y := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ht hlog) hsd.le
    _ = Real.pi / 2 *
        (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) :=
      smoothSaddleCentralRadius_mul_log_div_sd hX hy

/-- Conversely, the source-scale condition is exactly membership in the
explicit central interval. -/
theorem abs_le_smoothSaddleCentralRadius_iff
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {t : ℝ} :
    |t| ≤ smoothSaddleCentralRadius X y ↔
      |t| * Real.log (y : ℝ) / smoothSaddleStandardDeviation X y ≤
        Real.pi / 2 *
          (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  constructor
  · exact smoothSaddleFrequencyRange_of_abs_le_centralRadius hX hy
  · intro ht
    rw [div_le_iff₀ hsd] at ht
    rw [show smoothSaddleCentralRadius X y =
        (Real.pi / 2 *
            (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) *
          smoothSaddleStandardDeviation X y) /
            Real.log (y : ℝ) by
      unfold smoothSaddleCentralRadius
      ring]
    rw [le_div_iff₀ hlog]
    simpa [mul_assoc] using ht

/-- The normalized characteristic function has a universal squared Gaussian
envelope throughout the explicit central interval. -/
theorem norm_smoothSaddleNormalizedCharacteristic_sq_le_exp_of_abs_le_radius
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (ht : |t| ≤ smoothSaddleCentralRadius X y) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 ≤
      Real.exp (-(2 / Real.pi ^ 2 * t ^ 2)) := by
  exact norm_smoothSaddleNormalizedCharacteristic_sq_le_exp_of_range
    hX hy t (smoothSaddleFrequencyRange_of_abs_le_centralRadius hX hy ht)

/-- Unsquared Gaussian envelope throughout the explicit central interval. -/
theorem norm_smoothSaddleNormalizedCharacteristic_le_exp_of_abs_le_radius
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (ht : |t| ≤ smoothSaddleCentralRadius X y) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ≤
      Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) := by
  exact norm_smoothSaddleNormalizedCharacteristic_le_exp_of_range
    hX hy t (smoothSaddleFrequencyRange_of_abs_le_centralRadius hX hy ht)

/-- Once the maximal normalized prime phase tends to zero, the explicit
central radius expands to all fixed frequencies.  This isolates the precise
curvature estimate still needed from the critical-regime analysis. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleCentralRadius_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hscale : Tendsto (fun n =>
      Real.log (y n : ℝ) /
        smoothSaddleStandardDeviation (X n) (y n)) atTop (nhds 0)) :
    Tendsto (fun n => smoothSaddleCentralRadius (X n) (y n))
      atTop atTop := by
  let q : ℕ → ℝ := fun n =>
    Real.log (y n : ℝ) /
      smoothSaddleStandardDeviation (X n) (y n)
  have hqPos : ∀ᶠ n in atTop, 0 < q n := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact div_pos
      (Real.log_pos (by exact_mod_cast (show 1 < y n by omega)))
      (smoothSaddleStandardDeviation_pos hX hy)
  have hqWithin : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hscale, hqPos⟩
  have hqInv : Tendsto (fun n => (q n)⁻¹) atTop atTop :=
    hqWithin.inv_tendsto_nhdsGT_zero
  have hsaddleNeg : Tendsto (fun n =>
      -smoothSaddlePoint (X n) (y n)) atTop (nhds (-1)) := by
    simpa using (hregime.tendsto_smoothSaddlePoint_one hα).neg
  have hpow : Tendsto (fun n =>
      (2 : ℝ) ^ (-smoothSaddlePoint (X n) (y n)))
      atTop (nhds ((2 : ℝ) ^ (-1 : ℝ))) := by
    exact (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousAt.tendsto.comp
      hsaddleNeg
  have hfactor : Tendsto (fun n =>
      Real.pi / 2 *
        (1 - (2 : ℝ) ^ (-smoothSaddlePoint (X n) (y n))))
      atTop (nhds (Real.pi / 4)) := by
    have hpi : Tendsto (fun _ : ℕ => Real.pi / 2) atTop
        (nhds (Real.pi / 2)) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds 1) := tendsto_const_nhds
    have h := hpi.mul (hone.sub hpow)
    convert h using 1
    norm_num [Real.rpow_neg_one]
    ring
  have hproduct := hfactor.pos_mul_atTop
    (by positivity [Real.pi_pos] : 0 < Real.pi / 4) hqInv
  apply hproduct.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  have hsd := (smoothSaddleStandardDeviation_pos hX hy).ne'
  have hlog : Real.log (y n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y n by omega))).ne'
  dsimp [q]
  unfold smoothSaddleCentralRadius
  field_simp [hsd, hlog]

/-- Under the same vanishing maximal-phase hypothesis, every fixed frequency
eventually lies in the explicit central interval. -/
theorem IsTaoCriticalSmoothRegime.eventually_abs_le_smoothSaddleCentralRadius
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hscale : Tendsto (fun n =>
      Real.log (y n : ℝ) /
        smoothSaddleStandardDeviation (X n) (y n)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, |t| ≤ smoothSaddleCentralRadius (X n) (y n) := by
  exact (hregime.tendsto_smoothSaddleCentralRadius_atTop hα hscale).eventually
    (eventually_ge_atTop |t|)

/-- Consequently, the universal Gaussian envelope holds eventually at every
fixed normalized frequency. -/
theorem IsTaoCriticalSmoothRegime.eventually_norm_normalizedCharacteristic_le_gaussian
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hscale : Tendsto (fun n =>
      Real.log (y n : ℝ) /
        smoothSaddleStandardDeviation (X n) (y n)) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      ‖smoothSaddleNormalizedCharacteristic (X n) (y n) t‖ ≤
        Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_abs_le_smoothSaddleCentralRadius hα hscale] with
      n hX hy ht
  exact norm_smoothSaddleNormalizedCharacteristic_le_exp_of_abs_le_radius
    hX hy t ht

end

end Tao2026
