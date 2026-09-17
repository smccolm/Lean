import Tao2026.SmoothNumberSaddleLaplaceCutoff
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The central saddle integral

This module evaluates the normalized central-frequency contribution in the
smooth-number saddle argument.  The exact Laplace/Perron kernel tends to one,
the expanding central interval is dominated by the Gaussian envelope, and
dominated convergence gives the full standard Gaussian mass.  Thus the
central contribution to the normalized one-sided Laplace target tends to one;
the remaining analytic obligation is the complementary Perron truncation
error outside this interval.
-/

open Filter Topology MeasureTheory Set

namespace Tao2026

noncomputable section

/-- The normalized Laplace kernel `lambda / (lambda - i*t)`, written in a
form that remains defined even when the rate vanishes. -/
noncomputable def smoothSaddleLaplaceFourierKernel
    (X y : ℕ) (t : ℝ) : ℂ :=
  1 / (1 - ((t / smoothSaddleLaplaceRate X y : ℝ) : ℂ) * Complex.I)

/-- The exact centered characteristic function times the Laplace kernel,
restricted to the explicit central saddle interval. -/
noncomputable def smoothSaddleCentralFourierIntegrand
    (X y : ℕ) (t : ℝ) : ℂ :=
  (Set.Icc (-smoothSaddleCentralRadius X y)
      (smoothSaddleCentralRadius X y)).indicator
    (fun u => smoothSaddleNormalizedCharacteristic X y u *
      smoothSaddleLaplaceFourierKernel X y u) t

/-- The central integral normalized by the standard Gaussian mass. -/
noncomputable def smoothSaddleCentralLaplaceContribution
    (X y : ℕ) : ℂ :=
  (∫ t : ℝ, smoothSaddleCentralFourierIntegrand X y t) /
    (Real.sqrt (2 * Real.pi) : ℂ)

/-- The normalized saddle characteristic function is continuous. -/
theorem continuous_smoothSaddleNormalizedCharacteristic
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Continuous (smoothSaddleNormalizedCharacteristic X y) := by
  letI : IsProbabilityMeasure
      (smoothTiltedLogMeasure y (smoothSaddlePoint X y)) :=
    isProbabilityMeasure_smoothTiltedLogMeasure y
      (smoothSaddlePoint_pos hX hy)
  unfold smoothSaddleNormalizedCharacteristic smoothTiltedCharacteristic
  fun_prop

/-- The saddle Laplace rate is positive in the defining range. -/
theorem smoothSaddleLaplaceRate_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleLaplaceRate X y := by
  exact mul_pos (smoothSaddlePoint_pos hX hy)
    (smoothSaddleStandardDeviation_pos hX hy)

/-- The normalized Laplace kernel is continuous for every parameter pair. -/
theorem continuous_smoothSaddleLaplaceFourierKernel
    (X y : ℕ) :
    Continuous (smoothSaddleLaplaceFourierKernel X y) := by
  unfold smoothSaddleLaplaceFourierKernel
  apply Continuous.div continuous_const
    (continuous_const.sub
      ((Complex.continuous_ofReal.comp
        (continuous_id.div_const _)).mul continuous_const))
  intro t ht
  have hre := congrArg Complex.re ht
  norm_num at hre

/-- The normalized Laplace kernel has norm at most one. -/
theorem norm_smoothSaddleLaplaceFourierKernel_le_one
    (X y : ℕ) (t : ℝ) :
    ‖smoothSaddleLaplaceFourierKernel X y t‖ ≤ 1 := by
  unfold smoothSaddleLaplaceFourierKernel
  rw [norm_div, norm_one,
    show (1 : ℂ) - ((t / smoothSaddleLaplaceRate X y : ℝ) : ℂ) * Complex.I =
      ((1 : ℝ) : ℂ) +
        (-(t / smoothSaddleLaplaceRate X y) : ℝ) * Complex.I by push_cast; ring,
    Complex.norm_add_mul_I]
  have hs : (1 : ℝ) ≤ Real.sqrt (1 ^ 2 +
      (-(t / smoothSaddleLaplaceRate X y)) ^ 2) := by
    have := Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 ^ 2 +
        (-(t / smoothSaddleLaplaceRate X y)) ^ 2 by
          nlinarith [sq_nonneg (-(t / smoothSaddleLaplaceRate X y))])
    simpa using this
  exact (div_le_one (by linarith)).2 hs

/-- The truncated central integrand is strongly measurable. -/
theorem aestronglyMeasurable_smoothSaddleCentralFourierIntegrand
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    AEStronglyMeasurable (smoothSaddleCentralFourierIntegrand X y) := by
  unfold smoothSaddleCentralFourierIntegrand
  apply AEStronglyMeasurable.indicator
  · exact ((continuous_smoothSaddleNormalizedCharacteristic hX hy).mul
      (continuous_smoothSaddleLaplaceFourierKernel X y)).aestronglyMeasurable
  · exact measurableSet_Icc

/-- The central integrand is dominated by an integrable universal Gaussian. -/
theorem norm_smoothSaddleCentralFourierIntegrand_le_gaussian
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    ‖smoothSaddleCentralFourierIntegrand X y t‖ ≤
      Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) := by
  unfold smoothSaddleCentralFourierIntegrand
  by_cases ht : t ∈ Set.Icc (-smoothSaddleCentralRadius X y)
      (smoothSaddleCentralRadius X y)
  · rw [Set.indicator_of_mem ht, norm_mul]
    have habs : |t| ≤ smoothSaddleCentralRadius X y := by
      rw [abs_le]
      exact ht
    calc
      ‖smoothSaddleNormalizedCharacteristic X y t‖ *
          ‖smoothSaddleLaplaceFourierKernel X y t‖ ≤
          Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) * 1 :=
        mul_le_mul
          (norm_smoothSaddleNormalizedCharacteristic_le_exp_of_abs_le_radius
            hX hy t habs)
          (norm_smoothSaddleLaplaceFourierKernel_le_one X y t)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1 / Real.pi ^ 2 * t ^ 2)) := by ring
  · simp only [Set.indicator, ht, ↓reduceIte, norm_zero]
    exact (Real.exp_pos _).le

/-- At every fixed normalized frequency, the diverging Laplace rate makes
the exact kernel tend to one. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleLaplaceFourierKernel_one
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleLaplaceFourierKernel (X n) (y n) t)
      atTop (nhds 1) := by
  have hsmall : Tendsto (fun n =>
      t / smoothSaddleLaplaceRate (X n) (y n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (hregime.tendsto_smoothSaddleLaplaceRate_atTop hα)
  have hcast : Tendsto (fun n =>
      ((t / smoothSaddleLaplaceRate (X n) (y n) : ℝ) : ℂ))
      atTop (nhds 0) := by
    change Tendsto (Complex.ofReal ∘ fun n =>
      t / smoothSaddleLaplaceRate (X n) (y n)) atTop (nhds 0)
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hsmall
  have hden : Tendsto (fun n =>
      (1 : ℂ) -
        ((t / smoothSaddleLaplaceRate (X n) (y n) : ℝ) : ℂ) * Complex.I)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hcast.mul_const Complex.I)
  have hquot := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ))
    atTop (nhds 1)).div hden (by norm_num)
  change Tendsto (fun n => (1 : ℂ) /
    (1 - ((t / smoothSaddleLaplaceRate (X n) (y n) : ℝ) : ℂ) * Complex.I))
    atTop (nhds 1)
  simpa only [Pi.div_apply, div_one] using hquot

/-- At every fixed frequency, the truncated saddle integrand tends to the
standard Gaussian characteristic function. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleCentralFourierIntegrand
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleCentralFourierIntegrand (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) := by
  have hmem : ∀ᶠ n in atTop,
      t ∈ Set.Icc (-smoothSaddleCentralRadius (X n) (y n))
        (smoothSaddleCentralRadius (X n) (y n)) := by
    have habs := hregime.eventually_abs_le_smoothSaddleCentralRadius hα
      (hregime.tendsto_log_y_div_saddleStandardDeviation_zero hα) (t := t)
    filter_upwards [habs] with n hn
    rw [Set.mem_Icc, ← abs_le]
    exact hn
  have hprod : Tendsto (fun n =>
      smoothSaddleNormalizedCharacteristic (X n) (y n) t *
        smoothSaddleLaplaceFourierKernel (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) := by
    simpa using (hregime.tendsto_normalizedCharacteristic_gaussian hα
      (t := t)).mul
        (hregime.tendsto_smoothSaddleLaplaceFourierKernel_one hα (t := t))
  apply hprod.congr'
  filter_upwards [hmem] with n hn
  simp [smoothSaddleCentralFourierIntegrand, hn]

/-- The complex-valued standard Gaussian has mass `sqrt (2*pi)`. -/
theorem integral_complex_standard_gaussian :
    (∫ t : ℝ, Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  calc
    (∫ t : ℝ, Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)) =
        (∫ t : ℝ, (Real.exp (-(1 / 2 : ℝ) * t ^ 2) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Complex.ofReal_exp]
      congr 2
      ring
    _ = Complex.ofReal (∫ t : ℝ,
        Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
      exact integral_ofReal
    _ = (Real.sqrt (2 * Real.pi) : ℂ) := by
      rw [integral_gaussian]
      congr 2
      ring

/-- The entire expanding central saddle integral converges to the standard
Gaussian mass. -/
theorem IsTaoCriticalSmoothRegime.tendsto_integral_smoothSaddleCentralFourierIntegrand
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => ∫ t : ℝ,
      smoothSaddleCentralFourierIntegrand (X n) (y n) t)
      atTop (nhds (Real.sqrt (2 * Real.pi) : ℂ)) := by
  let bound : ℝ → ℝ := fun t =>
    Real.exp (-(1 / Real.pi ^ 2 * t ^ 2))
  have hboundIntegrable : Integrable bound := by
    have hpos : 0 < (1 / Real.pi ^ 2 : ℝ) := by positivity [Real.pi_pos]
    simpa [bound] using integrable_exp_neg_mul_sq hpos
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable
        (smoothSaddleCentralFourierIntegrand (X n) (y n)) := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact aestronglyMeasurable_smoothSaddleCentralFourierIntegrand hX hy
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t : ℝ,
      ‖smoothSaddleCentralFourierIntegrand (X n) (y n) t‖ ≤ bound t := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact ae_of_all _ fun t =>
      norm_smoothSaddleCentralFourierIntegrand_le_gaussian hX hy t
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun n =>
      smoothSaddleCentralFourierIntegrand (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) :=
    ae_of_all _ fun t =>
      hregime.tendsto_smoothSaddleCentralFourierIntegrand hα
  have hdct := tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundIntegrable hlim
  rw [integral_complex_standard_gaussian] at hdct
  exact hdct

/-- After the exact Gaussian normalization used by the one-sided Laplace
target, the central-frequency contribution tends to one. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleCentralLaplaceContribution_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleCentralLaplaceContribution (X n) (y n))
      atTop (nhds 1) := by
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)).ne'
  have h := (hregime.tendsto_integral_smoothSaddleCentralFourierIntegrand hα).div_const
    (Real.sqrt (2 * Real.pi) : ℂ)
  have hsqrtC : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  simpa only [smoothSaddleCentralLaplaceContribution, div_self hsqrtC] using h

end

end Tao2026
