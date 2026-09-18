import Tao2026.SmoothNumberSaddleHTMinorArcScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted integration of the HT minor arc

The finite-shell estimate which only uses `|kernel| <= 1` loses the full
length of a high-frequency interval.  On the physical Perron line the exact
Laplace kernel also has reciprocal-frequency decay.  This module records
that sharper bound as the input for integrating the unconditional HT
minor-arc estimate through its full finite height.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Interval

namespace Tao2026

noncomputable section

/-- Exact norm of the Laplace kernel after physical-frequency rescaling. -/
theorem norm_smoothSaddleLaplaceFourierKernel_physical
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    ‖smoothSaddleLaplaceFourierKernel X y
        (-t * smoothSaddleStandardDeviation X y)‖ =
      smoothSaddlePoint X y /
        Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsigma := smoothSaddlePoint_pos hX hy
  unfold smoothSaddleLaplaceFourierKernel smoothSaddleLaplaceRate
  have hq : -t * smoothSaddleStandardDeviation X y /
      (smoothSaddlePoint X y * smoothSaddleStandardDeviation X y) =
        -t / smoothSaddlePoint X y := by
    field_simp [hsd.ne', hsigma.ne']
  rw [hq, norm_div, norm_one]
  rw [show (1 : ℂ) - ((-t / smoothSaddlePoint X y : ℝ) : ℂ) *
      Complex.I = ((1 : ℝ) : ℂ) +
        ((t / smoothSaddlePoint X y : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.norm_add_mul_I]
  have hsqrt : Real.sqrt
      (1 ^ 2 + (t / smoothSaddlePoint X y) ^ 2) =
      Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) /
        smoothSaddlePoint X y := by
    have hins : 1 ^ 2 + (t / smoothSaddlePoint X y) ^ 2 =
        (smoothSaddlePoint X y ^ 2 + t ^ 2) /
          smoothSaddlePoint X y ^ 2 := by
      field_simp [hsigma.ne']
    rw [hins, Real.sqrt_div, Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
    positivity
  rw [hsqrt]
  field_simp

/-- Away from frequency zero, the physical Laplace kernel retains the
reciprocal Perron weight. -/
theorem norm_smoothSaddleLaplaceFourierKernel_physical_le_div_abs
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {t : ℝ}
    (ht : 0 < |t|) :
    ‖smoothSaddleLaplaceFourierKernel X y
        (-t * smoothSaddleStandardDeviation X y)‖ ≤
      smoothSaddlePoint X y / |t| := by
  rw [norm_smoothSaddleLaplaceFourierKernel_physical hX hy]
  have hsigma := smoothSaddlePoint_pos hX hy
  have habsLe : |t| ≤
      Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (smoothSaddlePoint X y)])
  exact div_le_div_of_nonneg_left hsigma.le ht habsLe

/-- The HT characteristic estimate and the exact Laplace kernel give a
pointwise Perron bound which retains the reciprocal physical frequency. -/
theorem norm_smoothSaddlePerronLineIntegrand_le_hildebrandTenenbaum_div_abs
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper t : ℝ}
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper)
    (htLower : lower ≤ |t|) (htUpper : |t| ≤ upper)
    (ht : 0 < |t|) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) *
        (smoothSaddlePoint X y / |t|) := by
  rw [smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy,
    norm_mul]
  exact mul_le_mul (hminor t htLower htUpper)
    (norm_smoothSaddleLaplaceFourierKernel_physical_le_div_abs hX hy ht)
    (norm_nonneg _) (Real.exp_pos _).le

/-- On a positive interval, the reciprocal Perron weight has logarithmic
mass. -/
theorem integral_one_div_pos
    {lower upper : ℝ} (hlower : 0 < lower) (hlu : lower ≤ upper) :
    (∫ t in lower..upper, 1 / t) = Real.log (upper / lower) := by
  have hderiv : ∀ t ∈ Set.uIcc lower upper,
      HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    simpa [one_div] using Real.hasDerivAt_log
      (ne_of_gt (hlower.trans_le ht.1))
  have hcont : ContinuousOn (fun t : ℝ => 1 / t)
      (Set.uIcc lower upper) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    change t ≠ 0
    exact ne_of_gt (hlower.trans_le ht.1)
  calc
    (∫ t in lower..upper, 1 / t) =
        Real.log upper - Real.log lower := by
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        hderiv (hcont.intervalIntegrable :
          IntervalIntegrable (fun t : ℝ => 1 / t) volume lower upper)
    _ = Real.log (upper / lower) := by
      rw [Real.log_div (by linarith) (ne_of_gt hlower)]

/-- A reciprocal pointwise majorant costs only a logarithm on a positive
finite interval. -/
theorem norm_intervalIntegral_le_mul_log_of_norm_le_div
    {f : ℝ → ℂ} {A lower upper : ℝ}
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hpoint : ∀ t ∈ Set.Icc lower upper, ‖f t‖ ≤ A / t) :
    ‖∫ t in lower..upper, f t‖ ≤
      A * Real.log (upper / lower) := by
  let g : ℝ → ℝ := fun t => A / t
  have hg : ContinuousOn g (Set.uIcc lower upper) := by
    dsimp [g]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    change t ≠ 0
    exact ne_of_gt (hlower.trans_le ht.1)
  have hraw := intervalIntegral.norm_integral_le_of_norm_le
    (f := f) (g := g) (a := lower) (b := upper) hlu (by
      filter_upwards with t ht
      have htIcc : t ∈ Set.Icc lower upper := by
        rw [Set.mem_Ioc] at ht
        exact ⟨ht.1.le, ht.2⟩
      exact hpoint t htIcc)
    (hg.intervalIntegrable : IntervalIntegrable g volume lower upper)
  calc
    ‖∫ t in lower..upper, f t‖ ≤ ∫ t in lower..upper, g t := hraw
    _ = A * (∫ t in lower..upper, 1 / t) := by
      dsimp [g]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = A * Real.log (upper / lower) := by
      rw [integral_one_div_pos hlower hlu]

end

end Tao2026
