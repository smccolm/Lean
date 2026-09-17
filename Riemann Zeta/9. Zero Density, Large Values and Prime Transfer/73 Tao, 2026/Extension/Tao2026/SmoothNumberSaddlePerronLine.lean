import Tao2026.SmoothNumberSaddleCentralIntegral

/-!
# The normalized smooth-number Perron line

This module matches the centered characteristic-function calculation to the
literal normalized vertical-line integrand in the smooth-number Perron
formula.  It verifies the Fourier sign, the `sigma / (sigma + i*t)` kernel,
the standard-deviation change of variables, and the exact central height.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

/-- The vertical-line height corresponding exactly to the normalized central
radius. -/
noncomputable def smoothSaddleCentralPerronHeight (X y : ℕ) : ℝ :=
  smoothSaddleCentralRadius X y / smoothSaddleStandardDeviation X y

/-- The normalized vertical-line Perron integrand before the
standard-deviation change of variables. -/
noncomputable def smoothSaddlePerronLineIntegrand
    (X y : ℕ) (t : ℝ) : ℂ :=
  (smoothFourierDirichletSeries (y + 1) (smoothSaddlePoint X y) (-t) /
      (smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) : ℂ)) *
    Complex.exp (((t * Real.log X : ℝ) : ℂ) * Complex.I) *
      ((smoothSaddlePoint X y : ℂ) /
        ((smoothSaddlePoint X y : ℂ) + (t : ℂ) * Complex.I))

/-- The literal normalized Perron-line integrand equals the centered
characteristic function times the exact Laplace kernel at the rescaled
negative frequency. -/
theorem smoothSaddlePerronLineIntegrand_eq_characteristic_kernel
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    smoothSaddlePerronLineIntegrand X y t =
      smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y) *
        smoothSaddleLaplaceFourierKernel X y
          (-t * smoothSaddleStandardDeviation X y) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsigma := smoothSaddlePoint_pos hX hy
  rw [smoothSaddleNormalizedCharacteristic,
    smoothTiltedCharacteristic_eq_fourierDirichletSeries_div y hsigma]
  unfold smoothSaddlePerronLineIntegrand smoothSaddleLaplaceFourierKernel
    smoothSaddleLaplaceRate
  have harg : -t * smoothSaddleStandardDeviation X y /
      smoothSaddleStandardDeviation X y = -t := by
    field_simp [hsd.ne']
  rw [harg]
  have hphase :
      (-(-t * smoothSaddleStandardDeviation X y * Real.log X /
          smoothSaddleStandardDeviation X y) : ℝ) = t * Real.log X := by
    field_simp [hsd.ne']
  rw [hphase]
  have hkernelArg :
      (-t * smoothSaddleStandardDeviation X y) /
          (smoothSaddlePoint X y * smoothSaddleStandardDeviation X y) =
        -t / smoothSaddlePoint X y := by
    field_simp [hsd.ne', hsigma.ne']
  rw [hkernelArg]
  rw [Complex.ofReal_div, Complex.ofReal_neg]
  field_simp [hsigma.ne']
  ring

/-- The chosen Perron height rescales exactly to the central radius. -/
theorem smoothSaddleCentralPerronHeight_mul_standardDeviation
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCentralPerronHeight X y *
        smoothSaddleStandardDeviation X y =
      smoothSaddleCentralRadius X y := by
  unfold smoothSaddleCentralPerronHeight
  field_simp [(smoothSaddleStandardDeviation_pos hX hy).ne']

/-- The normalized Perron-line integrand is continuous. -/
theorem continuous_smoothSaddlePerronLineIntegrand
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Continuous (smoothSaddlePerronLineIntegrand X y) := by
  have hcomp : Continuous (fun t : ℝ =>
      smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y) *
        smoothSaddleLaplaceFourierKernel X y
          (-t * smoothSaddleStandardDeviation X y)) := by
    exact ((continuous_smoothSaddleNormalizedCharacteristic hX hy).comp
      (by fun_prop)).mul
        ((continuous_smoothSaddleLaplaceFourierKernel X y).comp (by fun_prop))
  exact hcomp.congr fun t =>
    (smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy t).symm

/-- The indicator integral used for dominated convergence is exactly the
ordinary interval integral over the central radius. -/
theorem integral_smoothSaddleCentralFourierIntegrand_eq_intervalIntegral
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (∫ t : ℝ, smoothSaddleCentralFourierIntegrand X y t) =
      ∫ t in (-smoothSaddleCentralRadius X y)..
        (smoothSaddleCentralRadius X y),
        smoothSaddleNormalizedCharacteristic X y t *
          smoothSaddleLaplaceFourierKernel X y t := by
  have hR : 0 ≤ smoothSaddleCentralRadius X y :=
    (smoothSaddleCentralRadius_pos hX hy).le
  unfold smoothSaddleCentralFourierIntegrand
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith :
      -smoothSaddleCentralRadius X y ≤ smoothSaddleCentralRadius X y)]

/-- The standard-deviation substitution converts the literal Perron-line
integral exactly into the normalized central interval integral. -/
theorem standardDeviation_mul_integral_perronLine_eq_centralInterval
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (smoothSaddleStandardDeviation X y : ℂ) *
        (∫ t in (-smoothSaddleCentralPerronHeight X y)..
            (smoothSaddleCentralPerronHeight X y),
          smoothSaddlePerronLineIntegrand X y t) =
      ∫ u in (-smoothSaddleCentralRadius X y)..
          (smoothSaddleCentralRadius X y),
        smoothSaddleNormalizedCharacteristic X y u *
          smoothSaddleLaplaceFourierKernel X y u := by
  let f : ℝ → ℂ := fun u =>
    smoothSaddleNormalizedCharacteristic X y u *
      smoothSaddleLaplaceFourierKernel X y u
  let H := smoothSaddleCentralPerronHeight X y
  let d := smoothSaddleStandardDeviation X y
  have hd : d ≠ 0 := (smoothSaddleStandardDeviation_pos hX hy).ne'
  have hline (t : ℝ) : smoothSaddlePerronLineIntegrand X y t = f (-t * d) :=
    smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy t
  have hneg : (∫ t in (-H)..H, f (-t * d)) =
      ∫ t in (-H)..H, f (t * d) := by
    calc
      (∫ t in (-H)..H, f (-t * d)) =
          ∫ t in (-H)..H, (fun v => f (v * d)) (-t) := by
            apply intervalIntegral.integral_congr
            intro t _
            congr 1
      _ = ∫ t in (-H)..H, f (t * d) := by
            simpa using (intervalIntegral.integral_comp_neg
              (f := fun v => f (v * d)) (a := -H) (b := H))
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (f := f) (a := -H) (b := H) d
  simp_rw [hline]
  rw [hneg]
  change (d : ℂ) * (∫ t in (-H)..H, f (t * d)) = _
  rw [← Complex.real_smul]
  rw [hscale]
  have hHd : H * d = smoothSaddleCentralRadius X y :=
    smoothSaddleCentralPerronHeight_mul_standardDeviation hX hy
  have hnegHd : (-H) * d = -smoothSaddleCentralRadius X y := by
    rw [neg_mul, hHd]
  rw [hHd, hnegHd]

/-- Exact source-facing expression of the normalized central Laplace
contribution as a vertical-line Perron integral. -/
theorem smoothSaddleCentralLaplaceContribution_eq_perronLine
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCentralLaplaceContribution X y =
      ((smoothSaddleStandardDeviation X y : ℂ) /
          (Real.sqrt (2 * Real.pi) : ℂ)) *
        (∫ t in (-smoothSaddleCentralPerronHeight X y)..
            (smoothSaddleCentralPerronHeight X y),
          smoothSaddlePerronLineIntegrand X y t) := by
  rw [smoothSaddleCentralLaplaceContribution,
    integral_smoothSaddleCentralFourierIntegrand_eq_intervalIntegral hX hy,
    ← standardDeviation_mul_integral_perronLine_eq_centralInterval hX hy]
  ring

end

end Tao2026
